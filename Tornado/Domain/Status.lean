import Lean
import Tornado.Domain.Catalog

/-!
Pure one-note withdrawal status decoding and candidate aggregation. This
module does not read or write files. It models selected validation and
transition rules from the captured TypeScript `withdrawal/status-file.ts`;
filesystem locks, exclusive creation, atomic rename, and chain truth remain
separate obligations.
-/

namespace Tornado.Domain
open Lean

inductive WithdrawalState where
  | pending | confirmed | failed | unknown | rejected
  deriving Repr, BEq, DecidableEq, Inhabited

def WithdrawalState.fromString : String → Option WithdrawalState
  | "pending" => some .pending
  | "confirmed" => some .confirmed
  | "failed" => some .failed
  | "unknown" => some .unknown
  | "rejected" => some .rejected
  | _ => none

structure OneNoteStatus where
  chainId : ChainId
  userOpHash : String
  entryPointAddress : String
  sender : String
  paymaster : String
  nonce : String
  poolAddress : String
  recipient : String
  fee : String
  nullifierHash : String
  fromBlock : Option String := none
  status : WithdrawalState
  transactionHash : Option String := none
  message : Option Json := none
  deriving Inhabited

structure WithdrawalStatusRecord where
  current : OneNoteStatus
  rpcUrl : Option Json := none
  bundlerUrl : Option Json := none
  attemptId : Option String := none
  candidates : Option (List OneNoteStatus) := none
  deriving Inhabited

private def invalid : String := "This is not a supported 4337 withdrawal status file."
private def asciiHex (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def hexFixed (value : String) (digits : Nat) : Bool :=
  value.startsWith "0x" && value.length == digits + 2 &&
    (value.toList.drop 2).all asciiHex

private def hexPlus (value : String) : Bool :=
  value.startsWith "0x" && value.length > 2 &&
    (value.toList.drop 2).all asciiHex

private def optionalField (json : Json) (name : String) : Option Json :=
  (json.getObjVal? name).toOption

private def requiredString (json : Json) (name : String) : Except String String := do
  let value ← json.getObjVal? name |>.mapError (fun _ => invalid)
  value.getStr? |>.mapError (fun _ => invalid)

private def optionalString (json : Json) (name : String) : Except String (Option String) := do
  match optionalField json name with
  | none => return none
  | some value => return some (← value.getStr? |>.mapError (fun _ => invalid))

private def decodeOne (json : Json) : Except String OneNoteStatus := do
  let chainValue ← json.getObjVal? "chainId" |>.mapError (fun _ => invalid)
  let chainNumber ← chainValue.getNat? |>.mapError (fun _ => invalid)
  let some chainId := chainFromNat chainNumber | throw invalid
  let userOpHash ← requiredString json "userOpHash"
  let entryPointAddress ← requiredString json "entryPointAddress"
  let sender ← requiredString json "sender"
  let paymaster ← requiredString json "paymaster"
  let nonce ← requiredString json "nonce"
  let poolAddress ← requiredString json "poolAddress"
  let recipient ← requiredString json "recipient"
  let fee ← requiredString json "fee"
  let nullifierHash ← requiredString json "nullifierHash"
  let fromBlock ← optionalString json "fromBlock"
  let transactionHash ← optionalString json "transactionHash"
  let statusString ← requiredString json "status"
  let some status := WithdrawalState.fromString statusString | throw invalid
  if !hexFixed userOpHash 64 || !hexPlus nonce ||
      !(fromBlock.map hexPlus).getD true ||
      !hexFixed entryPointAddress 40 || !hexFixed sender 40 ||
      !hexFixed paymaster 40 || !hexFixed poolAddress 40 ||
      !hexFixed recipient 40 || !hexFixed nullifierHash 64 ||
      !hexPlus fee || !(transactionHash.map (hexFixed · 64)).getD true then
    throw invalid
  return { chainId, userOpHash, entryPointAddress, sender, paymaster, nonce, poolAddress, recipient, fee, nullifierHash, fromBlock, transactionHash, status, message := optionalField json "message" }

private def sameProtectedIdentity (parent candidate : OneNoteStatus) : Bool :=
  parent.chainId == candidate.chainId &&
    parent.poolAddress.toLower == candidate.poolAddress.toLower &&
    parent.recipient.toLower == candidate.recipient.toLower &&
    parent.nullifierHash.toLower == candidate.nullifierHash.toLower &&
    parent.sender.toLower == candidate.sender.toLower &&
    parent.entryPointAddress.toLower == candidate.entryPointAddress.toLower &&
    parent.paymaster.toLower == candidate.paymaster.toLower &&
    parent.nonce == candidate.nonce

private def uniqueHashes (candidates : List OneNoteStatus) : Bool :=
  let hashes := candidates.map (fun candidate => candidate.userOpHash.toLower)
  hashes.eraseDups.length == hashes.length

def decodeWithdrawalStatus (raw : String) : Except String WithdrawalStatusRecord := do
  let json ← Json.parse raw |>.mapError (fun _ => invalid)
  let version ← (← json.getObjVal? "version" |>.mapError (fun _ => invalid)).getNat?
    |>.mapError (fun _ => invalid)
  let kind ← requiredString json "kind"
  if version != 1 || kind != "one-note-4337" then throw invalid
  let current ← decodeOne json
  let attemptId ← optionalString json "attemptId"
  if attemptId.any (fun value => value.length != 36 ||
      !(value.toList.all (fun c => asciiHex c || c == '-'))) then throw invalid
  let candidates ← match optionalField json "candidates" with
    | none => pure none
    | some value => do
        let array ← value.getArr? |>.mapError (fun _ => invalid)
        if array.size < 1 || array.size > 16 then throw invalid
        let decoded ← array.toList.mapM decodeOne
        if !decoded.all (sameProtectedIdentity current) ||
            !(decoded.any (fun candidate => candidate.userOpHash.toLower == current.userOpHash.toLower)) ||
            !uniqueHashes decoded then throw invalid
        pure (some decoded)
  return { current, attemptId, candidates, rpcUrl := optionalField json "rpcUrl", bundlerUrl := optionalField json "bundlerUrl" }

/-- A signed candidate always blocks starting a replacement attempt. A
    legacy rejected record without candidates is the only retry exception. -/
def canPrepareNewAttempt (prior : Option WithdrawalStatusRecord) (retryRejected : Bool) : Bool :=
  match prior with
  | none => true
  | some record => retryRejected && record.current.status == .rejected && record.candidates.isNone

theorem signedCandidateBlocksReplacement (record : WithdrawalStatusRecord)
    (h : record.candidates.isSome = true) (retryRejected : Bool) :
    canPrepareNewAttempt (some record) retryRejected = false := by
  simp [canPrepareNewAttempt, h]

/-- Aggregate candidate statuses using the captured source priority order. -/
def aggregateCandidate (candidates : List OneNoteStatus) : Option OneNoteStatus :=
  candidates.find? (fun candidate => candidate.status == .confirmed) <|>
  candidates.find? (fun candidate => candidate.status == .unknown) <|>
  candidates.find? (fun candidate => candidate.status == .pending) <|>
  candidates.find? (fun candidate => candidate.status == .failed) <|>
  candidates.head?

theorem aggregateConfirmedFirst (candidates : List OneNoteStatus) (candidate : OneNoteStatus)
    (h : candidates.find? (fun row => row.status == .confirmed) = some candidate) :
    aggregateCandidate candidates = some candidate := by
  simp [aggregateCandidate, h]

#print axioms Tornado.Domain.signedCandidateBlocksReplacement
#print axioms Tornado.Domain.aggregateConfirmedFirst

end Tornado.Domain
