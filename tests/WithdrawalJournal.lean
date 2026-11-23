import Tornado.Cli.WithdrawalJournal
import Tornado.Cli.RelayerSend
import Tornado.Protocol.Rlp

/-! Real protected-I/O checks reusing the public, unfunded proof generated
once by ProverWorker. All submission effects are local test functions. -/

namespace Tornado.Test.WithdrawalJournal

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.UserOperation08 Tornado.Protocol.SponsoredWithdrawal
open Tornado.Cli.WithdrawalSend

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def rejects (action : IO α) (message : String) : IO Unit := do
  let rejected ← try let _ ← action; pure false catch _ => pure true
  require rejected message

private def number (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def privatePath (directory : String) (tag : Char) : String :=
  directory ++ "/tornado-withdraw-1-" ++ String.ofList (List.replicate 64 tag) ++ ".json"

private def load (path : String) : IO Json := do
  let some raw := String.fromUTF8? (← ProtectedIO.readPrivate path)
    | throw <| IO.userError "Protected journal was not UTF-8."
  checked <| Json.parse raw

private def authorization (key : ByteArray) : IO Bundler.Authorization := do
  let digest ← checked <| Rlp.authorizationHash7702 1 ProverSignerWire.delegate 0
  let sig ← checked <| secp256k1SignDigest key digest
  let publicKey ← checked <| secp256k1PublicKey key
  require (← NativeSigner.verifyPublicDigest publicKey digest sig.bytes65)
    "Native public verification rejected the exact authorization tuple."
  return {
    chainId := 1, delegate := ProverSignerWire.delegate, nonce := 0,
    r := sig.r, s := sig.s, yParity := if sig.recovery == 0 then 0 else 1 }

private def relayerClaim (record : Json) : Json := Id.run do
  let record := record.setObjVal! "kind" (toJson ("relayer" : String))
  -- An original Classic pool is needed only to parse this cross-route
  -- creation attempt. It must never overwrite the existing opaque claim.
  let record := record.setObjVal! "poolAddress" (toJson ("0x12d66f87a04a9e220743712ce6d9bb1b5616b8fc" : String))
  let record := record.setObjVal! "relayerUrl" (toJson ("https://relayer.example.org/" : String))
  return record.setObjVal! "rewardAccount" (toJson ("0x00000000000000000000000000000000000000bb" : String))

def run (directory : String) (publicProof directProof : NoteProof)
    (key : ByteArray) (gas : Gas) : IO Unit := do
  ProtectedIO.checkPrivateDirectory directory
  let owner := number (← checked <| secp256k1EthereumAddress key)
  let publicKey ← checked <| secp256k1PublicKey key
  let clock ← IO.monoMsNow
  let review : Review := {
    mode := .single owner publicProof.request.recipient, notes := #[publicProof],
    owner, gas, preparedAtMs := clock, fromBlock := 1 }
  let op ← checked <| build review
  let hash ← checked <| userOperationHash 1 Bundler.entryPoint op
  let auth ← authorization key
  let signature := (← checked <| secp256k1SignDigest key hash).bytes65
  require (← NativeSigner.verifyPublicDigest publicKey hash signature)
    "Native public verification rejected the reviewed operation digest."
  let signed := { op with signature }
  let expectedPayload ← checked <| Bundler.withAuthorization 1 signed (some auth)
  let path := privatePath directory 'a'
  let journal ← Tornado.Cli.WithdrawalJournal.create #[path]
  let trace ← IO.mkRef (#[] : Array String)
  let sends ← IO.mkRef (0 : Nat)
  let effects : Effects := {
    rpc := fun method params => do
      require (method == .sendUserOperation && params.size == 2 &&
        params[0]! == expectedPayload &&
        params[1]! == toJson (← checked <| Bundler.address Bundler.entryPoint))
        "Only the canonical reviewed operation and authorization may be submitted."
      let saved ← load path
      require ((← checked <| saved.getObjVal? "phase") == toJson ("exposed" : String) &&
        (← checked <| saved.getObjVal? "signedOperation") == expectedPayload)
        "Executable bytes escaped before the exact protected reservation."
      sends.modify (· + 1)
      trace.modify (·.push "send")
      return toJson (Bundler.dataHex hash),
    approve := fun _ => trace.modify (·.push "approve"),
    revalidate := fun _ => trace.modify (·.push "revalidate"),
    signDigest := fun digest => do
      require (digest == hash) "Signer received an unreviewed digest."
      trace.modify (·.push "sign")
      return { owner, signature, authorization := some auth },
    reserve := fun reviewed candidate reserved payload => do
      trace.modify (·.push "reserve")
      Tornado.Cli.WithdrawalJournal.reserve journal reviewed candidate reserved payload
        "https://ethereum.publicnode.com" "https://public.pimlico.io/v2/1/rpc",
    markExposed := fun value => do
      trace.modify (·.push "exposed")
      Tornado.Cli.WithdrawalJournal.mark journal value "exposed",
    markSubmitted := fun value => do
      trace.modify (·.push "submitted")
      Tornado.Cli.WithdrawalJournal.mark journal value "submitted",
    markUnknown := fun value => do
      trace.modify (·.push "unknown")
      Tornado.Cli.WithdrawalJournal.mark journal value "unknown",
    simulate := fun _ => throw <| IO.userError "One-note withdrawals must not use execution simulation.",
    nowMs := pure clock }
  match ← executeWith effects review with
  | .submitted actual => require (actual == hash) "Final one-note hash changed."
  | .unknown _ => throw <| IO.userError "Valid local one-note authorization failed."
  require ((← trace.get) == #["approve", "revalidate", "sign", "reserve", "exposed", "send", "submitted"] &&
    (← sends.get) == 1) "Single authorization or protected exposure ordering changed."
  let saved ← load path
  let storedPayload ← checked <| saved.getObjVal? "signedOperation"
  require (storedPayload == expectedPayload &&
    (← checked <| storedPayload.getObjVal? "eip7702Auth") == (← checked <| Bundler.authorizationJson auth) &&
    (← checked <| saved.getObjVal? "signedPayloadHash") ==
      toJson (Bundler.dataHex (keccak256 expectedPayload.compress.toUTF8)) &&
    (← checked <| saved.getObjVal? "releaseReservations") == toJson false &&
    (← checked <| (← checked <| saved.getObjVal? "candidates").getArr?).size == 1)
    "The status file omitted or changed the exact signed operation/auth payload."
  let _ ← checked <| decodeWithdrawalStatus saved.compress
  let duplicate ← Tornado.Cli.WithdrawalJournal.create #[path]
  rejects (Tornado.Cli.WithdrawalJournal.reserve duplicate review signed hash
    expectedPayload.compress.toUTF8 "https://ethereum.publicnode.com" "https://public.pimlico.io/v2/1/rpc")
    "A second 4337 sender overwrote the permanent note claim."
  let crossRoute ← Tornado.Cli.RelayerSend.protectedJournal path
  rejects (crossRoute.reserve (relayerClaim saved).compress)
    "Switching to the relayer route replaced a permanent note claim."
  require ((← load path) == saved) "A duplicate route claim changed the original signed candidate."
  let mutated := expectedPayload.setObjVal! "callData" (toJson ("0x01" : String))
  require (!(Tornado.Cli.WithdrawalJournal.record review signed hash mutated.compress.toUTF8
    #[path] "https://ethereum.publicnode.com" "https://public.pimlico.io/v2/1/rpc").isOk)
    "Payload mutation survived reservation binding."
  require (!(Tornado.Cli.WithdrawalJournal.record review signed hash
    (expectedPayload.compress ++ "\n").toUTF8 #[path]
    "https://ethereum.publicnode.com" "https://public.pimlico.io/v2/1/rpc").isOk)
    "Noncanonical payload framing survived reservation binding."
  let invalidAuth : Effects := { effects with
    signDigest := fun _ => pure {
      owner, signature, authorization := some { auth with nonce := 1 } } }
  trace.set #[]
  rejects (executeWith invalidAuth review) "A nonzero note-derived authorization nonce was accepted."
  require ((← sends.get) == 1 && !(← trace.get).contains "reserve")
    "An invalid authorization reached reservation or another send."
  -- Force a real partial multi-note claim: the second selected note is
  -- already claimed. The first candidate must survive, with every selected
  -- event and path retained, even though no operation may be exposed.
  let paths := #[privatePath directory 'b', privatePath directory 'c']
  let other := "An earlier permanent claim. Public fixture only.".toUTF8
  ProtectedIO.createPrivate paths[1]! other
  let account : Account := {
    address := publicProof.request.recipient, owner, nonce := 0, deployed := true }
  let calls : Array Abi.ContractCall := #[{ to := 3, value := 0, data := ByteArray.empty }]
  let batchReview : Review := { review with
    mode := .batch account publicProof.request.recipient calls,
    notes := #[publicProof, directProof], gas := { gas with execution := 600000 } }
  let batchOp ← checked <| build batchReview
  let batchHash ← checked <| userOperationHash 1 Bundler.entryPoint batchOp
  let batchSigned := { batchOp with signature :=
    (← checked <| secp256k1SignDigest key batchHash).bytes65 }
  let batchPayload ← checked <| Bundler.withAuthorization 1 batchSigned none
  let partialJournal ← Tornado.Cli.WithdrawalJournal.create paths
  rejects (Tornado.Cli.WithdrawalJournal.reserve partialJournal batchReview batchSigned batchHash
    batchPayload.compress.toUTF8 "https://ethereum.publicnode.com" "https://public.pimlico.io/v2/1/rpc")
    "A partial batch claim unexpectedly succeeded."
  let first ← load paths[0]!
  let parsed ← checked <| Tornado.Cli.BatchWithdrawalStatus.parseRecord first
  require (parsed.statusFiles == paths && parsed.events.length == 2 &&
    (← ProtectedIO.readPrivate paths[1]!) == other &&
    (← checked <| first.getObjVal? "signedOperation") == batchPayload)
    "A partial batch failure lost its exact payload, selected events or prior claim."
  require (← (System.FilePath.mk paths[0]!).pathExists)
    "The partial batch claim was automatically released."
  rejects (Tornado.Cli.WithdrawalJournal.mark partialJournal batchHash "exposed")
    "An incomplete batch reservation authorized exposure."
  -- A status process racing a later phase update must win its own CAS;
  -- this stale writer cannot erase that state or release the candidate.
  let old ← ProtectedIO.readPrivate path
  let newer := (saved.setObjVal! "message" (toJson ("Concurrent status check." : String))).compress.toUTF8
  ProtectedIO.replacePrivate path old newer
  rejects (Tornado.Cli.WithdrawalJournal.mark journal hash "unknown")
    "A stale sender overwrote a concurrent protected status update."
  require ((← ProtectedIO.readPrivate path) == newer)
    "CAS conflict discarded the concurrent status evidence."

end Tornado.Test.WithdrawalJournal
