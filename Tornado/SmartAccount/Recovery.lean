import Tornado.Domain.Invoice
import Tornado.Protocol.Abi

/-!
Pure UI-compatible smart-account factory and recovery-call construction.
Balances, code bytes, nonce, implementation and account address must be
checked against the selected chain by the caller. This module never
contacts an RPC or signs/sends a transaction.
-/

namespace Tornado.SmartAccount

open Tornado.Domain Tornado.Protocol
open Tornado.Crypto

def simpleAccountFactory : String :=
  "0x13E9ed32155810FDbd067D4522C492D6f68E5944"

def factoryCodeHash : String :=
  "a2e635152a61e180383c7afc045620b7461ef6f43ba27d592262513106b991b7"

def implementationCodeHash : String :=
  "689a90eff03926a12aedad2fc6d4fdbcbdd9ffac86e7d0d70ce6355961305c74"

def implementationSlot : String :=
  "0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc"

private def bytesNatBE (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def addressFromText (text : String) : Except String Nat := do
  let bytes ← parseHexBytes text
  if bytes.size != 20 || !text.startsWith "0x" then
    throw "Invalid pinned Ethereum address."
  return bytesNatBE bytes

/-- Salt shared with the pinned UI and TypeScript CLI. -/
def withdrawalAccountSalt : Nat :=
  bytesNatBE (keccak256 "tornado-ui-new-era:withdrawal-account:v1".toUTF8)

/-- `createAccount(address,uint256)` call to the pinned SimpleAccount v0.8
    factory. Exact bytes must be checked against independent viem vectors. -/
def accountFactoryData (owner : Nat) : Except String ByteArray := do
  if owner == 0 || owner >= Abi.maxAddress then
    throw "Enter a nonzero EOA owner address."
  return Abi.selector "createAccount(address,uint256)" ++
    (← Abi.addressWord owner) ++ (← Abi.uintWord withdrawalAccountSalt)

/-- Accepts an ordinary EOA or exactly the 23-byte EIP-7702 delegation marker.
    Contract-wallet code is outside this CLI's owner signature scheme. -/
def ownerCodeAllowed (code : ByteArray) : Bool :=
  code.isEmpty ||
    (code.size == 23 && code[0]! == 0xef && code[1]! == 0x01 && code[2]! == 0x00)

def pinnedFactoryCode (code : ByteArray) : Bool :=
  !code.isEmpty && bytesToHex (keccak256 code) == factoryCodeHash

def pinnedImplementationCode (code : ByteArray) : Bool :=
  !code.isEmpty && bytesToHex (keccak256 code) == implementationCodeHash

/-- Post-deployment identity check over values supplied by an authenticated
    chain adapter. A malicious RPC could fabricate every one of these values. -/
def deployedAccountIdentityValid (expectedOwner expectedEntryPoint expectedImplementation
    actualOwner actualEntryPoint slotValue : Nat) : Bool :=
  expectedOwner > 0 && expectedOwner < Abi.maxAddress &&
    expectedEntryPoint > 0 && expectedEntryPoint < Abi.maxAddress &&
    expectedImplementation > 0 && expectedImplementation < Abi.maxAddress &&
    actualOwner == expectedOwner && actualEntryPoint == expectedEntryPoint &&
    slotValue == expectedImplementation

structure RecoveryPlan where
  owner : Nat
  account : Nat
  recipient : Nat
  balances : Array Nat
  entryPointDeposit : Nat
  calls : Array Abi.ContractCall
  data : ByteArray
  deriving Inhabited

/-- Independent self-check of the ABI call list against the payload bytes. -/
def encodedCallsMatch (calls : Array Abi.ContractCall) (data : ByteArray) : Bool :=
  match Abi.accountExecuteBatch calls with
  | .error _ => false
  | .ok encoded => encoded == data

theorem encoded_calls_match_sound (calls : Array Abi.ContractCall) (data : ByteArray)
    (h : encodedCallsMatch calls data = true) :
    Abi.accountExecuteBatch calls = .ok data := by
  cases encoded : Abi.accountExecuteBatch calls with
  | error error => simp [encodedCallsMatch, encoded] at h
  | ok value =>
    have equal : value == data := by simpa [encodedCallsMatch, encoded] using h
    have exact : value = data := Abi.byteArray_eq_of_beq equal
    simp [exact]

/-- Runtime check at the pure/effectful boundary. It rejects an empty plan or
    any data bytes that do not encode exactly the stored ordered call list. -/
def validateRecoveryPlan (plan : RecoveryPlan) : Except String RecoveryPlan := do
  if plan.calls.isEmpty then throw "Recovery plan contains no calls."
  if !encodedCallsMatch plan.calls plan.data then
    throw "Recovery calldata does not encode the reviewed calls."
  return plan

/-- Build supported-asset sweeps in catalog order and append the optional
    EntryPoint-deposit withdrawal from the account to itself. No arbitrary
    owner-authorized calls can enter this path. -/
def planRecovery (chain : ChainId) (owner account recipient : Nat)
    (balances : Array Nat) (entryPointDeposit : Nat) : Except String RecoveryPlan := do
  if owner == 0 || owner >= Abi.maxAddress || account == 0 ||
      account >= Abi.maxAddress then
    throw "Enter a nonzero EOA owner and smart-account address."
  if recipient == 0 || recipient >= Abi.maxAddress then
    throw "Enter a nonzero recovery recipient."
  if recipient == account then
    throw "Recovery recipient must differ from the smart account."
  let assets := assetsFor chain
  if balances.size != assets.length then
    throw "Recovery balance list does not match the supported asset catalog."
  let mut calls : Array Abi.ContractCall := #[]
  for (asset, amount) in assets.zip balances.toList do
    if amount >= Abi.maxUint256 then throw "Recovery balance is outside uint256."
    if amount == 0 then continue
    match asset.token with
    | none =>
      calls := calls.push { to := recipient, value := amount, data := ByteArray.empty }
    | some token =>
      let target ← addressFromText token
      let data ← Abi.erc20Transfer recipient amount
      calls := calls.push { to := target, value := 0, data := data }
  if entryPointDeposit >= Abi.maxUint256 then
    throw "EntryPoint deposit is outside uint256."
  if entryPointDeposit > 0 then
    let data ← Abi.accountWithdrawDepositTo recipient entryPointDeposit
    calls := calls.push { to := account, value := 0, data := data }
  if calls.isEmpty then
    throw "There are no supported assets or EntryPoint deposits to recover."
  let data ← Abi.accountExecuteBatch calls
  validateRecoveryPlan { owner, account, recipient, balances, entryPointDeposit, calls, data }

end Tornado.SmartAccount

#print axioms Tornado.SmartAccount.encoded_calls_match_sound
