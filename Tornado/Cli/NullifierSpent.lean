import Lean
import Tornado.Domain.Catalog
import Tornado.Crypto.Keccak
import Tornado.Protocol.Abi
import Tornado.Runtime.HttpTransport
import Tornado.Runtime.JsonRpc

/-!
Read-only, exact-block `isSpent(bytes32)` check for a catalogued Tornado pool.
The nullifier hash is disclosed to the selected RPC. An RPC response is an
observation, not an authenticated Ethereum state proof or finality guarantee.
-/

namespace Tornado.Cli.NullifierSpent

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime

structure Selection where
  chainId : ChainId
  pool : Pool
  nullifierHash : ByteArray
  blockNumber : Nat
  deriving Inhabited

/-- Bind the selected pool to the pinned catalog and bound the ABI input. -/
def validSelection (selection : Selection) : Bool :=
  selection.pool.chainId == selection.chainId &&
  (poolsFor selection.chainId).contains selection.pool &&
  selection.nullifierHash.size == 32 &&
  selection.blockNumber < Abi.maxUint256

def validateSelection (selection : Selection) : Except String Unit :=
  if validSelection selection then .ok ()
  else .error "Selected chain, pool, nullifier hash, or block is invalid."

theorem accepted_selection_binds_pool (selection : Selection)
    (h : validateSelection selection = .ok ()) :
    selection.pool.chainId == selection.chainId ∧
    (poolsFor selection.chainId).contains selection.pool = true := by
  unfold validateSelection at h
  by_cases hv : validSelection selection = true
  · simp [hv] at h
    simp only [validSelection, Bool.and_eq_true] at hv
    exact ⟨hv.1.1.1, hv.1.1.2⟩
  · simp [hv] at h

private def quantityHex (value : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 value)

private def callData (nullifierHash : ByteArray) : ByteArray :=
  Abi.selector "isSpent(bytes32)" ++ nullifierHash

/-- The only call target is the selected catalogued pool, at a numeric block. -/
def callParams (selection : Selection) : Except String (Array Json) := do
  let _ ← validateSelection selection
  return #[Json.mkObj [
    ("to", toJson selection.pool.address),
    ("data", toJson ("0x" ++ bytesToHex (callData selection.nullifierHash)))],
    toJson (quantityHex selection.blockNumber)]

def falseWord : String := "0x" ++ String.ofList (List.replicate 64 '0')
def trueWord : String := "0x" ++ String.ofList (List.replicate 63 '0') ++ "1"

/-- Exact canonical ABI bool: one 32-byte word, containing only 0 or 1. -/
def decodeBoolRaw (raw : String) : Except String Bool :=
  if raw = trueWord then .ok true
  else if raw = falseWord then .ok false
  else .error "Pool isSpent returned a malformed or noncanonical bool."

def decodeBool (result : Json) : Except String Bool := do
  decodeBoolRaw (← result.getStr?)

theorem accepted_spent_is_canonical (raw : String)
    (h : decodeBoolRaw raw = .ok true) : raw = trueWord := by
  by_cases ht : raw = trueWord
  · exact ht
  · simp [decodeBoolRaw, ht] at h
    by_cases hf : raw = falseWord
    · simp [hf] at h
    · simp [hf] at h

private def fromExcept (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

/-- Injected read-only RPC boundary. No ambiguity maps to `false` or `true`. -/
def checkWith (selection : Selection)
    (fetch : JsonRpc.Method → Array Json → IO Json) : IO Bool := do
  let _ ← fromExcept (validateSelection selection)
  let chain ← fromExcept <| JsonRpc.parseHexQuantity
    (← fromExcept (← fetch .chainId #[]).getStr?)
  if chain != chainNumber selection.chainId then
    throw <| IO.userError "The RPC endpoint is on a different network."
  let head ← fromExcept <| JsonRpc.parseHexQuantity
    (← fromExcept (← fetch .blockNumber #[]).getStr?)
  if head < selection.blockNumber then
    throw <| IO.userError "The RPC head precedes the selected block."
  let result ← fetch .call (← fromExcept (callParams selection))
  fromExcept (decodeBool result)

/-- Live adapter using the native HTTPS JSON-RPC transport. -/
def checkAt (selection : Selection) (rpc : String) : IO Bool := do
  let requestId ← IO.mkRef (1 : Nat)
  checkWith selection fun method params => do
    let id ← requestId.get
    requestId.set (id + 1)
    HttpTransport.call rpc id method params

end Tornado.Cli.NullifierSpent

#print axioms Tornado.Cli.NullifierSpent.accepted_selection_binds_pool
#print axioms Tornado.Cli.NullifierSpent.accepted_spent_is_canonical
