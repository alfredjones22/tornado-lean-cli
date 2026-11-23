import Tornado.Runtime.ProverWorkerClient
import Tornado.Runtime.Bundler
import Tornado.Protocol.SelectedPoolBootstrap
import Tornado.SmartAccount.Recovery
import Tornado.Protocol.DirectWithdrawalIntent

/-! Public-only preparation for the pinned Tornado paymaster. Every proof is
checked against its reviewed inputs before it can enter a UserOperation. This
module does not read a note, sign, journal, simulate or broadcast. -/

namespace Tornado.Protocol.SponsoredWithdrawal

open Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.ProverWorkerWire Tornado.Protocol.UserOperation08

def paymaster (chainId : Nat) : Except String Nat :=
  if chainId == 1 then .ok 0xb0ffcdc890e969579d348f519a9c3920c2dd04a5
  else if chainId == 11155111 then .ok 0x835ce2da8ad0d1f5d5a8462a58594006514c39b0
  else .error "Unsupported Tornado paymaster network."

structure Gas where
  verification : Nat := 50000
  execution : Nat := 0
  preVerification : Nat := 100000
  paymasterVerification : Nat := 450000
  postOp : Nat := 50000
  maxFee : Nat
  priority : Nat
  deriving Inhabited

def ethFee (gas : Gas) : Nat :=
  ((gas.verification + gas.execution + gas.preVerification +
    gas.paymasterVerification + gas.postOp) * gas.maxFee) * 120 / 100

structure NoteProof where
  request : Request
  result : Result
  deriving Inhabited

private def selectedPool (note : NoteProof) : Except String Pool := do
  let row ← SelectedPoolBootstrap.byIdentity note.request.chainId note.request.pool
  let some chain := chainFromNat note.request.chainId
    | throw "Unsupported note network."
  let some pool := allPools.find? (fun pool => pool.chainId == chain &&
      (parseHexBytes pool.address).toOption.map
        (fun bytes => bytes.data.foldl (fun n b => n * 256 + b.toNat) 0) == some row.address)
    | throw "Selected withdrawal pool is outside the pinned catalog."
  return pool

private def baseOperation (sender nonce : Nat) (gas : Gas) : UserOperation := {
  sender, nonce,
  verificationGasLimit := gas.verification, callGasLimit := gas.execution,
  preVerificationGas := gas.preVerification,
  paymasterVerificationGasLimit := gas.paymasterVerification,
  paymasterPostOpGasLimit := gas.postOp,
  maxFeePerGas := gas.maxFee, maxPriorityFeePerGas := gas.priority }

private def sponsorData (note : NoteProof) : Except String ByteArray := do
  Abi.sponsorParameters {
    instanceAddress := note.request.pool, proof := note.result.proof,
    root := ← Abi.uintWord note.request.root,
    nullifierHash := ← Abi.uintWord note.request.nullifierHash,
    recipient := note.request.recipient, fee := note.request.fee }

/-- Direct one-note sponsorship uses no execution or deployment. Funds go to
the reviewed recipient in paymaster validation. Owner recovery is separate. -/
def single (note : NoteProof) (sender recipient : Nat) (gas : Gas)
    (bounds : Bundler.Bounds := {}) : Except String UserOperation := do
  let pool ← selectedPool note
  let sponsor ← paymaster note.request.chainId
  if note.request.recipient != recipient || recipient == 0 ||
      note.request.relayer != sponsor || note.request.refund != 0 ||
      note.request.fee == 0 || note.request.fee >= pool.amount ||
      gas.execution != 0 || gas.verification > 250000 then
    throw "One-note sponsor differs from reviewed payout or gas policy."
  let _ ← ProverWorkerClient.acceptResponse note.request note.result
  let op := { baseOperation sender 0 gas with
    paymaster := some sponsor, paymasterData := ← sponsorData note }
  Bundler.validate op bounds
  let _ ← DirectWithdrawalIntent.accept {
    sender, sponsor, pool := note.request.pool, recipient,
    proof := note.result.proof, root := ← Abi.uintWord note.request.root,
    nullifierHash := ← Abi.uintWord note.request.nullifierHash, fee := note.request.fee,
    verificationGas := gas.verification, preVerificationGas := gas.preVerification,
    paymasterVerificationGas := gas.paymasterVerification, postOpGas := gas.postOp,
    maxFee := gas.maxFee, priorityFee := gas.priority } op
  return op

structure Account where
  address : Nat
  owner : Nat
  nonce : Nat
  deployed : Bool
  deriving Inhabited

/-- Sponsor note pays the gas fee; every remaining note is withdrawn to the
recoverable account with zero relayer/fee. Tail calls retain exact order.
Without tail calls, the total net amount is forwarded to the receiver. -/
def batch (notes : Array NoteProof) (account : Account) (receiver : Nat)
    (tail : Array Abi.ContractCall) (gas : Gas)
    (bounds : Bundler.Bounds := {}) : Except String UserOperation := do
  if notes.isEmpty || notes.size > 12 || (notes.size == 1 && tail.isEmpty) ||
      gas.execution == 0 ||
      account.address == 0 || account.owner == 0 || receiver == 0 ||
      account.address >= 2 ^ 160 || account.owner >= 2 ^ 160 || receiver >= 2 ^ 160 then
    throw "Invalid batch withdrawal scope."
  let tail ← Abi.validateCalls tail (some account.address)
  if !tail.isEmpty && receiver != account.address then
    throw "Contract calls require proceeds to remain in the recoverable account."
  let first := notes[0]!
  let pool ← selectedPool first
  let sponsor ← paymaster first.request.chainId
  if first.request.recipient != account.address || first.request.relayer != sponsor ||
      first.request.fee == 0 || first.request.fee >= pool.amount || first.request.refund != 0 then
    throw "Batch sponsor differs from the recoverable account or fee policy."
  let mut total := 0
  let mut nullifiers : Array Nat := #[]
  let mut commitments : Array Nat := #[]
  let mut calls : Array Abi.ContractCall := #[]
  for i in [0:notes.size] do
    let note := notes[i]!
    let selected ← selectedPool note
    if selected.chainId != pool.chainId || selected.asset != pool.asset ||
        note.request.recipient != account.address || note.request.refund != 0 ||
        nullifiers.contains note.request.nullifierHash ||
        commitments.contains note.request.commitment then
      throw "Batch note selection or payout differs from review."
    if i > 0 && (note.request.relayer != 0 || note.request.fee != 0) then
      throw "Only the sponsoring note may pay a relayer fee."
    let accepted ← ProverWorkerClient.acceptResponse note.request note.result
    if i > 0 then
      calls := calls.push { to := note.request.pool, value := 0, data := accepted.calldata }
    total := total + selected.amount
    nullifiers := nullifiers.push note.request.nullifierHash
    commitments := commitments.push note.request.commitment
  calls := calls ++ tail
  if tail.isEmpty && receiver != account.address then
    let net := total - first.request.fee
    match pool.asset.token with
    | none => calls := calls.push { to := receiver, value := net, data := ByteArray.empty }
    | some token =>
      let bytes ← parseHexBytes token
      let target := bytes.data.foldl (fun n b => n * 256 + b.toNat) 0
      calls := calls.push { to := target, value := 0, data := ← Abi.erc20Transfer receiver net }
  let factoryData ← if account.deployed then pure ByteArray.empty
    else Tornado.SmartAccount.accountFactoryData account.owner
  let op := { baseOperation account.address account.nonce gas with
    paymaster := some sponsor, paymasterData := ← sponsorData first,
    callData := ← Abi.accountExecuteBatchComposed calls,
    factory := if account.deployed then none
      else some (.address 0x13e9ed32155810fdbd067d4522c492d6f68e5944),
    factoryData }
  Bundler.validate op bounds
  return op

end Tornado.Protocol.SponsoredWithdrawal
