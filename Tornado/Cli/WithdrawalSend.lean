import Tornado.Protocol.SponsoredWithdrawal
import Tornado.Runtime.WithdrawalDriver

/-! Effect-injected experimental sponsored withdrawal runner. It connects
proof/payout validation, final approval, one signature, durable reservation,
optional signed simulation and one bundler send. Secret handling and chain
truth remain explicit assumptions, rather than consequences of this runner. -/

namespace Tornado.Cli.WithdrawalSend

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.UserOperation08 Tornado.Protocol.SponsoredWithdrawal

inductive Mode where
  | single (sender recipient : Nat)
  | batch (account : Account) (receiver : Nat) (calls : Array Abi.ContractCall)
  deriving Inhabited

structure Review where
  mode : Mode
  notes : Array NoteProof
  owner : Nat
  gas : Gas
  preparedAtMs : Nat
  fromBlock : Nat
  bounds : Bundler.Bounds := {}
  deriving Inhabited

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

def build (review : Review) : Except String UserOperation := do
  if review.notes.isEmpty || review.notes.size > 12 || review.owner == 0 ||
      review.owner >= 2 ^ 160 || review.fromBlock >= 2 ^ 64 then
    throw "Invalid reviewed withdrawal candidate."
  match review.mode with
  | .single sender recipient =>
    if review.notes.size != 1 || review.owner != sender then
      throw "One-note owner or selection differs from review."
    SponsoredWithdrawal.single review.notes[0]! sender recipient review.gas review.bounds
  | .batch account receiver calls =>
    if review.owner != account.owner then
      throw "Batch owner differs from the recoverable account."
    SponsoredWithdrawal.batch review.notes account receiver calls review.gas review.bounds

abbrev Signed := WithdrawalDriver.Signed

structure Effects where
  rpc : JsonRpc.Method → Array Json → IO Json
  approve : String → IO Unit
  revalidate : Review → IO Unit
  signDigest : ByteArray → IO Signed
  reserve : Review → UserOperation → ByteArray → ByteArray → IO Unit
  markExposed : ByteArray → IO Unit
  markSubmitted : ByteArray → IO Unit
  markUnknown : ByteArray → IO Unit
  simulate : UserOperation → IO Bool
  nowMs : IO Nat

def reviewText (review : Review) (op : UserOperation) (hash : ByteArray) :
    Except String String := do
  let mut lines := [s!"Chain: {review.notes[0]!.request.chainId}",
    s!"Owner: {← Bundler.address review.owner}",
    s!"Withdrawal sender: {← Bundler.address op.sender}"]
  let mut total := 0
  for note in review.notes do
    let row ← SelectedPoolBootstrap.byIdentity note.request.chainId note.request.pool
    total := total + row.amount
    lines := lines ++ [s!"Selected pool: {← Bundler.address note.request.pool}; note value: {row.amount} base units"]
  let fee := review.notes[0]!.request.fee
  lines := lines ++ [s!"Fee: {fee} base units; net withdrawal: {total - fee} base units",
    s!"Maximum network gas cost: {Bundler.maximumGasCost op} wei"]
  match review.mode with
  | .single _ recipient =>
    lines := lines ++ [s!"Recipient: {← Bundler.address recipient}", "No post-withdrawal calls.",
      "EIP-7702 authorization: pinned Simple7702 delegate 0xe6cae83bde06e4c305530e199d7217f42808555b; selected chain; nonce zero."]
  | .batch account receiver calls =>
    lines := lines ++ [s!"Recoverable account: {← Bundler.address account.address}",
      s!"Receiver: {← Bundler.address receiver}",
      s!"Ordered contract calls hash: {Bundler.dataHex (← Abi.callsHash calls)}"]
    for i in [0:calls.size] do
      let call := calls[i]!
      lines := lines ++ [s!"Call {i + 1}: {← Bundler.address call.to}; {call.value} wei; data={Bundler.dataHex call.data}"]
  lines := lines ++ [s!"Operation hash: {Bundler.dataHex hash}"]
  return String.intercalate "\n" lines

/-- Carries the actual builder equality into the runtime command machine. -/
structure PreparedReview (review : Review) where
  private mk ::
  operation : UserOperation
  built : build review = .ok operation
  driver : WithdrawalDriver.ReviewedOperation operation

def prepareReview (review : Review) : Except String (PreparedReview review) := do
  match built : build review with
  | .error message => throw message
  | .ok operation =>
    let chainId := review.notes[0]!.request.chainId
    let hash ← userOperationHash chainId Bundler.entryPoint operation
    let text ← reviewText review operation hash
    let selected := review.notes.map fun note =>
      (⟨note.request.pool, note.request.nullifierHash⟩ : WithdrawalDriver.NoteId)
    let flow := match review.mode with
      | .single .. => WithdrawalDriver.Flow.direct
      | .batch .. => WithdrawalDriver.Flow.batch
    let driver ← WithdrawalDriver.prepareReviewed chainId review.owner operation selected flow
      review.preparedAtMs text review.bounds
    return ⟨operation, built, driver⟩

/-- Approval, revalidation, signing, reservation and every exposure callback
are dispatched by the same finite command machine checked by the driver proofs.
The protected reserve callback acknowledges all selected note paths together;
the filesystem, signer and chain-response contracts remain external assumptions. -/
def executeWith (effects : Effects) (review : Review) : IO Bundler.Outcome := do
  let prepared ← checked (prepareReview review)
  let driver := prepared.driver
  WithdrawalDriver.runWith (reviewed := driver) {
    approve := effects.approve
    nowMs := effects.nowMs
    revalidate := effects.revalidate review
    signDigest := effects.signDigest
    reserve := fun payload => effects.reserve review payload.operation driver.hash payload.bytes
    markExposed := effects.markExposed
    simulate := effects.simulate
    rpc := effects.rpc
    markSubmitted := effects.markSubmitted
    markUnknown := effects.markUnknown }

end Tornado.Cli.WithdrawalSend
