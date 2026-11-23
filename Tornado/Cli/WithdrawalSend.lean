import Tornado.Protocol.SponsoredWithdrawal

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

structure Signed where
  owner : Nat
  signature : ByteArray
  authorization : Option Bundler.Authorization := none

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

private def validateSignature (signature : ByteArray) : Except String Unit := do
  if signature.size != 65 then throw "Invalid owner signature length."
  let word (start : Nat) := (signature.extract start (start + 32)).data.foldl
    (fun n b => n * 256 + b.toNat) 0
  let r := word 0
  let s := word 32
  if r == 0 || r >= secp256k1Order || s == 0 || s > secp256k1Order / 2 ||
      (signature[64]! != 27 && signature[64]! != 28) then
    throw "Owner signature is not canonical Ethereum ECDSA."

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

/-- All potentially executable bytes are reserved before any signed simulation
or send. A failed simulation remains unknown because its RPC may have relayed
the signed operation. Revalidation must establish live root, spent, account,
nonce and chain policy; no HTTP reply authenticates itself. -/
def executeWith (effects : Effects) (review : Review) : IO Bundler.Outcome := do
  let op ← checked (build review)
  let chainId := review.notes[0]!.request.chainId
  let hash ← checked (userOperationHash chainId Bundler.entryPoint op)
  effects.approve (← checked (reviewText review op hash))
  let now ← effects.nowMs
  if now < review.preparedAtMs || now - review.preparedAtMs > 300000 then
    throw <| IO.userError "Withdrawal quote expired; no operation was signed."
  effects.revalidate review
  let beforeSign ← effects.nowMs
  if beforeSign < review.preparedAtMs || beforeSign - review.preparedAtMs > 300000 then
    throw <| IO.userError "Withdrawal review expired before signing."
  let result ← effects.signDigest hash
  if result.owner != review.owner then
    throw <| IO.userError "Signing key differs from the reviewed withdrawal owner."
  let _ ← checked (validateSignature result.signature)
  match review.mode with
  | .single .. =>
    let some auth := result.authorization
      | throw <| IO.userError "One-note withdrawal is missing its final authorization."
    if auth.nonce != 0 then
      throw <| IO.userError "Note-derived sender authorization nonce must be zero."
    let _ ← checked (Bundler.withAuthorization chainId op (some auth))
  | .batch .. =>
    if result.authorization.isSome then
      throw <| IO.userError "A recoverable account cannot use EIP-7702 authorization."
  let signed := { op with signature := result.signature }
  let finalHash ← checked (userOperationHash chainId Bundler.entryPoint signed)
  if finalHash != hash then
    throw <| IO.userError "Final signed withdrawal differs from review."
  let afterSign ← effects.nowMs
  if afterSign < review.preparedAtMs || afterSign - review.preparedAtMs > 300000 then
    throw <| IO.userError "Withdrawal review expired during signing; no payload was exposed."
  let simulate := match review.mode with | .single .. => false | .batch .. => true
  let bundlerEffects : Bundler.Effects := {
    rpc := fun method params => do
      if simulate then
        unless (← effects.simulate signed) do
          throw <| IO.userError "Signed simulation rejected the withdrawal."
      effects.rpc method params
    reserve := fun reserved bytes => do
      if reserved != hash then
        throw <| IO.userError "Reservation hash differs from reviewed withdrawal."
      effects.reserve review signed hash bytes
    markExposed := effects.markExposed
    markSubmitted := effects.markSubmitted
    markUnknown := effects.markUnknown }
  Bundler.submitWith bundlerEffects chainId signed review.bounds result.authorization

end Tornado.Cli.WithdrawalSend
