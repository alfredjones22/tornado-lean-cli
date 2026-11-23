import Tornado.Domain.NoteIdentity
import Tornado.Crypto.Keccak

/-!
Native Classic deposit calldata and public commitment-only invoice format.
The pool catalog and Pedersen commitment are supplied by Lean modules.
-/

namespace Tornado.Domain

structure DepositCall where
  to : String
  value : Nat
  data : String
  deriving Repr, BEq, Inhabited

structure PublicInvoice where
  raw : String
  pool : Pool
  commitment : String
  call : DepositCall
  deriving Repr, BEq, Inhabited

/-- Four-byte Ethereum selector for `deposit(bytes32)`, calculated natively. -/
def depositSelector : String :=
  Tornado.Crypto.bytesToHex ((Tornado.Crypto.keccak256 "deposit(bytes32)".toUTF8).extract 0 4)

def depositCall (pool : Pool) (commitment : String) : Except String DepositCall := do
  let bytes ← parseHexBytes commitment
  if bytes.size != 32 then throw "Deposit commitment must be bytes32."
  return { to := pool.address, value := if pool.asset.token.isSome then 0 else pool.amount, data := "0x" ++ depositSelector ++ Tornado.Crypto.bytesToHex bytes }

def invoiceForNote (pool : Pool) (commitment : String) : Except String String := do
  let some known := poolFor pool.chainId pool.denomination pool.asset.symbol
    | throw "Cannot create an invoice for an unsupported pool or commitment."
  let bytes ← match parseHexBytes commitment with
    | .ok bytes => pure bytes
    | .error _ => throw "Cannot create an invoice for an unsupported pool or commitment."
  if known.address.toLower != pool.address.toLower || bytes.size != 32 ||
      !commitment.startsWith "0x" || commitment.length != 66 then
    throw "Cannot create an invoice for an unsupported pool or commitment."
  return s!"tornadoInvoice-{pool.asset.symbol.toLower}-{pool.denomination}-{chainNumber pool.chainId}-{commitment.toLower}"

private def validAlphaNum (value : String) : Bool :=
  !value.isEmpty && value.toList.all (fun c =>
    ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z'))

private def validDenomination (value : String) : Bool :=
  !value.isEmpty && value.toList.all (fun c => ('0' ≤ c && c ≤ '9') || c == '.')

def parseInvoice (input : String) (chainId : ChainId) : Except String PublicInvoice := do
  let raw := jsTrim input
  let [tag, symbol, denomination, chainText, commitment] := raw.splitOn "-"
    | throw "This is not a supported Tornado deposit invoice."
  if tag != "tornadoInvoice" || !validAlphaNum symbol ||
      !validDenomination denomination ||
      !(chainText == "1" || chainText == "11155111") ||
      !commitment.startsWith "0x" || commitment.length != 66 then
    throw "This is not a supported Tornado deposit invoice."
  let bytes ← match parseHexBytes commitment with
    | .ok bytes => pure bytes
    | .error _ => throw "This is not a supported Tornado deposit invoice."
  if bytes.size != 32 then throw "This is not a supported Tornado deposit invoice."
  if chainText != toString (chainNumber chainId) then
    throw "This invoice belongs to a different network."
  let some pool := poolFor chainId denomination symbol
    | throw "This invoice uses an unavailable denomination."
  return { raw := raw, pool := pool, commitment := commitment.toLower, call := (← depositCall pool commitment) }

end Tornado.Domain
