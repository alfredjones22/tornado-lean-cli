import Lean
import Tornado.Crypto.Keccak
import Tornado.Domain.NoteIdentity
import Tornado.Protocol.BN254G1

/-!
Canonical records containing only public identifiers for the experimental
Classic prover worker. No raw note, nullifier preimage, secret, mnemonic, or
blinding scalar belongs on this channel. The association of commitment,
nullifier hash, and recipient is privacy sensitive even though the values are
public individually; callers must not log or persist the record. A valid wire
record is only a
shape/binding check; the caller must independently check pool history, the
Merkle root, and the returned Groth16 proof.
-/

namespace Tornado.Protocol.ProverWorkerWire

open Lean Tornado.Crypto Tornado.Domain

private def badRequest : String := "Invalid prover worker request"
private def badResult : String := "Invalid prover worker result"

/-- Public values reviewed before any proving work begins. `commitment` and
`nullifierHash` are expected note identifiers, never their preimages. -/
structure Request where
  chainId : Nat
  pool : Nat
  commitment : Nat
  nullifierHash : Nat
  leafIndex : Nat
  root : Nat
  siblings : Array Nat
  pathIndices : Array Nat
  recipient : Nat
  relayer : Nat
  fee : Nat
  refund : Nat
  deriving BEq, Inhabited

namespace Request

/-- The six ordered public inputs of the pinned Classic Withdraw(20) circuit. -/
def publicSignals (request : Request) : Array Nat :=
  #[request.root, request.nullifierHash, request.recipient,
    request.relayer, request.fee, request.refund]

theorem publicSignals_size (request : Request) :
    request.publicSignals.size = 6 := by
  rfl

theorem publicSignals_root (request : Request) :
    request.publicSignals[0]? = some request.root := by
  rfl

theorem publicSignals_nullifierHash (request : Request) :
    request.publicSignals[1]? = some request.nullifierHash := by
  rfl

/-- Bounds are intentionally narrower than generic JSON integers. The
BabyJubJub Pedersen commitment, public signals, and Merkle siblings lie in Fr. -/
def validate (request : Request) : Except String Unit := do
  let fr := BN254G1.scalarPrime
  if request.chainId == 0 || request.chainId >= 2 ^ 64 ||
      request.pool == 0 || request.pool >= 2 ^ 160 ||
      request.commitment >= fr ||
      request.nullifierHash >= fr || request.root >= fr ||
      request.recipient == 0 || request.recipient >= 2 ^ 160 ||
      request.relayer >= 2 ^ 160 ||
      request.fee >= fr || request.refund >= fr then
    throw badRequest
  if request.leafIndex >= 2 ^ 20 ||
      request.siblings.size != 20 || request.pathIndices.size != 20 ||
      request.siblings.any (· >= fr) then
    throw badRequest
  for i in [0:20] do
    if request.pathIndices[i]! != (request.leafIndex / 2 ^ i) % 2 then
      throw badRequest

/-- Canonical JSON contains exactly this fixed public field allowlist. All
large integers are decimal strings to avoid JSON-number precision loss. -/
def toJson (request : Request) : Json :=
  Json.mkObj [
    ("version", Lean.toJson (1 : Nat)),
    ("chainId", Lean.toJson (toString request.chainId)),
    ("pool", Lean.toJson (toString request.pool)),
    ("commitment", Lean.toJson (toString request.commitment)),
    ("nullifierHash", Lean.toJson (toString request.nullifierHash)),
    ("leafIndex", Lean.toJson (toString request.leafIndex)),
    ("root", Lean.toJson (toString request.root)),
    ("siblings", Lean.toJson (request.siblings.map toString)),
    ("pathIndices", Lean.toJson (request.pathIndices.map toString)),
    ("recipient", Lean.toJson (toString request.recipient)),
    ("relayer", Lean.toJson (toString request.relayer)),
    ("fee", Lean.toJson (toString request.fee)),
    ("refund", Lean.toJson (toString request.refund))]

def encode (request : Request) : String := request.toJson.compress

/-- Public request identifier. The exact bytes are UTF-8 canonical JSON,
without a trailing newline. This does not authenticate an external sender. -/
def hash (request : Request) : ByteArray :=
  keccak256 request.encode.toUTF8

private def number (json : Json) : Except String Nat := do
  let value ← json.getStr?
  if value.isEmpty || value.length > 78 then throw badRequest
  let some number := value.toNat?
    | throw badRequest
  if toString number != value then throw badRequest
  return number

private def field (json : Json) (name : String) : Except String Nat := do
  number (← json.getObjVal? name)

private def vector (json : Json) (name : String) : Except String (Array Nat) := do
  let items ← (← json.getObjVal? name).getArr?
  if items.size != 20 then throw badRequest
  items.mapM number

private def decodeCore (raw : String) : Except String Request := do
  if raw.toUTF8.size > 4096 then throw badRequest
  let json ← Json.parse raw
  let version ← (← json.getObjVal? "version").getNat?
  if version != 1 then throw badRequest
  let request : Request := {
    chainId := ← field json "chainId"
    pool := ← field json "pool"
    commitment := ← field json "commitment"
    nullifierHash := ← field json "nullifierHash"
    leafIndex := ← field json "leafIndex"
    root := ← field json "root"
    siblings := ← vector json "siblings"
    pathIndices := ← vector json "pathIndices"
    recipient := ← field json "recipient"
    relayer := ← field json "relayer"
    fee := ← field json "fee"
    refund := ← field json "refund" }
  validate request
  if request.encode != raw then throw badRequest
  return request

/-- Exact canonical decoder: missing, extra, duplicate, reordered, or
noncanonical fields fail with a fixed error that never reflects input. -/
def decode (raw : String) : Except String Request :=
  match decodeCore raw with
  | .ok request => .ok request
  | .error _ => .error badRequest

end Request

/-- Public identifiers inspected inside the worker. Their association is
privacy sensitive; this record must not be logged or persistently cached.
The opaque status label is derived from the note secret only in the worker. -/
structure Metadata where
  chainId : Nat
  pool : Nat
  commitment : Nat
  nullifierHash : Nat
  amount : Nat
  denomination : String
  asset : String
  statusFileName : String
  deriving BEq, Inhabited

namespace Metadata

private def bad : String := "Invalid prover worker metadata"

def validate (metadata : Metadata) : Except String Unit := do
  let some chain := chainFromNat metadata.chainId | throw bad
  let some selected := allPools.find? (fun pool => pool.chainId == chain &&
    (parseHexBytes pool.address).toOption.map
      (fun bytes => bytes.data.foldl (fun n b => n * 256 + b.toNat) 0) == some metadata.pool)
    | throw bad
  if metadata.commitment >= BN254G1.scalarPrime ||
      metadata.nullifierHash >= BN254G1.scalarPrime ||
      metadata.amount != selected.amount || metadata.denomination != selected.denomination ||
      metadata.asset != selected.asset.symbol then throw bad
  let labelStart := s!"tornado-withdraw-{metadata.chainId}-"
  if !metadata.statusFileName.startsWith labelStart || !metadata.statusFileName.endsWith ".json" ||
      metadata.statusFileName.length != labelStart.length + 64 + 5 then throw bad
  let digest := (metadata.statusFileName.toList.drop labelStart.length).take 64
  unless digest.all (fun char => ('0' ≤ char && char ≤ '9') || ('a' ≤ char && char ≤ 'f')) do
    throw bad

def matchesRequest (metadata : Metadata) (request : Request) : Bool :=
  metadata.chainId == request.chainId && metadata.pool == request.pool &&
  metadata.commitment == request.commitment && metadata.nullifierHash == request.nullifierHash

def toJson (metadata : Metadata) : Json := Json.mkObj [
  ("version", Lean.toJson (1 : Nat)), ("kind", Lean.toJson ("metadata" : String)),
  ("chainId", Lean.toJson (toString metadata.chainId)),
  ("pool", Lean.toJson (toString metadata.pool)),
  ("commitment", Lean.toJson (toString metadata.commitment)),
  ("nullifierHash", Lean.toJson (toString metadata.nullifierHash)),
  ("amount", Lean.toJson (toString metadata.amount)),
  ("denomination", Lean.toJson metadata.denomination),
  ("asset", Lean.toJson metadata.asset),
  ("statusFileName", Lean.toJson metadata.statusFileName)]

def encode (metadata : Metadata) : String := metadata.toJson.compress

private def number (json : Json) (key : String) : Except String Nat := do
  let raw ← (← json.getObjVal? key).getStr?
  if raw.isEmpty || raw.length > 78 then throw bad
  let some number := raw.toNat? | throw bad
  if toString number != raw then throw bad
  return number

private def string (json : Json) (key : String) : Except String String := do
  (← json.getObjVal? key).getStr?

private def decodeCore (raw : String) : Except String Metadata := do
  if raw.utf8ByteSize > 1536 then throw bad
  let json ← Json.parse raw
  if (← (← json.getObjVal? "version").getNat?) != 1 ||
      (← string json "kind") != "metadata" then throw bad
  let metadata : Metadata := {
    chainId := ← number json "chainId"
    pool := ← number json "pool"
    commitment := ← number json "commitment"
    nullifierHash := ← number json "nullifierHash"
    amount := ← number json "amount"
    denomination := ← string json "denomination"
    asset := ← string json "asset"
    statusFileName := ← string json "statusFileName" }
  validate metadata
  if metadata.encode != raw then throw bad
  return metadata

def decode (raw : String) : Except String Metadata :=
  match decodeCore raw with
  | .ok metadata => .ok metadata
  | .error _ => .error bad

end Metadata

/-! Ordered public selection of every note in one protected backup. The
strict worker/parser rejects partial extraction, reused nullifiers and mixed
assets; the parent independently repeats these public identity guards. -/
namespace BatchMetadata

def maxBytes : Nat := 16384

def validate (items : Array Metadata) : Except String Unit := do
  if items.isEmpty || items.size > 12 then throw "Invalid prover batch metadata"
  let first := items[0]!
  let mut commitments : Array Nat := #[]
  let mut nullifiers : Array Nat := #[]
  let mut labels : Array String := #[]
  for item in items do
    item.validate
    if item.chainId != first.chainId || item.asset != first.asset ||
        commitments.contains item.commitment || nullifiers.contains item.nullifierHash ||
        labels.contains item.statusFileName then throw "Invalid prover batch metadata"
    commitments := commitments.push item.commitment
    nullifiers := nullifiers.push item.nullifierHash
    labels := labels.push item.statusFileName

def toJson (items : Array Metadata) : Json := Json.mkObj [
  ("version", Lean.toJson (1 : Nat)), ("kind", Lean.toJson ("batch-metadata" : String)),
  ("items", Json.arr (items.map Metadata.toJson))]

def encode (items : Array Metadata) : String := (toJson items).compress

private def decodeCore (raw : String) : Except String (Array Metadata) := do
  if raw.utf8ByteSize > maxBytes then throw "Invalid prover batch metadata"
  let json ← Json.parse raw
  if (← (← json.getObjVal? "version").getNat?) != 1 ||
      (← (← json.getObjVal? "kind").getStr?) != "batch-metadata" then
    throw "Invalid prover batch metadata"
  let rows ← (← json.getObjVal? "items").getArr?
  if rows.size > 12 then throw "Invalid prover batch metadata"
  let items ← rows.mapM (fun row => Metadata.decode row.compress)
  validate items
  if encode items != raw then throw "Invalid prover batch metadata"
  return items

def decode (raw : String) : Except String (Array Metadata) :=
  (decodeCore raw).mapError (fun _ => "Invalid prover batch metadata")

end BatchMetadata

/-- Only public Groth16 output. Proof bytes use the eight-word Solidity
encoding, and signals use the pinned circuit order. -/
structure Result where
  requestHash : ByteArray
  proof : ByteArray
  signals : Array Nat
  deriving BEq, Inhabited

namespace Result

def validate (result : Result) : Except String Unit := do
  if result.requestHash.size != 32 || result.proof.size != 256 ||
      result.signals.size != 6 ||
      result.signals.any (· >= BN254G1.scalarPrime) then
    throw badResult

/-- Bind the output to the exact reviewed request before verifying the
Groth16 equation. This does not itself verify the proof. -/
def validateFor (request : Request) (result : Result) : Except String Unit := do
  Request.validate request
  validate result
  if result.requestHash = request.hash ∧
      result.signals = request.publicSignals then
    pure ()
  else throw badResult

def toJson (result : Result) : Json :=
  Json.mkObj [
    ("version", Lean.toJson (1 : Nat)),
    ("requestHash", Lean.toJson ("0x" ++ bytesToHex result.requestHash)),
    ("proof", Lean.toJson ("0x" ++ bytesToHex result.proof)),
    ("signals", Lean.toJson (result.signals.map toString))]

def encode (result : Result) : String := result.toJson.compress

private def bytes (json : Json) (name : String) (expected : Nat) :
    Except String ByteArray := do
  let raw ← (← json.getObjVal? name).getStr?
  let value ← parseHexBytes raw
  if value.size != expected || raw != "0x" ++ bytesToHex value then
    throw badResult
  return value

private def signal (json : Json) : Except String Nat := do
  let raw ← json.getStr?
  if raw.isEmpty || raw.length > 78 then throw badResult
  let some number := raw.toNat?
    | throw badResult
  if toString number != raw then throw badResult
  return number

private def decodeCore (raw : String) : Except String Result := do
  if raw.toUTF8.size > 2048 then throw badResult
  let json ← Json.parse raw
  let version ← (← json.getObjVal? "version").getNat?
  if version != 1 then throw badResult
  let values ← (← json.getObjVal? "signals").getArr?
  if values.size != 6 then throw badResult
  let result : Result := {
    requestHash := ← bytes json "requestHash" 32
    proof := ← bytes json "proof" 256
    signals := ← values.mapM signal }
  validate result
  if result.encode != raw then throw badResult
  return result

def decode (raw : String) : Except String Result :=
  match decodeCore raw with
  | .ok result => .ok result
  | .error _ => .error badResult

end Result

end Tornado.Protocol.ProverWorkerWire

#print axioms Tornado.Protocol.ProverWorkerWire.Request.publicSignals_size
#print axioms Tornado.Protocol.ProverWorkerWire.Request.publicSignals_root
#print axioms Tornado.Protocol.ProverWorkerWire.Request.publicSignals_nullifierHash
