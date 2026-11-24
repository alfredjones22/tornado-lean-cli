import Tornado.Protocol.WitnessLocalConstraints
import Tornado.Protocol.PedersenSchedule
import Tornado.Compression.Gzip

set_option autoImplicit false
namespace Tornado.Protocol.WitnessSymbolic
open Lean
open Tornado.Protocol.WitnessVM
open LeanCrypto.Groth16.ConstraintCertificate

private def decimal (json : Json) : Except String Nat := do
  let text ← json.getStr?
  if text.isEmpty || text.length > 78 || !text.toList.all Char.isDigit then
    throw "Public witness certificate has an invalid field coefficient."
  let some value := text.toNat? | throw "Public witness certificate coefficient is malformed."
  return value

private def natural (json : Json) (field : String) : Except String Nat :=
  json.getObjVal? field >>= Json.getNat?

private def nodeFromJson (json : Json) : Except String Node := do
  let kind ← (← json.getObjVal? "kind").getStr?
  match kind with
  | "constant" => return .constant (← decimal (← json.getObjVal? "value"))
  | "input" => return .input (← natural json "index")
  | "bit" => return .bit (← natural json "input") (← natural json "bit")
  | "mux" => return .select (← natural json "selector") (← natural json "left") (← natural json "right")
  | _ =>
    let args ← (← json.getObjVal? "args").getArr?
    if kind == "inv" then
      if args.size != 1 then throw "Public witness inverse has the wrong arity."
      return .inverse (← args[0]!.getNat?)
    if args.size != 2 then throw "Public witness binary operation has the wrong arity."
    let left ← args[0]!.getNat?
    let right ← args[1]!.getNat?
    match kind with
    | "add" => return .add left right
    | "sub" => return .sub left right
    | "mul" => return .mul left right
    | _ => throw "Public witness certificate has an unknown expression."

private def stepFromJson (json : Json) : Except String LinearStep := do
  let kind ← (← json.getObjVal? "kind").getStr?
  match kind with
  | "scale" => return .scale (← natural json "source") (← decimal (← json.getObjVal? "scalar"))
  | "add" => return .add (← natural json "left") (← natural json "right")
  | _ => throw "Public witness certificate has an unknown derivation step."

private def ruleFromJson (json : Json) : Except String Rule := do
  return ⟨(← natural json "pivot"),(← natural json "row")⟩

private def indicesFromJson (json : Json) (field : String) : Except String (List Nat) := do
  let values ← (← json.getObjVal? field).getArr?
  if values.size > maximumSubstitutionSteps then
    throw "Public witness substitution program is too large."
  return (← values.mapM Json.getNat?).toList

private def substitutionFromJson (json : Json) : Except String Substitution := do
  return ⟨(← indicesFromJson json "a"),(← indicesFromJson json "b"),
    (← indicesFromJson json "c")⟩

private def matchFromJson (json : Json) : Except String Match := do
  return ⟨(← natural json "source"),(← decimal (← json.getObjVal? "scale"))⟩

structure PublicCertificateData where
  nodes : Array Node
  elimination : Certificate

/-- The five instantiated circuit segments use the exact deterministic native
generators, including their unreduced subgroup-order checks. -/
def pedersenSeedCoordinates (first : LeanCrypto.Pedersen.CertifiedGenerator 0)
    (second : LeanCrypto.Pedersen.CertifiedGenerator 1)
    (third : LeanCrypto.Pedersen.CertifiedGenerator 2) : Array (Nat × Nat) :=
  #[(28551, first.x), (28552, first.y),
    (30747, second.x), (30748, second.y),
    (32867, third.x), (32868, third.y),
    (33871, first.x), (33872, first.y),
    (35967, second.x), (35968, second.y)]

structure CertifiedPedersenBases (graph : SelectedGraph) where
  private mk ::
  first : LeanCrypto.Pedersen.CertifiedGenerator 0
  second : LeanCrypto.Pedersen.CertifiedGenerator 1
  third : LeanCrypto.Pedersen.CertifiedGenerator 2
  binding : graph.bases.map (fun base => (base.index, base.value)) =
    pedersenSeedCoordinates first second third

def certifyPedersenBases (graph : SelectedGraph) : Except String (CertifiedPedersenBases graph) := do
  let first ← LeanCrypto.Pedersen.certifyGenerator 0
  let second ← LeanCrypto.Pedersen.certifyGenerator 1
  let third ← LeanCrypto.Pedersen.certifyGenerator 2
  if binding : graph.bases.map (fun base => (base.index, base.value)) =
      pedersenSeedCoordinates first second third then
    return ⟨first, second, third, binding⟩
  else throw "Public circuit Pedersen bases differ from the native generators."

/-- Bounded public data only. Every arithmetic derivation is checked after
parsing; the extractor and JSON bytes supply no trusted mathematical facts. -/
def decodePublicCertificate (json : Json) : Except String PublicCertificateData := do
  let version ← natural json "schemaVersion"
  if version != 1 then throw "Public witness certificate has an unsupported version."
  let nodes ← (← json.getObjVal? "nodes").getArr?
  let certificate ← json.getObjVal? "certificate"
  let steps ← (← certificate.getObjVal? "steps").getArr?
  let rules ← (← certificate.getObjVal? "rules").getArr?
  let substitutions ← (← certificate.getObjVal? "substitutions").getArr?
  let matchRows ← (← certificate.getObjVal? "matches").getArr?
  if nodes.size > 100000 || steps.size > maximumSteps || rules.size > maximumRows ||
      substitutions.size > maximumRows || matchRows.size > maximumRows then
    throw "Public witness certificate exceeds its structural bounds."
  return ⟨(← nodes.mapM nodeFromJson),⟨(← steps.mapM stepFromJson),
    (← rules.mapM ruleFromJson),(← substitutions.mapM substitutionFromJson),
    (← matchRows.mapM matchFromJson)⟩⟩

/-- Only an erased public-data derivation survives admission. No DAG, symbolic
lookup table, expanded rows, transcript, or secret witness is stored here. -/
structure CertifiedPublic (graph : SelectedGraph) (circuit : Groth16R1CS.Circuit) : Type where
  private mk ::
  pedersenBases : CertifiedPedersenBases graph
  private accepted : ∃ (data : PublicCertificateData) (compiled : CompiledGraph)
      (system : LocalSystem),
    graph.nVars = circuit.nVars ∧
    compileGraph (Resolver.ofNodes data.nodes) graph = .ok compiled ∧
    generateLocalSystem data.nodes compiled graph = .ok system ∧
    checkCertificate graph.nVars graph.nSignals system.linears system.nonlinear
      (circuit.constraints.map ofConstraint) data.elimination = .ok () ∧
    Nonempty (PedersenSchedule.CertifiedSchedule (Resolver.ofNodes data.nodes) graph compiled)

def preparePublicCertificate (graph : SelectedGraph) (circuit : Groth16R1CS.Circuit)
    (data : PublicCertificateData) : Except String (CertifiedPublic graph circuit) := do
  let pedersenBases ← certifyPedersenBases graph
  if dimensions : graph.nVars = circuit.nVars then
    match compiled : compileGraph (Resolver.ofNodes data.nodes) graph with
    | .error message => .error message
    | .ok graphResult =>
      let schedule ← PedersenSchedule.certifySchedule (Resolver.ofNodes data.nodes) graph graphResult
      match generated : generateLocalSystem data.nodes graphResult graph with
      | .error message => .error message
      | .ok system =>
        match _checked : prepareCertificate graph.nVars graph.nSignals system.linears system.nonlinear
            (circuit.constraints.map ofConstraint) data.elimination with
        | .error message => .error message
        | .ok proof => .ok ⟨pedersenBases, ⟨data,graphResult,system,dimensions,compiled,generated,
            checkedCertificate_accepted _ _ _ _ _ _ proof, ⟨schedule⟩⟩⟩
  else .error "Public witness graph and R1CS dimensions differ."

/-- Admission happens entirely on public assets, before original input bytes
or blinding entropy are read by the isolated worker. -/
def loadPublicCertificate (graph : SelectedGraph) (circuit : Groth16R1CS.Circuit)
    (compressed : ByteArray) : Except String (CertifiedPublic graph circuit) := do
  if compressed.size > 2*1024*1024 then throw "Compressed public witness certificate is too large."
  let bytes ← Tornado.Compression.Gzip.decompress compressed (16*1024*1024)
  let some text := String.fromUTF8? bytes | throw "Public witness certificate is not UTF-8."
  let json ← Json.parse text
  let data ← decodePublicCertificate json
  preparePublicCertificate graph circuit data

theorem certifiedPublic_accepted (graph : SelectedGraph) (circuit : Groth16R1CS.Circuit)
    (certified : CertifiedPublic graph circuit) :
    ∃ (data : PublicCertificateData) (compiled : CompiledGraph) (system : LocalSystem),
      graph.nVars = circuit.nVars ∧
      compileGraph (Resolver.ofNodes data.nodes) graph = .ok compiled ∧
      generateLocalSystem data.nodes compiled graph = .ok system ∧
      checkCertificate graph.nVars graph.nSignals system.linears system.nonlinear
        (circuit.constraints.map ofConstraint) data.elimination = .ok () := by
  obtain ⟨data, compiled, system, dimensions, built, generated, checked, _⟩ := certified.accepted
  exact ⟨data, compiled, system, dimensions, built, generated, checked⟩

theorem certifiedPublic_schedule (graph : SelectedGraph) (circuit : Groth16R1CS.Circuit)
    (certified : CertifiedPublic graph circuit) :
    ∃ (data : PublicCertificateData) (compiled : CompiledGraph) (system : LocalSystem),
      graph.nVars = circuit.nVars ∧
      compileGraph (Resolver.ofNodes data.nodes) graph = .ok compiled ∧
      generateLocalSystem data.nodes compiled graph = .ok system ∧
      checkCertificate graph.nVars graph.nSignals system.linears system.nonlinear
        (circuit.constraints.map ofConstraint) data.elimination = .ok () ∧
      Nonempty (PedersenSchedule.CertifiedSchedule (Resolver.ofNodes data.nodes) graph compiled) :=
  certified.accepted

end Tornado.Protocol.WitnessSymbolic
#print axioms Tornado.Protocol.WitnessSymbolic.certifiedPublic_accepted
#print axioms Tornado.Protocol.WitnessSymbolic.certifiedPublic_schedule
