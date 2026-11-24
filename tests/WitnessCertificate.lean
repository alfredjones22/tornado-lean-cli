import Tornado.Protocol.PublicWitnessCertificate
import Tornado.Protocol.PedersenSchedule

open Lean Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.Groth16R1CS

def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)


namespace ScheduleRegression
open Tornado.Protocol.PedersenSchedule
def requireResult {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def requireRejected {α : Type} (result : Except String α) (label : String) : IO Unit :=
  if result.isOk then throw (IO.userError s!"unexpected schedule acceptance: {label}") else pure ()

def run (graph : SelectedGraph) (data : PublicCertificateData) : IO Unit := do
  let resolver := Resolver.ofNodes data.nodes
  let compiled ← requireResult (compileGraph resolver graph)
  let _ ← requireResult (certifySchedule resolver graph compiled)
  let reference ← requireResult (referenceSchedule resolver graph)
  let checkGraph (candidate : SelectedGraph) (observed : CompiledGraph) : Except String Unit := do
    let actual ← actualPointSteps observed candidate
    if scheduleMatches reference actual observed then pure () else throw "Independent schedule mismatch."
  let renamed := {graph with primitives := graph.primitives.map fun p => {p with name := "ignored public candidate name"}}
  let _ ← requireResult (checkGraph renamed compiled)
  let muxIndex := (graph.primitives.findIdx? (fun p => p.kind == "MultiMux3")).getD 0
  let mux := graph.primitives[muxIndex]!
  let signIndex := (graph.primitives.findIdx? (fun p => p.kind == "Window4")).getD 0
  let signed := graph.primitives[signIndex]!
  let mutate (index : Nat) (p : Primitive) := {graph with primitives := graph.primitives.set! index p}
  requireRejected (checkGraph (mutate muxIndex {mux with inputs := mux.inputs.set! 0 graph.num2bits[1]!.outputs[0]!}) compiled) "wrong original bit source"
  requireRejected (checkGraph (mutate muxIndex {mux with inputs := (mux.inputs.set! 0 mux.inputs[1]!).set! 1 mux.inputs[0]!}) compiled) "swapped selector positions"
  requireRejected (checkGraph (mutate muxIndex {mux with inputs := (mux.inputs.set! 3 mux.inputs[4]!).set! 4 mux.inputs[3]!}) compiled) "wrong magnitude table"
  requireRejected (checkGraph (mutate signIndex {signed with inputs := signed.inputs.set! 1 graph.num2bits[0]!.outputs[4]!}) compiled) "wrong sign bit"
  let first := graph.primitives[0]!
  requireRejected (checkGraph (mutate 0 {first with inputs := first.inputs.set! 0 7}) compiled) "wrong base edge"
  requireRejected (checkGraph (mutate 0 {first with outputs := first.outputs.set! 0 7}) compiled) "wrong output edge"
  requireRejected (checkGraph (mutate 0 {first with kind := "MontgomeryAdd"}) compiled) "wrong point operation"
  let extra : Primitive := ⟨"MontgomeryAdd", "unused injected point operation", #[7,8,7,8], #[7,8,9]⟩
  requireRejected (checkGraph {graph with primitives := graph.primitives.push extra} compiled) "unaccounted point denominator"
  let aliases := compiled.commitmentAliases
  requireRejected (checkGraph graph {compiled with commitmentAliases := aliases.push aliases[0]!}) "extra commitment alias"
  requireRejected (checkGraph graph {compiled with commitmentAliases := #[(0,aliases[0]!.2)]}) "wrong commitment source"
  requireRejected (checkGraph graph {compiled with commitmentAliases := #[(aliases[0]!.1,0)]}) "wrong commitment result"
  requireRejected (checkGraph graph {compiled with publicNullifier := (compiled.publicNullifier.1,0)}) "wrong nullifier result"
  requireRejected (referenceSchedule resolver {graph with bases := graph.bases.reverse}) "wrong generator ordering"
  IO.println "PASS: 15 independent Pedersen schedule checks (2 acceptance, 13 adversarial rejection)"

end ScheduleRegression

def main : IO Unit := do
  let graphRaw ← IO.FS.readFile "fixtures/witness-vm-selected-components.json"
  let pinnedGraph ← IO.ofExcept (decodePinnedGraph graphRaw)
  let circuitZip ← IO.FS.readBinFile "assets/proving/tornado-3ddd61dbff09caee.json.gz"
  let bytes ← IO.ofExcept (Tornado.Compression.Gzip.pinnedCircuit circuitZip)
  let some circuitText := String.fromUTF8? bytes | throw (IO.userError "Circuit UTF-8")
  let circuitJson ← IO.ofExcept (Json.parse circuitText)
  let circuit ← IO.ofExcept (decodeCircuit circuitJson)
  let compressed ← IO.FS.readBinFile "assets/proving/tornado-witness-certificate-v1.json.gz"
  let _ ← IO.ofExcept (loadPublicCertificate pinnedGraph.graph circuit compressed)
  IO.println s!"PASS: actual public-asset gate admits all {circuit.constraints.size} rows before any private input"
  let oversized := ByteArray.mk (Array.replicate (2*1024*1024+1) 0)
  require (!(loadPublicCertificate pinnedGraph.graph circuit oversized).isOk) "Oversized certificate accepted."
  let corrupted := compressed.set! (compressed.size-1) (compressed[compressed.size-1]! ^^^ 1)
  require (!(loadPublicCertificate pinnedGraph.graph circuit corrupted).isOk) "Corrupted gzip accepted."
  require (!(decodePublicCertificate (Json.mkObj [("schemaVersion",toJson (2:Nat))])).isOk)
    "Unsupported schema accepted."
  let publicBytes ← IO.ofExcept (Tornado.Compression.Gzip.decompress compressed (16*1024*1024))
  let some text := String.fromUTF8? publicBytes | throw (IO.userError "Public UTF-8")
  let data ← IO.ofExcept (decodePublicCertificate (← IO.ofExcept (Json.parse text)))
  let wrongOne := {data with nodes := data.nodes.set! 1 (.constant 2)}
  require (!(preparePublicCertificate pinnedGraph.graph circuit wrongOne).isOk)
    "Missing constant-one expression accepted."
  let forward := {data with nodes := data.nodes.push (.mul data.nodes.size 0)}
  require (!(preparePublicCertificate pinnedGraph.graph circuit forward).isOk)
    "Forward DAG reference accepted."
  let firstBase := pinnedGraph.graph.bases[0]!
  let wrongBase := { pinnedGraph.graph with
    bases := pinnedGraph.graph.bases.set! 0 {firstBase with value := firstBase.value + 1} }
  require (!(certifyPedersenBases wrongBase).isOk) "Changed native/circuit Pedersen base accepted."
  let wrongIndex := { pinnedGraph.graph with
    bases := pinnedGraph.graph.bases.set! 0 {firstBase with index := firstBase.index + 1} }
  require (!(certifyPedersenBases wrongIndex).isOk) "Changed Pedersen base signal accepted."
  IO.println "PASS: public certificate size, gzip integrity, schema, constant-one, topology, and Pedersen base mutations reject"
  ScheduleRegression.run pinnedGraph.graph data
