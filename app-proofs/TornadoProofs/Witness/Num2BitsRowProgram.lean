import TornadoProofs.Witness.PrimitiveRowProgram
import TornadoProofs.Witness.SignalWriteMany

set_option autoImplicit false
namespace TornadoProofs.Witness.Local
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate

/-- Proof-visible extraction of the actual inline bit-row body. -/
def num2BitsLocalSystem (nodes : Array Node) (compiled : CompiledGraph)
    (seed : LocalSystem) (component : Num2BitsComponent) : Except String LocalSystem := do
  let row := signalLinear nodes compiled
  let mut result := seed
  let mut reconstructed : Linear := []
  for bit in [0:component.outputs.size] do
    let output := row component.outputs[bit]!
    result := result.constraint output (minusLinear output (constantLinear 1)) []
    reconstructed := addLinear reconstructed (scaleLinear (2^bit) output)
  pure (result.linear (minusLinear (row component.input) reconstructed))

def localSystemAfterBits (nodes : Array Node) (compiled : CompiledGraph)
    (graph : SelectedGraph) (constants : Array Nat) (seed : LocalSystem) : Except String LocalSystem := do
  let row := signalLinear nodes compiled
  let mut result := seed
  for base in graph.bases do result := result.equality base.index (constantLinear base.value)
  for primitive in graph.primitives do result ← primitiveLocalSystem nodes compiled result primitive
  result := result.linear (minusLinear (row 28300) (row 2))
  for i in [0:20] do result := merkleLocalSystem nodes compiled constants result graph.merkle[i]! graph.feistel[i]!
  result := result.linear (minusLinear (row graph.rootSignal) (row graph.merkle[19]!.hashOutput))
  return result

theorem generateLocalSystemWith_bits_source (nodes : Array Node) (compiled : CompiledGraph)
    (graph : SelectedGraph) (constants : Array Nat) :
    generateLocalSystemWith nodes compiled graph constants = (do
      if !graph.layoutValid || compiled.signalRoots.size != graph.nSignals || constants.size != 220 then
        throw "Public witness local system has an invalid shape."
      let mut result : LocalSystem := {}
      for component in graph.num2bits do result ← num2BitsLocalSystem nodes compiled result component
      localSystemAfterBits nodes compiled graph constants result) := by
  unfold generateLocalSystemWith num2BitsLocalSystem localSystemAfterBits
  simp only [bind_assoc,pure_bind]

abbrev BitRowsFrame := MProd Linear LocalSystem

def bitRowsStep (nodes : Array Node) (compiled : CompiledGraph)
    (component : Num2BitsComponent) (bit : Nat) (frame : BitRowsFrame) : BitRowsFrame :=
  let output := signalLinear nodes compiled component.outputs[bit]!
  ⟨addLinear frame.fst (scaleLinear (2^bit) output),
    frame.snd.constraint output (minusLinear output (constantLinear 1)) []⟩

def bitRowsEffect (nodes : Array Node) (compiled : CompiledGraph)
    (component : Num2BitsComponent) (bit : Nat) (frame : BitRowsFrame) : Except String (ForInStep BitRowsFrame) :=
  pure (.yield (bitRowsStep nodes compiled component bit frame))

theorem num2BitsLocalSystem_source (nodes : Array Node) (compiled : CompiledGraph)
    (seed : LocalSystem) (component : Num2BitsComponent) :
    num2BitsLocalSystem nodes compiled seed component = (do
      let frame ← forIn (List.range component.outputs.size) (⟨[],seed⟩ : BitRowsFrame)
        (bitRowsEffect nodes compiled component)
      pure (frame.snd.linear (minusLinear (signalLinear nodes compiled component.input) frame.fst))) := by
  unfold num2BitsLocalSystem
  dsimp only
  rw [Execution.forIn_range_zero]
  rfl

end TornadoProofs.Witness.Local
#print axioms TornadoProofs.Witness.Local.generateLocalSystemWith_bits_source
#print axioms TornadoProofs.Witness.Local.num2BitsLocalSystem_source
