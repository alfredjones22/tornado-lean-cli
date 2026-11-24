import TornadoProofs.Witness.PrefixMeaning

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

theorem witnessValues_source_slice (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (trace : CompilationTrace resolver graph compiled) (inputs : Array Nat) (commitment : Nat)
    (size : inputs.size=49) (constant : inputs[0]! = 1) :
    (witnessValues compiled.signalRoots (sourceValues resolver inputs commitment) graph.nVars).extract 1 7 =
      inputs.extract 1 7 := by
  let witness := witnessValues compiled.signalRoots (sourceValues resolver inputs commitment) graph.nVars
  have dimensions := graph_layout_dimensions graph trace.layout
  have witnessSize : witness.size=28300 := (witnessValues_size _ _ _).trans dimensions.2
  have leftSize : (witness.extract 1 7).size=6 := by simp only [Array.size_extract,witnessSize]; rfl
  have rightSize : (inputs.extract 1 7).size=6 := by simp only [Array.size_extract,size]; rfl
  change witness.extract 1 7=inputs.extract 1 7
  apply Array.ext
  · exact leftSize.trans rightSize.symm
  · intro index leftBound rightBound
    have bound : index<6 := by simpa only [leftSize] using leftBound
    have inputBound : 1+index < inputs.size := by rw [size]; omega
    have witnessBound : 1+index < witness.size := by rw [witnessSize]; omega
    have graphBound : 1+index < graph.nVars := by rw [dimensions.2]; omega
    have value : witness[1+index]! = inputs[1+index]! :=
      (witnessValues_get _ _ _ _ graphBound).trans
        (source_prefix_meaning resolver graph compiled trace inputs commitment size constant (1+index) (by omega))
    rw [Array.getElem_extract,Array.getElem_extract]
    simpa only [getElem!_pos witness (1+index) witnessBound,getElem!_pos inputs (1+index) inputBound] using value

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.witnessValues_source_slice
