import TornadoProofs.Witness.CheckedWitnessConstruction

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate

/-- Well-founded values computed from the original source prefix and native
commitment. This interpretation does not execute or accept a circuit witness. -/
def sourceValues (resolver : Resolver) (inputs : Array Nat) (commitment : Nat) : Array Nat :=
  Symbolic.mathematicalValues resolver.nodes (inputs.push commitment)

theorem pushed_inputs_bounded (inputs : Array Nat) (commitment : Nat)
    (canonical : Primitive.Bounded inputs) (commitmentBound : commitment<Field.q) :
    ∀ (index : Nat),(inputs.push commitment)[index]! < Field.q := by
  have bounded : Primitive.Bounded (inputs.push commitment) := by
    intro value member
    have member' : value∈inputs.push commitment := by simpa using member
    rcases Array.mem_push.mp member' with previous | equal
    · exact canonical value (Array.mem_toList_iff.mpr previous)
    · simpa only [equal] using commitmentBound
  exact canonical_lookup _ bounded

theorem sourceValues_denotes (resolver : Resolver) (inputs : Array Nat) (commitment : Nat)
    (valid : tableValid resolver.nodes=true) :
    Symbolic.Denotes resolver.nodes (inputs.push commitment) (sourceValues resolver inputs commitment) :=
  Symbolic.mathematicalValues_denotes resolver.nodes (inputs.push commitment)
    (Symbolic.tableValid_topological resolver.nodes valid)

theorem sourceValues_bounded (resolver : Resolver) (inputs : Array Nat) (commitment : Nat)
    (valid : tableValid resolver.nodes=true) (canonical : Primitive.Bounded inputs)
    (commitmentBound : commitment<Field.q) : Primitive.Bounded (sourceValues resolver inputs commitment) :=
  Symbolic.mathematicalValues_bounded resolver.nodes (inputs.push commitment) valid
    (pushed_inputs_bounded inputs commitment canonical commitmentBound)

theorem pushed_prefix (inputs : Array Nat) (commitment : Nat) (size : inputs.size=49)
    (index : Nat) (bound : index<49) : (inputs.push commitment)[index]! = inputs[index]! := by
  have previous : index < inputs.size := by simpa only [size] using bound
  have extended : index<(inputs.push commitment).size := by simp only [Array.size_push]; omega
  rw [getElem!_pos (inputs.push commitment) index extended,Array.getElem_push_lt previous,
    getElem!_pos inputs index previous]

theorem pushed_commitment (inputs : Array Nat) (commitment : Nat) (size : inputs.size=49) :
    (inputs.push commitment)[49]! = commitment := by
  have extended : 49<(inputs.push commitment).size := by simp only [Array.size_push,size]; decide
  rw [getElem!_pos (inputs.push commitment) 49 extended]
  simpa only [←size] using (Array.getElem_push_eq (xs:=inputs) (x:=commitment))

/-- The returned actual witness is constructed from canonical original input
fields and their independent mathematical graph interpretation. The remaining
source predicate contains explicit bit/inverse/commitment/Merkle facts. -/
theorem generateCheckedWitness_source (pinnedGraph : PinnedGraph) (pinned : PinnedCircuit)
    (resolver : Resolver) (compiled : CompiledGraph) (system : LocalSystem) (certificate : Certificate)
    (variableCount : pinnedGraph.graph.nVars=pinned.circuit.nVars)
    (publicCompiled : compileGraph resolver pinnedGraph.graph=.ok compiled)
    (publicGenerated : generateLocalSystem resolver.nodes compiled pinnedGraph.graph=.ok system)
    (publicChecked : checkCertificate pinnedGraph.graph.nVars pinnedGraph.graph.nSignals
      system.linears system.nonlinear (pinned.circuit.constraints.map ofConstraint) certificate=.ok ())
    (inputs : Array Nat) (commitment : Nat) (inputSize : inputs.size=49) (constant : inputs[0]! = 1)
    (canonical : Primitive.Bounded inputs) (commitmentBound : commitment<Field.q)
    (source : GraphSourceAdmitted pinnedGraph.graph compiled (sourceValues resolver inputs commitment)) :
    generateCheckedWitness pinnedGraph pinned inputs commitment =
      .ok (witnessValues compiled.signalRoots (sourceValues resolver inputs commitment) pinnedGraph.graph.nVars) := by
  obtain ⟨trace⟩ := compileGraph_trace resolver pinnedGraph.graph compiled publicCompiled
  exact generateCheckedWitness_construct pinnedGraph pinned resolver compiled system certificate variableCount
    publicCompiled publicGenerated publicChecked (inputs.push commitment) inputs (sourceValues resolver inputs commitment)
    commitment (sourceValues_denotes resolver inputs commitment trace.table)
    (sourceValues_bounded resolver inputs commitment trace.table canonical commitmentBound) inputSize constant
    (pushed_prefix inputs commitment inputSize) (pushed_commitment inputs commitment inputSize) source

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.pushed_inputs_bounded
#print axioms TornadoProofs.Witness.Execution.sourceValues_denotes
#print axioms TornadoProofs.Witness.Execution.sourceValues_bounded
#print axioms TornadoProofs.Witness.Execution.pushed_prefix
#print axioms TornadoProofs.Witness.Execution.pushed_commitment
#print axioms TornadoProofs.Witness.Execution.generateCheckedWitness_source
