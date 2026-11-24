import TornadoProofs.Witness.WitnessValues
import TornadoProofs.Witness.SourceConstant
import LeanCryptoProofs.ConstraintCertificate.R1CSBridge

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr

/-- The actual complete VM and authenticated R1CS checker succeed from
independent arithmetic source conditions plus a checked public-only wiring
certificate. No final execution or R1CS-check success is assumed. -/
theorem generateCheckedWitness_construct (pinnedGraph : PinnedGraph) (pinned : PinnedCircuit)
    (resolver : Resolver) (compiled : CompiledGraph) (system : LocalSystem) (certificate : Certificate)
    (variableCount : pinnedGraph.graph.nVars=pinned.circuit.nVars)
    (publicCompiled : compileGraph resolver pinnedGraph.graph=.ok compiled)
    (publicGenerated : generateLocalSystem resolver.nodes compiled pinnedGraph.graph=.ok system)
    (publicChecked : checkCertificate pinnedGraph.graph.nVars pinnedGraph.graph.nSignals
      system.linears system.nonlinear (pinned.circuit.constraints.map ofConstraint) certificate=.ok ())
    (data inputs values : Array Nat) (commitment : Nat)
    (denotes : Symbolic.Denotes resolver.nodes data values) (canonical : Primitive.Bounded values)
    (inputSize : inputs.size=49) (constant : inputs[0]! = 1)
    (agreement : ∀ index<49,data[index]! = inputs[index]!) (commitmentValue : data[49]! = commitment)
    (source : GraphSourceAdmitted pinnedGraph.graph compiled values) :
    generateCheckedWitness pinnedGraph pinned inputs commitment =
      .ok (witnessValues compiled.signalRoots values pinnedGraph.graph.nVars) := by
  obtain ⟨trace⟩ := compileGraph_trace resolver pinnedGraph.graph compiled publicCompiled
  have sourceConstant := trace_constant resolver pinnedGraph.graph compiled trace data inputs values
    denotes canonical agreement constant source
  let assignment : Nat → Fr := fun index => model values[compiled.signalRoots[index]!]!
  have rootMeaning : Local.RootInterpretation compiled assignment values := fun _ => rfl
  have assignmentConstant : assignment 0=1 := by
    change model values[compiled.signalRoots[0]!]! = 1
    rw [sourceConstant]
    exact Field.model_one
  have sources := Local.generateLocalSystem_source resolver pinnedGraph.graph compiled trace data values
    denotes canonical source assignment assignmentConstant rootMeaning system publicGenerated
  let witness := witnessValues compiled.signalRoots values pinnedGraph.graph.nVars
  have dimensions := graph_layout_dimensions pinnedGraph.graph trace.layout
  have shape : witness.size=pinned.circuit.nVars := (witnessValues_size _ _ _).trans variableCount
  have witnessConstant : witness[0]?=some 1 := witnessValues_constant _ _ _
    (by rw [dimensions.2]; decide) sourceConstant
  have agrees : ∀ index,index<pinned.circuit.nVars → assignment index=model witness[index]! := by
    intro index bound
    have bound' : index<pinnedGraph.graph.nVars := by simpa only [variableCount] using bound
    rw [witnessValues_get _ _ _ index bound']
  have checked : checkCertificate pinned.circuit.nVars pinnedGraph.graph.nSignals
      system.linears system.nonlinear (pinned.circuit.constraints.map ofConstraint) certificate=.ok () := by
    simpa only [variableCount] using publicChecked
  have r1cs := checkCertificate_constructs_r1cs pinned.circuit witness pinnedGraph.graph.nSignals
    system.linears system.nonlinear certificate assignment assignmentConstant agrees sources.1 sources.2
    checked shape witnessConstant (witnessValues_canonical _ _ _ canonical)
  rw [pinned.dimensions.2.2] at r1cs
  obtain ⟨state,complete,_,executed⟩ := compileGraphWith_execution resolver pinnedGraph.graph data inputs values
    commitment compiled publicCompiled denotes canonical inputSize constant agreement commitmentValue source
  have materialized : (realize state values).toWitness pinnedGraph.graph=.ok witness :=
    toWitness_complete pinnedGraph.graph state compiled.signalRoots values trace.layout complete
      (localSystem_shape resolver.nodes compiled pinnedGraph.graph system publicGenerated)
      (by rw [dimensions.1,dimensions.2]; decide)
  unfold generateCheckedWitness
  rw [executed]
  change finishCheckedWitness pinnedGraph pinned (realize state values)=.ok witness
  unfold finishCheckedWitness
  rw [materialized]
  dsimp only
  rw [r1cs]
  rfl

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.generateCheckedWitness_construct
