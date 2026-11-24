import TornadoProofs.Witness.CompilationTrace

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

/-- Independent arithmetic/source conditions on the well-founded public DAG
interpretation. These do not mention VM acceptance or R1CS checker success. -/
structure GraphSourceAdmitted (graph : SelectedGraph) (compiled : CompiledGraph)
    (values : Array Nat) : Prop where
  aliases : ∀ pair∈compiled.commitmentAliases.toList,values[pair.1]! = values[pair.2]!
  bits : ∀ component∈graph.num2bits,BitSourceAdmitted compiled values component
  primitives : ∀ primitive∈graph.primitives,PrimitiveSourceAdmitted compiled values primitive
  selectors : ∀ index<20,MerkleSourceAdmitted compiled values graph.merkle[index]!
  root : values[compiled.publicRoot.1]! = values[compiled.publicRoot.2]!
  nullifier : values[compiled.publicNullifier.1]! = values[compiled.publicNullifier.2]!

theorem compileGraphWith_execution (resolver : Resolver) (graph : SelectedGraph)
    (data inputs values : Array Nat) (commitment : Nat) (compiled : CompiledGraph)
    (publicCompiled : compileGraph resolver graph=.ok compiled)
    (denotes : Symbolic.Denotes resolver.nodes data values) (canonical : Primitive.Bounded values)
    (inputSize : inputs.size=49) (constant : inputs[0]! = 1)
    (agreement : ∀ index<49,data[index]! = inputs[index]!)
    (commitmentValue : data[49]! = commitment)
    (source : GraphSourceAdmitted graph compiled values) :
    ∃ state : SignalState, state.slots=compiled.signalRoots.map some ∧
      state.commitmentAliases=compiled.commitmentAliases ∧
      executeSelected graph inputs commitment=.ok (realize state values) := by
  obtain ⟨trace⟩ := compileGraph_trace resolver graph compiled publicCompiled
  have terminal : SourceState compiled values trace.final :=
    ⟨by simpa only [AliasesValid,trace.aliases] using source.aliases,
      complete_nodeFits trace.final compiled trace.complete⟩
  have merkle := merkle_phase_construct resolver data values denotes canonical Tornado.Crypto.mimcConstants
    compiled graph.merkle graph.feistel source.selectors trace.withPrimitives trace.final trace.merkleBuilt terminal
  have bounded : ∀ (index : Nat),values[index]! < Tornado.Protocol.Groth16R1CS.scalarPrime :=
    canonical_lookup values canonical
  have primitives := primitive_phase_construct resolver data values denotes bounded compiled graph.primitives
    source.primitives trace.withBases trace.withPrimitives trace.primitivesBuilt merkle.1
  have bases := base_phase_construct resolver data values denotes bounded compiled graph.bases
    trace.withBits trace.withBases trace.basesBuilt primitives.1
  have bits := num2Bits_phase_construct resolver data values denotes bounded compiled graph.num2bits
    source.bits trace.withCommitment trace.withBits trace.bitsBuilt bases.1
  have commit := commitment_construct resolver data values denotes bounded commitment commitmentValue
    graph.commitmentSignal compiled trace.seeded trace.withCommitment trace.commitmentNode
    trace.commitmentResolved trace.commitmentBuilt bits.1
  have seeds := seed_phase_construct resolver data inputs values denotes bounded agreement constant
    compiled (SignalState.empty graph.nSignals) trace.seeded trace.seedsBuilt commit.1
  simp only [bind,Except.bind] at seeds commit bits bases primitives merkle
  refine ⟨trace.final,trace.complete,trace.aliases,?_⟩
  unfold executeSelected
  simp only [trace.layout,inputSize,bne_self_eq_false,Bool.not_true,Bool.false_or,Bool.false_eq_true,
    constant,↓reduceIte,forIn_range_zero,pure_bind]
  rw [← realize_empty graph.nSignals values]
  simp only [bind,Except.bind]
  rw [seeds.2]
  dsimp only
  rw [commit.2]
  dsimp only
  rw [bits.2]
  dsimp only
  rw [bases.2]
  dsimp only
  rw [primitives.2]
  dsimp only
  rw [merkle.2]
  dsimp only
  rw [signalRead_realize trace.final values graph.rootSignal compiled.publicRoot.1 trace.publicRootRead]
  dsimp only
  rw [signalRead_realize trace.final values graph.merkle[19]!.hashOutput compiled.publicRoot.2 trace.computedRootRead]
  dsimp only
  simp only [source.root,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,pure,Except.pure]

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.compileGraphWith_execution
