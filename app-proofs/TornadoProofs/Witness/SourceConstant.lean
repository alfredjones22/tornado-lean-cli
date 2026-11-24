import TornadoProofs.Witness.GlobalRows

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

theorem trace_seed_sourceState (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (trace : CompilationTrace resolver graph compiled) (data values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes data values) (canonical : Primitive.Bounded values)
    (source : GraphSourceAdmitted graph compiled values) : SourceState compiled values trace.seeded := by
  have terminal : SourceState compiled values trace.final :=
    ⟨by simpa only [AliasesValid,trace.aliases] using source.aliases,
      complete_nodeFits trace.final compiled trace.complete⟩
  have merkle := merkle_phase_construct resolver data values denotes canonical Tornado.Crypto.mimcConstants
    compiled graph.merkle graph.feistel source.selectors trace.withPrimitives trace.final trace.merkleBuilt terminal
  have primitive := primitive_phase_construct resolver data values denotes (canonical_lookup values canonical)
    compiled graph.primitives source.primitives trace.withBases trace.withPrimitives trace.primitivesBuilt merkle.1
  have bases := base_phase_construct resolver data values denotes (canonical_lookup values canonical)
    compiled graph.bases trace.withBits trace.withBases trace.basesBuilt primitive.1
  have bits := num2Bits_phase_construct resolver data values denotes (canonical_lookup values canonical)
    compiled graph.num2bits source.bits trace.withCommitment trace.withBits trace.bitsBuilt bases.1
  exact ⟨signalWrite_aliases_backwards trace.seeded trace.withCommitment values _ _ trace.commitmentBuilt bits.1.1,
    nodeFits_backwards compiled trace.seeded trace.withCommitment
      (signalWrite_extends _ _ _ _ trace.commitmentBuilt) bits.1.2⟩

theorem trace_constant (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (trace : CompilationTrace resolver graph compiled) (data inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes data values) (canonical : Primitive.Bounded values)
    (agreement : ∀ index<49,data[index]! = inputs[index]!) (constant : inputs[0]! = 1)
    (source : GraphSourceAdmitted graph compiled values) : values[compiled.signalRoots[0]!]! = 1 := by
  have terminal := trace_seed_sourceState resolver graph compiled trace data values denotes canonical source
  have seeds := seed_phase_construct resolver data inputs values denotes (canonical_lookup values canonical)
    agreement constant compiled (SignalState.empty graph.nSignals) trace.seeded trace.seedsBuilt terminal
  have writes : runAssignments (realize (SignalState.empty graph.nSignals) values)
      ((List.range 49).map fun index => (index,inputs[index]!))=.ok (realize trace.seeded values) := by
    rw [runAssignments_map]
    exact seeds.2
  have assigned : Assigned (realize trace.seeded values) 0 1 :=
    (runAssignments_success _ _ _ writes).2 0 1
      (List.mem_map.mpr ⟨0,by simp,by simp only [constant]⟩)
  let assignment : Nat → LeanCrypto.Proofs.ConstraintCertificate.Fr := fun index => Field.model values[compiled.signalRoots[index]!]!
  have interpreted := Local.interpreted_of_fit compiled trace.seeded assignment values
    (fun _ => rfl) terminal.2
  have fieldEqual : Field.model values[compiled.signalRoots[0]!]! = Field.model 1 :=
    Local.signalInterpretation_assigned trace.seeded assignment values interpreted 0 1 assigned
  exact Field.model_injective_bounded _ _ (canonical_lookup values canonical _) (by decide) fieldEqual

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.trace_seed_sourceState
#print axioms TornadoProofs.Witness.Execution.trace_constant
