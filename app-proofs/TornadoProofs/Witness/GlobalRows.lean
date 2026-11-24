import TornadoProofs.Witness.CompilationTrace
import TornadoProofs.Witness.GlobalExecution
import TornadoProofs.Witness.LocalRowPhases

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Local
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr
open Execution

/-- Every row regenerated from the actual public graph is satisfied by its
independent DAG interpretation. The checked public elimination certificate
then transports these source equations to the authenticated circuit rows. -/
theorem generateLocalSystem_source (resolver : Resolver) (graph : SelectedGraph)
    (compiled : CompiledGraph) (trace : CompilationTrace resolver graph compiled)
    (inputs values : Array Nat) (denotes : Symbolic.Denotes resolver.nodes inputs values)
    (canonical : Primitive.Bounded values) (source : GraphSourceAdmitted graph compiled values)
    (assignment : Nat → Fr) (constant : assignment 0=1)
    (roots : RootInterpretation compiled assignment values) (system : LocalSystem)
    (generated : generateLocalSystem resolver.nodes compiled graph=.ok system) :
    SystemSatisfied assignment system := by
  have rowValue := signalLinear_value resolver.nodes inputs values denotes compiled assignment constant roots
  have terminal : SourceState compiled values trace.final :=
    ⟨by simpa only [AliasesValid,trace.aliases] using source.aliases,
      complete_nodeFits trace.final compiled trace.complete⟩
  have merkle := merkle_phase_construct resolver inputs values denotes canonical Tornado.Crypto.mimcConstants
    compiled graph.merkle graph.feistel source.selectors trace.withPrimitives trace.final trace.merkleBuilt terminal
  have primitive := primitive_phase_construct resolver inputs values denotes (canonical_lookup values canonical)
    compiled graph.primitives source.primitives trace.withBases trace.withPrimitives trace.primitivesBuilt merkle.1
  have bases := base_phase_construct resolver inputs values denotes (canonical_lookup values canonical)
    compiled graph.bases trace.withBits trace.withBases trace.basesBuilt primitive.1
  unfold generateLocalSystem at generated
  rw [generateLocalSystemWith_bits_source] at generated
  by_cases invalid : (!graph.layoutValid || compiled.signalRoots.size != graph.nSignals ||
      Tornado.Crypto.mimcConstants.size != 220)=true
  · simp only [invalid,↓reduceIte] at generated
    change (Except.error "Public witness local system has an invalid shape." : Except String LocalSystem)=.ok system at generated
    contradiction
  · have validFalse : (!graph.layoutValid || compiled.signalRoots.size != graph.nSignals ||
        Tornado.Crypto.mimcConstants.size != 220)=false := Bool.eq_false_iff.mpr invalid
    simp only [validFalse,Bool.false_eq_true,↓reduceIte,pure_bind] at generated
    obtain ⟨bitsSystem,bitsGenerated,generated⟩ := bind_success _ _ system generated
    unfold localSystemAfterBits at generated
    simp only [pure_bind,forIn_range_zero] at generated
    obtain ⟨basesSystem,basesGenerated,generated⟩ := bind_success _ _ system generated
    obtain ⟨primitiveSystem,primitivesGenerated,generated⟩ := bind_success _ _ system generated
    obtain ⟨merkleSystem,merkleGenerated,generated⟩ := bind_success _ _ system generated
    have result : merkleSystem.linear (minusLinear (signalLinear resolver.nodes compiled graph.rootSignal)
        (signalLinear resolver.nodes compiled graph.merkle[19]!.hashOutput))=system := Except.ok.inj generated
    have bitsValid := bits_phase_localRows resolver inputs values denotes canonical compiled assignment constant
      roots rowValue graph.num2bits source.bits trace.withCommitment trace.withBits {} bitsSystem
      trace.bitsBuilt bitsGenerated bases.1 (empty_system assignment)
    have basesGenerated' : (forIn graph.bases bitsSystem (fun base current => do
        let next ← baseRowAction base current
        pure (ForInStep.yield next)))=.ok basesSystem := by
      simpa only [baseRowAction,pure,Except.pure,bind,Except.bind] using basesGenerated
    have basesValid := base_phase_localRows resolver inputs values denotes canonical compiled assignment constant
      roots graph.bases trace.withBits trace.withBases bitsSystem basesSystem trace.basesBuilt basesGenerated' primitive.1 bitsValid
    have primitiveValid := primitive_phase_localRows resolver inputs values denotes canonical compiled assignment constant
      roots rowValue graph.primitives source.primitives trace.withBases trace.withPrimitives basesSystem primitiveSystem
      trace.primitivesBuilt primitivesGenerated merkle.1 basesValid
    have finalInterpreted := interpreted_of_fit compiled trace.final assignment values roots terminal.2
    have publicNullifier := interpreted_read trace.final assignment values finalInterpreted 2
      compiled.publicNullifier.1 trace.publicNullifierRead
    have computedNullifier := interpreted_read trace.final assignment values finalInterpreted 28300
      compiled.publicNullifier.2 trace.computedNullifierRead
    have nullifierEquation : assignment 28300=assignment 2 := by
      rw [computedNullifier,publicNullifier,source.nullifier]
    have nullifierValid : SystemSatisfied assignment (primitiveSystem.linear
        (minusLinear (signalLinear resolver.nodes compiled 28300) (signalLinear resolver.nodes compiled 2))) := by
      apply linear_emit assignment primitiveSystem _ primitiveValid
      rw [minusLinear_value,rowValue,rowValue,nullifierEquation,sub_self]
    have merkleGenerated' : (forIn (List.range 20)
        (primitiveSystem.linear (minusLinear (signalLinear resolver.nodes compiled 28300)
          (signalLinear resolver.nodes compiled 2))) (fun index current => do
        let next ← merkleRowAction resolver.nodes compiled Tornado.Crypto.mimcConstants graph.merkle graph.feistel index current
        pure (ForInStep.yield next)))=.ok merkleSystem := by
      simpa only [merkleRowAction,pure,Except.pure,bind,Except.bind] using merkleGenerated
    have merkleValid := merkle_phase_localRows resolver inputs values denotes canonical compiled assignment constant
      roots rowValue Tornado.Crypto.mimcConstants graph.merkle graph.feistel source.selectors
      trace.withPrimitives trace.final _ merkleSystem trace.merkleBuilt merkleGenerated' terminal nullifierValid
    rw [←result]
    apply linear_emit assignment merkleSystem _ merkleValid
    have publicRoot := interpreted_read trace.final assignment values finalInterpreted graph.rootSignal
      compiled.publicRoot.1 trace.publicRootRead
    have computedRoot := interpreted_read trace.final assignment values finalInterpreted graph.merkle[19]!.hashOutput
      compiled.publicRoot.2 trace.computedRootRead
    rw [minusLinear_value,rowValue,rowValue,publicRoot,computedRoot,source.root,sub_self]

end TornadoProofs.Witness.Local
#print axioms TornadoProofs.Witness.Local.generateLocalSystem_source
