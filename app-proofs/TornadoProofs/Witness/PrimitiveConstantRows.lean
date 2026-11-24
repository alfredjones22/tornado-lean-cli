import TornadoProofs.Witness.PrimitiveRowProgram

set_option autoImplicit false
namespace TornadoProofs.Witness.Local
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr

theorem constantRowEffect_sound (nodes : Array Node) (compiled : CompiledGraph)
    (assignment : Nat → Fr)
    (rowValue : ∀ index, linearValue assignment (signalLinear nodes compiled index)=assignment index)
    (index : Nat) (seed : LocalSystem) (next : ForInStep LocalSystem)
    (valid : SystemSatisfied assignment seed)
    (returned : constantRowEffect nodes compiled index seed=.ok next) :
    SystemSatisfied assignment next.value := by
  cases folded : constantAt nodes compiled.signalRoots[index]! with
  | none =>
    have equal : ForInStep.yield seed=next := by
      simpa only [constantRowEffect,folded,pure,Except.pure,Except.ok.injEq] using returned
    subst next
    exact valid
  | some value =>
    have equal : ForInStep.yield (seed.equality index (constantLinear value))=next := by
      simpa only [constantRowEffect,folded,pure,Except.pure,Except.ok.injEq] using returned
    subst next
    apply equality_emit assignment seed _ _ valid
    have known := rowValue index
    simpa only [signalLinear,folded] using known.symm

theorem constantRows_sound (nodes : Array Node) (compiled : CompiledGraph)
    (assignment : Nat → Fr)
    (rowValue : ∀ index, linearValue assignment (signalLinear nodes compiled index)=assignment index)
    (indices : List Nat) (seed after : LocalSystem) (valid : SystemSatisfied assignment seed)
    (returned : forIn indices seed (constantRowEffect nodes compiled)=.ok after) :
    SystemSatisfied assignment after := by
  apply forIn_success_invariant indices (constantRowEffect nodes compiled)
    (SystemSatisfied assignment) _ seed valid after returned
  intro index member before previous next step
  exact constantRowEffect_sound nodes compiled assignment rowValue index before next previous step

end TornadoProofs.Witness.Local
#print axioms TornadoProofs.Witness.Local.constantRowEffect_sound
#print axioms TornadoProofs.Witness.Local.constantRows_sound
