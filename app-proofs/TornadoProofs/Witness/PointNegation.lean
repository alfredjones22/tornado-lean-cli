import TornadoProofs.Witness.OperationFacts

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open LeanCrypto.Proofs.BabyJubjub

theorem montgomery_neg_curve (u v : Field) (equation : Montgomery u v) : Montgomery u (-v) := by
  simpa only [Montgomery,neg_sq] using equation

theorem montgomeryPoint_neg (u v : Field) (equation : Montgomery u v) :
    montgomeryPoint u (-v) (montgomery_neg_curve u v equation)= -montgomeryPoint u v equation := by
  change WeierstrassCurve.Affine.Point.some u (-v) _ =
    WeierstrassCurve.Affine.Point.neg (WeierstrassCurve.Affine.Point.some u v _)
  simp only [WeierstrassCurve.Affine.Point.neg,WeierstrassCurve.Affine.negY,curve,zero_mul,sub_zero]

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.montgomery_neg_curve
#print axioms TornadoProofs.Witness.PedersenReference.montgomeryPoint_neg
