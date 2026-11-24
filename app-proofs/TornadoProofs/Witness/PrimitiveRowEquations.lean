import TornadoProofs.Witness.PrimitiveRowProgram

set_option autoImplicit false
namespace TornadoProofs.Witness.Local
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr
open TornadoProofs.Witness.Primitive

def KindEquations (kind : Kind) (i o : Array Nat) : Prop :=
  match kind with
  | .montgomeryAdd => MontgomeryAddEquations i o
  | .montgomeryDouble => MontgomeryDoubleEquations i o
  | .edwards2Montgomery => Edwards2MontgomeryEquations i o
  | .montgomery2Edwards => Montgomery2EdwardsEquations i o
  | .babyAdd => BabyAddEquations i o
  | .window4 => Window4Equations i o
  | .square => SquareEquations i o
  | .multiMux3 =>
    TornadoProofs.Witness.Field.model o[0]! = TornadoProofs.Witness.Field.model i[1]! * TornadoProofs.Witness.Field.model i[0]! ∧
    CoordinateEquations i 0 i[0]! i[1]! i[2]!
      (TornadoProofs.Witness.Field.mul i[1]! i[0]!) (coordinateAt o 0) ∧
    CoordinateEquations i 1 i[0]! i[1]! i[2]!
      (TornadoProofs.Witness.Field.mul i[1]! i[0]!) (coordinateAt o 1)

theorem kindValues_equations (kind : Kind) (i : Array Nat) (admitted : kind.Admitted i) :
    KindEquations kind i (kind.values i) := by
  cases kind with
  | montgomeryAdd => exact montgomeryAdd_equations i (by simpa only [Kind.Admitted,TornadoProofs.Witness.Field.model_sub] using admitted)
  | montgomeryDouble => exact montgomeryDouble_equations i (by simpa only [Kind.Admitted,TornadoProofs.Witness.Field.model_mul,show TornadoProofs.Witness.Field.model 1=(1:Fr) from rfl, show TornadoProofs.Witness.Field.model 2=(2:Fr) from rfl, show TornadoProofs.Witness.Field.model 168696=(168696:Fr) from rfl] using admitted)
  | edwards2Montgomery => exact edwards2Montgomery_equations i (by simpa only [Kind.Admitted,TornadoProofs.Witness.Field.model_sub,show TornadoProofs.Witness.Field.model 1=(1:Fr) from rfl, show TornadoProofs.Witness.Field.model 2=(2:Fr) from rfl, show TornadoProofs.Witness.Field.model 168696=(168696:Fr) from rfl] using admitted.1) admitted.2
  | montgomery2Edwards => exact montgomery2Edwards_equations i admitted.1 (by simpa only [Kind.Admitted,TornadoProofs.Witness.Field.model_add,show TornadoProofs.Witness.Field.model 1=(1:Fr) from rfl, show TornadoProofs.Witness.Field.model 2=(2:Fr) from rfl, show TornadoProofs.Witness.Field.model 168696=(168696:Fr) from rfl] using admitted.2)
  | babyAdd =>
    exact babyAdd_equations i
      (by simpa only [Kind.Admitted,TornadoProofs.Witness.Field.model_add,TornadoProofs.Witness.Field.model_mul,show TornadoProofs.Witness.Field.model 1=(1:Fr) from rfl, show TornadoProofs.Witness.Field.model 2=(2:Fr) from rfl, show TornadoProofs.Witness.Field.model 168696=(168696:Fr) from rfl] using admitted.1)
      (by simpa only [Kind.Admitted,TornadoProofs.Witness.Field.model_sub,TornadoProofs.Witness.Field.model_mul,show TornadoProofs.Witness.Field.model 1=(1:Fr) from rfl, show TornadoProofs.Witness.Field.model 2=(2:Fr) from rfl, show TornadoProofs.Witness.Field.model 168696=(168696:Fr) from rfl] using admitted.2)
  | window4 => exact window4_equations i
  | square => exact square_equations i
  | multiMux3 => exact multiMux3_equations i

end TornadoProofs.Witness.Local
#print axioms TornadoProofs.Witness.Local.kindValues_equations
