import Tornado.Protocol.WitnessLocalConstraints
import TornadoProofs.Witness.SymbolicBounds
import LeanCryptoProofs.ConstraintCertificate.CertificateTargets

set_option autoImplicit false
namespace TornadoProofs.Witness.Local
open Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate
open LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr

def SystemSatisfied (assignment : Nat → Fr) (system : LocalSystem) : Prop :=
  RowsZero assignment system.linears ∧ EquationsSatisfied assignment system.nonlinear

theorem atomLinear_value (assignment : Nat → Fr) (index : Nat) :
    linearValue assignment (atomLinear index) = assignment index := by
  simp [atomLinear, linearValue, evalSparse, model]

theorem constantLinear_value (assignment : Nat → Fr) (constant : assignment 0 = 1) (value : Nat) :
    linearValue assignment (constantLinear value) = model value := by
  rw [constantLinear, linear_normalize]
  simp [linearValue, evalSparse, constant]

theorem negative_one : model (modulus-1) = (-1 : Fr) := by
  have equation := coefficient_negate 1
  simpa only [show 1%modulus=1 from by decide,
    show (modulus-1)%modulus=modulus-1 from by decide,
    show model 1=(1:Fr) from by simp [model]] using equation

theorem negLinear_value (assignment : Nat → Fr) (row : Linear) :
    linearValue assignment (negLinear row) = -linearValue assignment row := by
  rw [negLinear, linear_scale, negative_one]
  ring

theorem minusLinear_value (assignment : Nat → Fr) (left right : Linear) :
    linearValue assignment (minusLinear left right) =
      linearValue assignment left-linearValue assignment right := by
  rw [minusLinear, linear_add, negLinear_value]
  ring

theorem asConstant_value (assignment : Nat → Fr) (constant : assignment 0=1)
    (row : Linear) (value : Nat) (found : asConstant row = some value) :
    linearValue assignment row = model value := by
  cases row with
  | nil =>
    simp only [asConstant, Option.some.injEq] at found
    subst value
    simp [linearValue, evalSparse, model]
  | cons term rest =>
    obtain ⟨index,coefficient⟩ := term
    cases index with
    | zero =>
      cases rest with
      | nil =>
        simp only [asConstant, Option.some.injEq] at found
        subst value
        simp [linearValue, evalSparse, constant]
      | cons head tail => simp [asConstant] at found
    | succ index => simp [asConstant] at found

theorem linear_emit (assignment : Nat → Fr) (system : LocalSystem) (row : Linear)
    (valid : SystemSatisfied assignment system) (equation : linearValue assignment row=0) :
    SystemSatisfied assignment (system.linear row) := by
  unfold LocalSystem.linear
  dsimp only
  split
  · exact valid
  · exact ⟨rowsZero_push assignment system.linears _ valid.1
      (by rw [linear_normalize]; exact equation),valid.2⟩

theorem equality_emit (assignment : Nat → Fr) (system : LocalSystem) (output : Nat)
    (expression : Linear) (valid : SystemSatisfied assignment system)
    (equation : assignment output=linearValue assignment expression) :
    SystemSatisfied assignment (system.equality output expression) := by
  apply linear_emit assignment system _ valid
  rw [minusLinear_value, atomLinear_value, equation, sub_self]

theorem constraint_emit (assignment : Nat → Fr) (constant : assignment 0=1)
    (system : LocalSystem) (a b c : Linear) (valid : SystemSatisfied assignment system)
    (equation : linearValue assignment a*linearValue assignment b=linearValue assignment c) :
    SystemSatisfied assignment (system.constraint a b c) := by
  cases first : asConstant a with
  | some value =>
    simp only [LocalSystem.constraint, first]
    apply linear_emit assignment system _ valid
    rw [minusLinear_value,linear_scale]
    rw [asConstant_value assignment constant a value first] at equation
    exact sub_eq_zero.mpr equation
  | none =>
    cases second : asConstant b with
    | some value =>
      simp only [LocalSystem.constraint,first,second]
      apply linear_emit assignment system _ valid
      rw [minusLinear_value,linear_scale]
      rw [asConstant_value assignment constant b value second] at equation
      exact sub_eq_zero.mpr (by simpa only [mul_comm] using equation)
    | none =>
      simp only [LocalSystem.constraint,first,second]
      refine ⟨valid.1,?_⟩
      intro row member
      rw [Array.mem_push] at member
      rcases member with previous | equal
      · exact valid.2 row previous
      · subst row
        exact equation

theorem product_emit (assignment : Nat → Fr) (constant : assignment 0=1)
    (system : LocalSystem) (output : Nat) (a b : Linear)
    (valid : SystemSatisfied assignment system)
    (equation : linearValue assignment a*linearValue assignment b=assignment output) :
    SystemSatisfied assignment (system.product output a b) := by
  apply constraint_emit assignment constant system _ _ _ valid
  simpa only [atomLinear_value] using equation

end TornadoProofs.Witness.Local
#print axioms TornadoProofs.Witness.Local.atomLinear_value
#print axioms TornadoProofs.Witness.Local.constantLinear_value
#print axioms TornadoProofs.Witness.Local.negative_one
#print axioms TornadoProofs.Witness.Local.negLinear_value
#print axioms TornadoProofs.Witness.Local.minusLinear_value
#print axioms TornadoProofs.Witness.Local.asConstant_value
#print axioms TornadoProofs.Witness.Local.linear_emit
#print axioms TornadoProofs.Witness.Local.equality_emit
#print axioms TornadoProofs.Witness.Local.constraint_emit
#print axioms TornadoProofs.Witness.Local.product_emit
