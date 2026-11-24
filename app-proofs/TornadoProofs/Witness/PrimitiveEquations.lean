import TornadoProofs.Witness.PrimitiveValues

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Primitive
open Field

@[simp]
theorem model_invValue (x : Nat) : model (invValue x) = (model x)⁻¹ := by
  exact model_inverse_value x

def MontgomeryAddEquations (i o : Array Nat) : Prop :=
  model o[0]! * (model i[2]! - model i[0]!) = model i[3]! - model i[1]! ∧
  model o[0]! * model o[0]! = model o[1]! + 168698 + model i[0]! + model i[2]! ∧
  model o[0]! * (model i[0]! - model o[1]!) = model o[2]! + model i[1]!

def MontgomeryDoubleEquations (i o : Array Nat) : Prop :=
  model o[0]! = model i[0]! * model i[0]! ∧
  model o[1]! * (2 * model i[1]!) = 3 * model o[0]! + 337396 * model i[0]! + 1 ∧
  model o[1]! * model o[1]! = model o[2]! + 168698 + 2 * model i[0]! ∧
  model o[1]! * (model i[0]! - model o[2]!) = model o[3]! + model i[1]!

def Edwards2MontgomeryEquations (i o : Array Nat) : Prop :=
  model o[0]! * (1 - model i[1]!) = 1 + model i[1]! ∧
  model o[1]! * model i[0]! = model o[0]!

def Montgomery2EdwardsEquations (i o : Array Nat) : Prop :=
  model o[0]! * model i[1]! = model i[0]! ∧
  model o[1]! * (model i[0]! + 1) = model i[0]! - 1

def BabyAddEquations (i o : Array Nat) : Prop :=
  model o[0]! = model i[0]! * model i[3]! ∧
  model o[1]! = model i[1]! * model i[2]! ∧
  model o[2]! = (model i[1]! - 168700 * model i[0]!) * (model i[2]! + model i[3]!) ∧
  model o[3]! = model o[0]! * model o[1]! ∧
  model o[4]! * (1 + 168696 * model o[3]!) = model o[0]! + model o[1]! ∧
  model o[5]! * (1 - 168696 * model o[3]!) = model o[2]! + 168700 * model o[0]! - model o[1]!

def Window4Equations (i o : Array Nat) : Prop :=
  (2 * model i[0]!) * model i[1]! = model i[0]! - model o[0]!

def SquareEquations (i o : Array Nat) : Prop := model o[0]! = model i[0]! * model i[0]!

-- These independent field equations are the actual local circuit gates. The
-- only inverse premises concern mathematical denominators, not evaluator or
-- checker acceptance.
theorem montgomeryAdd_equations (i : Array Nat)
    (nonzero : model i[2]! - model i[0]! ≠ 0) :
    MontgomeryAddEquations i (montgomeryAdd i) := by
  simp only [MontgomeryAddEquations, montgomeryAdd]
  simp only [getElem!_def, List.getElem?_toArray, List.getElem?_cons_zero,
    List.getElem?_cons_succ] at *
  simp only [model_sub, model_mul, model_invValue]
  norm_num only [model_ofNat, Nat.cast_ofNat] at *
  repeat' constructor
  all_goals first | exact inv_mul_cancel_right₀ nonzero _ | ring

theorem montgomeryDouble_equations (i : Array Nat)
    (nonzero : (2 : Model) * model i[1]! ≠ 0) :
    MontgomeryDoubleEquations i (montgomeryDouble i) := by
  simp only [MontgomeryDoubleEquations, montgomeryDouble]
  simp only [getElem!_def, List.getElem?_toArray, List.getElem?_cons_zero,
    List.getElem?_cons_succ] at *
  simp only [model_sub, model_mul, model_add, model_invValue]
  norm_num only [model_ofNat, Nat.cast_ofNat] at *
  repeat' constructor
  all_goals first | exact inv_mul_cancel_right₀ nonzero _ | ring

theorem edwards2Montgomery_equations (i : Array Nat)
    (oneMinusY : (1 : Model) - model i[1]! ≠ 0) (x : model i[0]! ≠ 0) :
    Edwards2MontgomeryEquations i (edwards2Montgomery i) := by
  simp only [Edwards2MontgomeryEquations, edwards2Montgomery]
  simp only [getElem!_def, List.getElem?_toArray, List.getElem?_cons_zero,
    List.getElem?_cons_succ] at *
  simp only [model_sub, model_mul, model_add, model_invValue]
  norm_num only [model_ofNat, Nat.cast_ofNat] at *
  constructor <;> field_simp [oneMinusY, x]

theorem montgomery2Edwards_equations (i : Array Nat)
    (y : model i[1]! ≠ 0) (onePlusX : model i[0]! + 1 ≠ 0) :
    Montgomery2EdwardsEquations i (montgomery2Edwards i) := by
  simp only [Montgomery2EdwardsEquations, montgomery2Edwards]
  simp only [getElem!_def, List.getElem?_toArray, List.getElem?_cons_zero,
    List.getElem?_cons_succ] at *
  simp only [model_sub, model_mul, model_add, model_invValue]
  norm_num only [model_ofNat, Nat.cast_ofNat] at *
  constructor <;> field_simp [y, onePlusX]

theorem babyAdd_equations (i : Array Nat)
    (plus : (1 : Model) + 168696 * ((model i[0]! * model i[3]!) *
      (model i[1]! * model i[2]!)) ≠ 0)
    (minus : (1 : Model) - 168696 * ((model i[0]! * model i[3]!) *
      (model i[1]! * model i[2]!)) ≠ 0) :
    BabyAddEquations i (babyAdd i) := by
  simp only [BabyAddEquations, babyAdd]
  simp only [getElem!_def, List.getElem?_toArray, List.getElem?_cons_zero,
    List.getElem?_cons_succ] at *
  simp only [model_sub, model_mul, model_add, model_invValue]
  norm_num only [model_ofNat, Nat.cast_ofNat] at *
  repeat' constructor
  all_goals first | exact inv_mul_cancel_right₀ plus _ | exact inv_mul_cancel_right₀ minus _

theorem window4_equations (i : Array Nat) : Window4Equations i (window4 i) := by
  simp only [Window4Equations, window4]
  simp only [getElem!_def, List.getElem?_toArray, List.getElem?_cons_zero] at *
  simp only [model_sub, model_mul]
  norm_num only [model_ofNat, Nat.cast_ofNat] at *
  ring

theorem square_equations (i : Array Nat) : SquareEquations i (square i) := by
  simp only [SquareEquations, square]
  simp only [getElem!_def, List.getElem?_toArray, List.getElem?_cons_zero] at *
  simp only [model_mul]

end TornadoProofs.Witness.Primitive
#print axioms TornadoProofs.Witness.Primitive.model_invValue
#print axioms TornadoProofs.Witness.Primitive.montgomeryAdd_equations
#print axioms TornadoProofs.Witness.Primitive.montgomeryDouble_equations
#print axioms TornadoProofs.Witness.Primitive.edwards2Montgomery_equations
#print axioms TornadoProofs.Witness.Primitive.montgomery2Edwards_equations
#print axioms TornadoProofs.Witness.Primitive.babyAdd_equations
#print axioms TornadoProofs.Witness.Primitive.window4_equations
#print axioms TornadoProofs.Witness.Primitive.square_equations
