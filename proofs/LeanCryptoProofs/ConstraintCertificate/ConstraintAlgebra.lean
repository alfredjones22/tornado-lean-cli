import LeanCryptoProofs.ConstraintCertificate.ConstraintCertificateModel
set_option autoImplicit false

namespace LeanCrypto.Proofs.ConstraintCertificate

open LeanCrypto.Groth16.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr

abbrev Fr := ZMod Q

def linearValue (assignment : Nat → Fr) (row : Linear) : Fr := evalSparse assignment row
def quadraticValue (assignment : Nat → Fr) (row : Quadratic) : Fr :=
  evalSparse (fun term => assignment term.1 * assignment term.2) row
def Satisfies (assignment : Nat → Fr) (equation : Equation) : Prop :=
  linearValue assignment equation.a * linearValue assignment equation.b = linearValue assignment equation.c

theorem linear_normalize (assignment : Nat → Fr) (row : Linear) :
    linearValue assignment (normalizeLinear row) = linearValue assignment row :=
  eval_normalizeSparse assignment _ row

theorem linear_add (assignment : Nat → Fr) (left right : Linear) :
    linearValue assignment (addLinear left right) = linearValue assignment left + linearValue assignment right := by
  rw [addLinear, linear_normalize]
  exact eval_append assignment left right

theorem linear_scale (assignment : Nat → Fr) (scalar : Nat) (row : Linear) :
    linearValue assignment (scaleLinear scalar row) = model scalar * linearValue assignment row := by
  rw [scaleLinear, linear_normalize]
  exact eval_scale assignment scalar row

theorem evalSparse_sum {Key : Type} (weight : Key → Fr) (row : List (Key × Nat)) :
    evalSparse weight row = (row.map (fun term => model term.2 * weight term.1)).sum := by
  induction row with
  | nil => rfl
  | cons term rest ih => simp only [evalSparse, List.map_cons, List.sum_cons, ih]

theorem evalSparse_perm {Key : Type} (weight : Key → Fr) (left right : List (Key × Nat))
    (permutation : left.Perm right) : evalSparse weight left = evalSparse weight right := by
  rw [evalSparse_sum, evalSparse_sum]
  exact (permutation.map (fun term => model term.2 * weight term.1)).sum_eq

theorem quadratic_normalize (assignment : Nat → Fr) (row : Quadratic) :
    quadraticValue assignment (normalizeQuadratic row) = quadraticValue assignment row := by
  unfold quadraticValue normalizeQuadratic
  rw [evalSparse_perm _ _ _ (List.reverse_perm _), eval_normalizeSparse]
  apply evalSparse_perm
  exact List.mergeSort_perm _ _

theorem quadratic_scale (assignment : Nat → Fr) (scalar : Nat) (row : Quadratic) :
    quadraticValue assignment (scaleQuadratic scalar row) = model scalar * quadraticValue assignment row := by
  rw [scaleQuadratic, quadratic_normalize]
  exact eval_scale _ scalar row

theorem orderedPair_value (assignment : Nat → Fr) (first second : Nat) :
    assignment (orderedPair first second).1 * assignment (orderedPair first second).2 =
      assignment first * assignment second := by
  unfold orderedPair
  split
  · rfl
  · exact mul_comm _ _

theorem product_row (assignment : Nat → Fr) (first coefficient : Nat) (row : Linear) :
    quadraticValue assignment (row.map fun (second, value) => (orderedPair first second, coefficient * value % modulus)) =
      (model coefficient * assignment first) * linearValue assignment row := by
  induction row with
  | nil => simp [quadraticValue, linearValue, evalSparse]
  | cons term rest ih =>
    obtain ⟨second, value⟩ := term
    change model (coefficient * value % modulus) *
      (assignment (orderedPair first second).1 * assignment (orderedPair first second).2) +
      quadraticValue assignment (rest.map fun (second, value) =>
        (orderedPair first second, coefficient * value % modulus)) = _
    rw [coefficient_mod, orderedPair_value]
    rw [show model (coefficient * value) = model coefficient * model value by simp [model]]
    change _ + quadraticValue assignment _ = _
    rw [ih]
    simp only [linearValue, evalSparse]
    ring

theorem product_rows (assignment : Nat → Fr) (left right : Linear) :
    quadraticValue assignment (left.flatMap fun (first, coefficient) =>
      right.map fun (second, value) => (orderedPair first second, coefficient * value % modulus)) =
      linearValue assignment left * linearValue assignment right := by
  induction left with
  | nil => simp [quadraticValue, linearValue, evalSparse]
  | cons term rest ih =>
    obtain ⟨first, coefficient⟩ := term
    simp only [List.flatMap_cons]
    have head := product_row assignment first coefficient right
    unfold quadraticValue at *
    rw [eval_append, head, ih]
    simp only [linearValue, evalSparse]
    ring

theorem coefficient_negate (coefficient : Nat) :
    model ((modulus - coefficient % modulus) % modulus) = -model coefficient := by
  rw [coefficient_mod]
  change ((Q - coefficient % Q : Nat) : ZMod Q) = -(coefficient : ZMod Q)
  rw [Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ (by decide))), ZMod.natCast_self, ZMod.natCast_mod]
  exact zero_sub _

theorem negative_row (assignment : Nat → Fr) (constant : assignment 0 = 1) (row : Linear) :
    quadraticValue assignment (row.map fun (index, coefficient) =>
      ((0, index), (modulus - coefficient % modulus) % modulus)) = -linearValue assignment row := by
  induction row with
  | nil => simp [quadraticValue, linearValue, evalSparse]
  | cons term rest ih =>
    obtain ⟨index, coefficient⟩ := term
    simp only [List.map_cons, quadraticValue, evalSparse, coefficient_negate, constant, one_mul] at *
    rw [ih]
    simp only [linearValue, evalSparse]
    ring

theorem equationPolynomial_value (assignment : Nat → Fr) (constant : assignment 0 = 1) (equation : Equation) :
    quadraticValue assignment (equationPolynomial equation) =
      linearValue assignment equation.a * linearValue assignment equation.b - linearValue assignment equation.c := by
  rw [equationPolynomial, quadratic_normalize]
  unfold quadraticValue
  rw [eval_append]
  change quadraticValue assignment _ + quadraticValue assignment _ = _
  rw [product_rows, negative_row assignment constant]
  exact sub_eq_add_neg _ _ |>.symm

theorem satisfies_iff_polynomial_zero (assignment : Nat → Fr) (constant : assignment 0 = 1) (equation : Equation) :
    Satisfies assignment equation ↔ quadraticValue assignment (equationPolynomial equation) = 0 := by
  rw [equationPolynomial_value assignment constant]
  exact sub_eq_zero.symm

end LeanCrypto.Proofs.ConstraintCertificate

#print axioms LeanCrypto.Proofs.ConstraintCertificate.linear_normalize
#print axioms LeanCrypto.Proofs.ConstraintCertificate.linear_add
#print axioms LeanCrypto.Proofs.ConstraintCertificate.linear_scale
#print axioms LeanCrypto.Proofs.ConstraintCertificate.evalSparse_sum
#print axioms LeanCrypto.Proofs.ConstraintCertificate.evalSparse_perm
#print axioms LeanCrypto.Proofs.ConstraintCertificate.quadratic_normalize
#print axioms LeanCrypto.Proofs.ConstraintCertificate.quadratic_scale
#print axioms LeanCrypto.Proofs.ConstraintCertificate.orderedPair_value
#print axioms LeanCrypto.Proofs.ConstraintCertificate.product_row
#print axioms LeanCrypto.Proofs.ConstraintCertificate.product_rows
#print axioms LeanCrypto.Proofs.ConstraintCertificate.coefficient_negate
#print axioms LeanCrypto.Proofs.ConstraintCertificate.negative_row
#print axioms LeanCrypto.Proofs.ConstraintCertificate.equationPolynomial_value
#print axioms LeanCrypto.Proofs.ConstraintCertificate.satisfies_iff_polynomial_zero
