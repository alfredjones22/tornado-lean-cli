import LeanCrypto.Groth16.ConstraintCertificate
import LeanCryptoProofs.R1CSModel

set_option autoImplicit false

namespace LeanCrypto.Proofs.ConstraintCertificate

open LeanCrypto.Groth16.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr

variable {Key : Type} [DecidableEq Key]

def evalSparse (weight : Key → ZMod Q) : List (Key × Nat) → ZMod Q
  | [] => 0
  | (key, coefficient) :: rest => model coefficient * weight key + evalSparse weight rest

theorem coefficient_mod (coefficient : Nat) :
    model (coefficient % modulus) = model coefficient := model_mod coefficient

theorem coefficient_zero (coefficient : Nat) (zero : coefficient % modulus = 0) :
    model coefficient = 0 := by
  rw [← coefficient_mod coefficient, zero]
  rfl

theorem eval_insertSparse (weight : Key → ZMod Q) (less : Key → Key → Bool)
    (key : Key) (coefficient : Nat) (row : List (Key × Nat)) :
    evalSparse weight (insertSparse less key coefficient row) =
      model coefficient * weight key + evalSparse weight row := by
  induction row with
  | nil =>
    rw [insertSparse]
    split
    · rename_i zero
      simp only [evalSparse, coefficient_zero coefficient zero, zero_mul, zero_add]
    · simp only [evalSparse, coefficient_mod]
  | cons term rest ih =>
    obtain ⟨other, value⟩ := term
    rw [insertSparse]
    by_cases zero : coefficient % modulus = 0
    · simp only [zero, ↓reduceIte, evalSparse, coefficient_zero coefficient zero, zero_mul, zero_add]
    · simp only [zero, ↓reduceIte]
      by_cases same : key = other
      · subst other
        simp only [↓reduceIte]
        by_cases totalZero : (coefficient + value) % modulus = 0
        · simp only [totalZero, ↓reduceIte, evalSparse]
          have total : model coefficient + model value = 0 := by
            change ((coefficient : ZMod Q) + value) = 0
            rw [← Nat.cast_add]
            exact coefficient_zero (coefficient + value) totalZero
          calc
            _ = (model coefficient + model value) * weight key + evalSparse weight rest := by rw [total]; simp
            _ = _ := by ring
        · simp only [totalZero, ↓reduceIte, evalSparse]
          rw [coefficient_mod]
          simp only [model, Nat.cast_add]
          ring
      · simp only [same, ↓reduceIte]
        split
        · simp only [evalSparse, coefficient_mod]
        · simp only [evalSparse, ih]
          ring

theorem eval_fold (weight : Key → ZMod Q) (less : Key → Key → Bool)
    (row accumulator : List (Key × Nat)) :
    evalSparse weight (row.foldl (fun current term => insertSparse less term.1 term.2 current) accumulator) =
      evalSparse weight row + evalSparse weight accumulator := by
  induction row generalizing accumulator with
  | nil => simp [evalSparse]
  | cons term rest ih =>
    simp only [List.foldl_cons, ih, eval_insertSparse, evalSparse]
    ring

theorem eval_normalizeSparse (weight : Key → ZMod Q) (less : Key → Key → Bool)
    (row : List (Key × Nat)) :
    evalSparse weight (normalizeSparse less row) = evalSparse weight row := by
  rw [normalizeSparse, eval_fold]
  simp [evalSparse]

omit [DecidableEq Key] in
theorem eval_append (weight : Key → ZMod Q) (left right : List (Key × Nat)) :
    evalSparse weight (left ++ right) = evalSparse weight left + evalSparse weight right := by
  induction left with
  | nil => simp [evalSparse]
  | cons term rest ih => simp only [List.cons_append, evalSparse, ih]; ring

omit [DecidableEq Key] in
theorem eval_scale (weight : Key → ZMod Q) (scale : Nat) (row : List (Key × Nat)) :
    evalSparse weight (row.map fun (key, coefficient) => (key, scale * coefficient % modulus)) =
      model scale * evalSparse weight row := by
  induction row with
  | nil => simp [evalSparse]
  | cons term rest ih =>
    obtain ⟨key, coefficient⟩ := term
    simp only [List.map_cons, evalSparse, ih]
    rw [coefficient_mod]
    simp only [model, Nat.cast_mul]
    ring

end LeanCrypto.Proofs.ConstraintCertificate

#print axioms LeanCrypto.Proofs.ConstraintCertificate.coefficient_mod
#print axioms LeanCrypto.Proofs.ConstraintCertificate.coefficient_zero
#print axioms LeanCrypto.Proofs.ConstraintCertificate.eval_insertSparse
#print axioms LeanCrypto.Proofs.ConstraintCertificate.eval_fold
#print axioms LeanCrypto.Proofs.ConstraintCertificate.eval_normalizeSparse
#print axioms LeanCrypto.Proofs.ConstraintCertificate.eval_append
#print axioms LeanCrypto.Proofs.ConstraintCertificate.eval_scale
