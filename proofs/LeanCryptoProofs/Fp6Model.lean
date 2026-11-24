import LeanCryptoProofs.Fp2Exponent
import LeanCrypto.BN254.PairingField
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Fp6
open LeanCrypto.BN254.G2 LeanCrypto.BN254.PairingField
open Polynomial

abbrev Base := BN254Fp2.Field
def xi : Base := BN254Fp2.model nonresidue
def cubic : Polynomial Base := X ^ 3 - C xi

theorem cubic_monic : cubic.Monic := monic_X_pow_sub_C xi (by decide)
theorem cubic_degree : cubic.natDegree = 3 := natDegree_X_pow_sub_C

theorem cubic_irreducible : Irreducible cubic := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [cubic_degree]
    decide
  · intro value root
    apply BN254Fp2.nonresidue_not_cube value
    apply sub_eq_zero.mp
    simpa [IsRoot, cubic, xi, nonresidue] using root

instance cubicIrreducible : Fact (Irreducible cubic) := ⟨cubic_irreducible⟩
abbrev Field := AdjoinRoot cubic
noncomputable def basis : Module.Basis (Fin 3) Base Field :=
  (AdjoinRoot.powerBasis' cubic_monic).basis.reindex (finCongr cubic_degree)

@[simp]
theorem basis_zero : basis 0 = 1 := by
  simp only [basis, Module.Basis.reindex_apply]
  rw [(AdjoinRoot.powerBasis' cubic_monic).basis_eq_pow]
  rfl
@[simp]
theorem basis_one : basis 1 = AdjoinRoot.root cubic := by
  simp only [basis, Module.Basis.reindex_apply]
  rw [(AdjoinRoot.powerBasis' cubic_monic).basis_eq_pow]
  rw [AdjoinRoot.powerBasis'_gen]
  change AdjoinRoot.root cubic ^ 1 = AdjoinRoot.root cubic
  exact pow_one _
@[simp]
theorem basis_two : basis 2 = AdjoinRoot.root cubic ^ 2 := by
  simp only [basis, Module.Basis.reindex_apply]
  rw [(AdjoinRoot.powerBasis' cubic_monic).basis_eq_pow]
  rfl

noncomputable def model (value : Fp6) : Field :=
  basis.equivFun.symm (fun index =>
    if index = 0 then BN254Fp2.model value.c0
    else if index = 1 then BN254Fp2.model value.c1
    else BN254Fp2.model value.c2)

noncomputable def encode (value : Field) : Fp6 :=
  ⟨BN254Fp2.encode (basis.equivFun value 0),
   BN254Fp2.encode (basis.equivFun value 1),
   BN254Fp2.encode (basis.equivFun value 2)⟩

theorem model_formula (value : Fp6) :
    model value = algebraMap Base Field (BN254Fp2.model value.c0) +
      algebraMap Base Field (BN254Fp2.model value.c1) * AdjoinRoot.root cubic +
      algebraMap Base Field (BN254Fp2.model value.c2) * AdjoinRoot.root cubic ^ 2 := by
  rw [model, Module.Basis.equivFun_symm_apply, Fin.sum_univ_three]
  simp [Algebra.smul_def]

theorem native_ext {left right : Fp6}
    (zero : left.c0 = right.c0) (one : left.c1 = right.c1) (two : left.c2 = right.c2) :
    left = right := by cases left; cases right; cases zero; cases one; cases two; rfl

@[simp]
theorem encode_model (value : Fp6) : encode (model value) = value := by
  apply native_ext <;> simp only [encode, model, LinearEquiv.apply_symm_apply] <;> simp

@[simp]
theorem model_encode (value : Field) : model (encode value) = value := by
  apply basis.equivFun.injective
  rw [model, LinearEquiv.apply_symm_apply]
  funext index
  fin_cases index <;> simp only [encode, BN254Fp2.model_encode] <;> rfl

theorem model_injective : Function.Injective model := by
  intro left right equal
  rw [← encode_model left, equal, encode_model]

theorem root_cube : AdjoinRoot.root cubic ^ 3 = algebraMap Base Field xi := by
  have root := AdjoinRoot.eval₂_root cubic
  change eval₂ (AdjoinRoot.of cubic) (AdjoinRoot.root cubic) (X ^ 3 - C xi) = 0 at root
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at root
  exact sub_eq_zero.mp root

@[simp]
theorem model_zero : model Fp6.zero = 0 := by simp [model_formula, Fp6.zero]
@[simp]
theorem model_one : model Fp6.one = 1 := by simp [model_formula, Fp6.one]
@[simp]
theorem model_v : model Fp6.v = AdjoinRoot.root cubic := by
  simp [model_formula, Fp6.v]

@[simp]
theorem model_add (left right : Fp6) : model (left.add right) = model left + model right := by
  simp [model_formula, Fp6.add]
  ring

@[simp]
theorem model_neg (value : Fp6) : model value.neg = -model value := by
  simp [model_formula, Fp6.neg]
  ring

@[simp]
theorem model_sub (left right : Fp6) : model (left.sub right) = model left - model right := by
  simp [Fp6.sub, sub_eq_add_neg]

@[simp]
theorem model_mulByV (value : Fp6) : model value.mulByV = model value * model Fp6.v := by
  simp only [model_formula, Fp6.mulByV, Fp6.v, BN254Fp2.model_zero, BN254Fp2.model_one,
    BN254Fp2.model_mul, map_mul, map_zero, map_one, zero_mul, one_mul, add_zero, zero_add]
  calc
    _ = algebraMap Base Field (BN254Fp2.model value.c0) * AdjoinRoot.root cubic +
        algebraMap Base Field (BN254Fp2.model value.c1) * AdjoinRoot.root cubic ^ 2 +
        algebraMap Base Field (BN254Fp2.model value.c2) * (algebraMap Base Field xi) := by unfold xi; ring
    _ = _ := by rw [← root_cube]; ring

@[simp]
theorem model_mul (left right : Fp6) : model (left.mul right) = model left * model right := by
  simp only [model_formula, Fp6.mul, BN254Fp2.model_add, BN254Fp2.model_mul, map_add, map_mul]
  have fourth : AdjoinRoot.root cubic ^ 4 = algebraMap Base Field xi * AdjoinRoot.root cubic := by
    rw [show (4 : Nat) = 3 + 1 from rfl, pow_add, root_cube, pow_one]
  have xiEq : BN254Fp2.model nonresidue = xi := rfl
  rw [xiEq]
  ring_nf
  rw [fourth, root_cube]
  ring

theorem model_beq (left right : Fp6) : (left == right) = true ↔ model left = model right := by
  change ((left.c0 == right.c0) && (left.c1 == right.c1) && (left.c2 == right.c2)) = true ↔ _
  simp only [Bool.and_eq_true, BN254Fp2.model_beq]
  constructor
  · rintro ⟨⟨zero, one⟩, two⟩
    have equal := native_ext (BN254Fp2.model_injective zero)
      (BN254Fp2.model_injective one) (BN254Fp2.model_injective two)
    rw [equal]
  · intro equal
    have native := model_injective equal
    cases native
    exact ⟨⟨rfl, rfl⟩, rfl⟩

end LeanCrypto.Proofs.BN254Fp6

#print axioms LeanCrypto.Proofs.BN254Fp6.cubic_monic
#print axioms LeanCrypto.Proofs.BN254Fp6.cubic_degree
#print axioms LeanCrypto.Proofs.BN254Fp6.cubic_irreducible
#print axioms LeanCrypto.Proofs.BN254Fp6.basis_zero
#print axioms LeanCrypto.Proofs.BN254Fp6.basis_one
#print axioms LeanCrypto.Proofs.BN254Fp6.basis_two
#print axioms LeanCrypto.Proofs.BN254Fp6.model_formula
#print axioms LeanCrypto.Proofs.BN254Fp6.native_ext
#print axioms LeanCrypto.Proofs.BN254Fp6.encode_model
#print axioms LeanCrypto.Proofs.BN254Fp6.model_encode
#print axioms LeanCrypto.Proofs.BN254Fp6.model_injective
#print axioms LeanCrypto.Proofs.BN254Fp6.root_cube
#print axioms LeanCrypto.Proofs.BN254Fp6.model_zero
#print axioms LeanCrypto.Proofs.BN254Fp6.model_one
#print axioms LeanCrypto.Proofs.BN254Fp6.model_v
#print axioms LeanCrypto.Proofs.BN254Fp6.model_add
#print axioms LeanCrypto.Proofs.BN254Fp6.model_neg
#print axioms LeanCrypto.Proofs.BN254Fp6.model_sub
#print axioms LeanCrypto.Proofs.BN254Fp6.model_mulByV
#print axioms LeanCrypto.Proofs.BN254Fp6.model_mul
#print axioms LeanCrypto.Proofs.BN254Fp6.model_beq
