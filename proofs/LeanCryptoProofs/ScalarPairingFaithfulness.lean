import LeanCryptoProofs.ScalarPairing

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open Groth16Assembly
local instance : NeZero LeanCrypto.BN254.G1.scalarPrime := ⟨by decide⟩
local instance : Fact LeanCrypto.BN254.G1.scalarPrime.Prime := ⟨Primes.bn254_scalar_prime⟩

def scalarTargetHom : Fr →+ Additive BN254Fp12.Fieldˣ where
  toFun value := scalarPairHom value 1
  map_zero' := by rw [map_zero]; rfl
  map_add' first second := by rw [map_add, AddMonoidHom.add_apply]

theorem scalarTargetHom_value (value : Fr) :
    scalarTargetHom value = value.val • scalarTargetHom 1 := by
  have equation : value = value.val • (1 : Fr) := by simp [nsmul_eq_mul]
  exact (congrArg scalarTargetHom equation).trans (scalarTargetHom.map_nsmul 1 value.val)

theorem scalarTargetHom_q_torsion : LeanCrypto.BN254.G1.scalarPrime • scalarTargetHom 1 = 0 := by
  rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]

theorem scalarTargetHom_exact_order (nonzero : scalarTargetHom 1 ≠ 0) :
    addOrderOf (scalarTargetHom 1) = LeanCrypto.BN254.G1.scalarPrime :=
  addOrderOf_eq_prime scalarTargetHom_q_torsion nonzero

theorem scalarTargetHom_injective (nonzero : scalarTargetHom 1 ≠ 0) : Function.Injective scalarTargetHom := by
  intro first second equal
  rw [scalarTargetHom_value first, scalarTargetHom_value second] at equal
  have residues := nsmul_inj_mod.mp equal
  rw [scalarTargetHom_exact_order nonzero, Nat.mod_eq_of_lt first.val_lt,
    Nat.mod_eq_of_lt second.val_lt] at residues
  exact ZMod.val_injective _ residues

theorem scalarTarget_model_one_iff (nonzero : scalarTargetHom 1 ≠ 0) (value : Fr) :
    ((scalarTargetHom value).toMul : BN254Fp12.Field) = 1 ↔ value = 0 := by
  constructor
  · intro one
    have zero : scalarTargetHom value = scalarTargetHom 0 := by
      rw [map_zero]
      apply Units.val_injective
      exact one
    exact scalarTargetHom_injective nonzero zero
  · intro zero
    rw [zero, map_zero]
    rfl

theorem scalar_pair_product_equation_iff (nonzero : scalarTargetHom 1 ≠ 0)
    (a b c alpha beta gamma delta publicIC : Fr) :
    ((scalarPairHom (-a) b + scalarPairHom alpha beta + scalarPairHom publicIC gamma +
      scalarPairHom c delta).toMul : BN254Fp12.Field) = 1 ↔
      a * b = alpha * beta + publicIC * gamma + c * delta := by
  have collected : scalarPairHom (-a) b + scalarPairHom alpha beta + scalarPairHom publicIC gamma +
      scalarPairHom c delta = scalarTargetHom (-a * b + alpha * beta + publicIC * gamma + c * delta) := by
    rw [scalarPair_product (-a) b, scalarPair_product alpha beta, scalarPair_product publicIC gamma,
      scalarPair_product c delta]
    simp only [scalarTargetHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_add]
  rw [collected, scalarTarget_model_one_iff nonzero]
  constructor <;> intro equation
  · linear_combination -equation
  · linear_combination -equation

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.scalarTargetHom_value
#print axioms LeanCrypto.Proofs.BN254Tate.scalarTargetHom_q_torsion
#print axioms LeanCrypto.Proofs.BN254Tate.scalarTargetHom_exact_order
#print axioms LeanCrypto.Proofs.BN254Tate.scalarTargetHom_injective
#print axioms LeanCrypto.Proofs.BN254Tate.scalarTarget_model_one_iff
#print axioms LeanCrypto.Proofs.BN254Tate.scalar_pair_product_equation_iff
