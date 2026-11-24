import LeanCryptoProofs.BabyJubjub.ExtendedAddition
import LeanCryptoProofs.BabyJubjub.NativeAffine

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjub

theorem scalarLoop_admissible (base accumulator : RawPoint) (scalar : Nat)
    (baseAdmitted : Admissible base) (accumulatorAdmitted : Admissible accumulator) :
    Admissible (nativeScalarLoop base scalar accumulator) := by
  induction scalar using Nat.strong_induction_on generalizing base accumulator with
  | h scalar ih =>
    unfold nativeScalarLoop
    rw [(pedersenFieldPrivate LeanCrypto.scalarMulLoop.eq_def) base scalar accumulator]
    split
    · exact accumulatorAdmitted
    · rename_i nonzero
      have nextBase := add_admissible base base baseAdmitted baseAdmitted
      have nextAccumulator : Admissible (if scalar%2==1 then nativeAddPoints accumulator base else accumulator) := by
        split
        · exact add_admissible accumulator base accumulatorAdmitted baseAdmitted
        · exact accumulatorAdmitted
      exact ih (scalar/2) (Nat.div_lt_self (Nat.pos_of_ne_zero nonzero) (by decide))
        _ _ nextBase nextAccumulator

theorem scalarMul_admissible (point : RawPoint) (scalar : Nat) (admitted : Admissible point) :
    Admissible (nativeScalarMul point scalar) :=
  scalarLoop_admissible point nativeIdentity scalar admitted identity_admissible

theorem scalarMul_affine_construct (point : RawPoint) (scalar : Nat) (admitted : Admissible point) :
    nativeAffine (nativeScalarMul point scalar)=some
      ((normalizedX (nativeScalarMul point scalar)).val,(normalizedY (nativeScalarMul point scalar)).val) :=
  native_affine_construct _ (scalarMul_admissible point scalar admitted)

theorem scalarMul_zero (point : RawPoint) : nativeScalarMul point 0=nativeIdentity := by
  change nativeScalarLoop point 0 nativeIdentity=nativeIdentity
  unfold nativeScalarLoop
  rw [(pedersenFieldPrivate LeanCrypto.scalarMulLoop.eq_def) point 0 nativeIdentity]
  rfl

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.scalarLoop_admissible
#print axioms LeanCrypto.Proofs.BabyJubjub.scalarMul_admissible
#print axioms LeanCrypto.Proofs.BabyJubjub.scalarMul_affine_construct
#print axioms LeanCrypto.Proofs.BabyJubjub.scalarMul_zero
