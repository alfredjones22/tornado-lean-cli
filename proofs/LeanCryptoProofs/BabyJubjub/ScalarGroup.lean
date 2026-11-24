import LeanCryptoProofs.BabyJubjub.GroupLaw

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjub

/-- Universal invariant of the actual total unreduced native binary loop. -/
theorem scalarLoop_groupPoint (base accumulator : RawPoint) (scalar : Nat)
    (baseAdmitted : Admissible base) (accumulatorAdmitted : Admissible accumulator) :
    groupPoint (nativeScalarLoop base scalar accumulator)=
      groupPoint accumulator+scalar • groupPoint base := by
  induction scalar using Nat.strong_induction_on generalizing base accumulator with
  | h scalar ih =>
    unfold nativeScalarLoop
    rw [(pedersenFieldPrivate LeanCrypto.scalarMulLoop.eq_def) base scalar accumulator]
    split
    · rename_i zero
      simp only [zero,zero_nsmul,add_zero]
    · rename_i nonzero
      have smaller : scalar/2<scalar := Nat.div_lt_self (Nat.pos_of_ne_zero nonzero) (by decide)
      have nextBase := add_admissible base base baseAdmitted baseAdmitted
      by_cases odd : scalar%2=1
      · simp only [beq_iff_eq,odd,↓reduceIte]
        rw [ih (scalar/2) smaller _ _ nextBase (add_admissible accumulator base accumulatorAdmitted baseAdmitted),
          add_groupPoint accumulator base accumulatorAdmitted baseAdmitted,
          add_groupPoint base base baseAdmitted baseAdmitted]
        have exponent : scalar/2+scalar/2+1=scalar := by
          have division := Nat.mod_add_div scalar 2
          omega
        calc
          groupPoint accumulator+groupPoint base+(scalar/2) • (groupPoint base+groupPoint base)=
              groupPoint accumulator+(scalar/2+scalar/2+1) • groupPoint base := by
            simp only [nsmul_add,add_nsmul,one_nsmul]
            ac_rfl
          _=_ := by rw [exponent]
      · simp only [beq_iff_eq,odd,↓reduceIte]
        rw [ih (scalar/2) smaller _ _ nextBase accumulatorAdmitted,
          add_groupPoint base base baseAdmitted baseAdmitted,nsmul_add,←add_nsmul]
        have exponent : scalar/2+scalar/2=scalar := by
          have bound := Nat.mod_lt scalar (by decide : 0<2)
          have division := Nat.mod_add_div scalar 2
          omega
        rw [exponent]

/-- Every Nat scalar is interpreted literally. The native Pedersen backend
performs no implicit reduction modulo the subgroup order. -/
theorem scalarMul_groupPoint (point : RawPoint) (scalar : Nat) (admitted : Admissible point) :
    groupPoint (nativeScalarMul point scalar)=scalar • groupPoint point := by
  change groupPoint (nativeScalarLoop point scalar nativeIdentity)=_
  rw [scalarLoop_groupPoint point nativeIdentity scalar admitted identity_admissible,
    identity_groupPoint,zero_add]

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.scalarLoop_groupPoint
#print axioms LeanCrypto.Proofs.BabyJubjub.scalarMul_groupPoint
