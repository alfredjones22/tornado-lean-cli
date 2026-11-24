import LeanCryptoProofs.TateMillerNonzero
open Lean Elab Term Meta
elab "actualTatePairCandidate" : term =>
  mkConstWithFreshMVarLevels
    (mkPrivateNameCore `LeanCrypto.BN254.TatePairing `LeanCrypto.BN254.TatePairing.pairCandidate)

set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.G1 LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing BN254Fp12

abbrev nativePairCandidate (g1 : Affine) (g2 : LeanCrypto.BN254.G2.Affine) : Except String Fp12 :=
  actualTatePairCandidate g1 g2

theorem pairCandidate_source (g1 : Affine) (g2 : LeanCrypto.BN254.G2.Affine) :
    nativePairCandidate g1 g2 = (do
      if !g1.onCurve || !g2.onCurve then throw "BN254 pairing input is off-curve."
      if !((LeanCrypto.BN254.G2.Jacobian.ofAffine g2).scalarMul scalarPrime).isInfinity then
        throw "BN254 G2 point is outside the prime-order subgroup."
      let value ← miller (embedG2 g2) (embedG1 g1)
      return value.pow finalExponent) := rfl

/-- The two final native guards add no further failure to a candidate:
Miller's nonzero invariant and the proved finite-field exponent identity
discharge them for all inputs. Input and Miller errors still propagate. -/
theorem pair_eq_candidate (g1 : Affine) (g2 : LeanCrypto.BN254.G2.Affine) :
    pair g1 g2 = nativePairCandidate g1 g2 := by
  have source := pairCandidate_source g1 g2
  by_cases onCurve : (!g1.onCurve || !g2.onCurve) = true
  · have failed : nativePairCandidate g1 g2 = .error "BN254 pairing input is off-curve." := by
      rw [source]
      simp [onCurve, bind, Except.bind]
    change (match nativePairCandidate g1 g2 with
      | .error message => Except.error message
      | .ok final => if final == Fp12.zero then Except.error _
        else if final.pow scalarPrime == Fp12.one then Except.ok final else Except.error _) = _
    rw [failed]
  · by_cases subgroup : (!((LeanCrypto.BN254.G2.Jacobian.ofAffine g2).scalarMul scalarPrime).isInfinity) = true
    · have failed : nativePairCandidate g1 g2 = .error "BN254 G2 point is outside the prime-order subgroup." := by
        rw [source]
        simp [onCurve, subgroup, bind, Except.bind, pure, Except.pure]
      change (match nativePairCandidate g1 g2 with
        | .error message => Except.error message
        | .ok final => if final == Fp12.zero then Except.error _
          else if final.pow scalarPrime == Fp12.one then Except.ok final else Except.error _) = _
      rw [failed]
    · cases result : miller (embedG2 g2) (embedG1 g1) with
      | error message =>
        have failed : nativePairCandidate g1 g2 = .error message := by
          rw [source]
          simp [onCurve, subgroup, result, bind, Except.bind, pure, Except.pure]
        change (match nativePairCandidate g1 g2 with
          | .error message => Except.error message
          | .ok final => if final == Fp12.zero then Except.error _
            else if final.pow scalarPrime == Fp12.one then Except.ok final else Except.error _) = _
        rw [failed]
      | ok value =>
        have nonzero := miller_success_nonzero _ _ value result
        have constructed : nativePairCandidate g1 g2 = .ok (value.pow finalExponent) := by
          rw [source]
          simp [onCurve, subgroup, result, bind, Except.bind, pure, Except.pure]
        have notZero : (value.pow finalExponent == Fp12.zero) = false := by
          apply Bool.eq_false_iff.mpr
          intro zero
          exact final_power_nonzero value nonzero ((model_beq _ _).1 zero |>.trans model_zero)
        have order := final_power_order value nonzero
        change (match nativePairCandidate g1 g2 with
          | .error message => Except.error message
          | .ok final => if final == Fp12.zero then Except.error _
            else if final.pow scalarPrime == Fp12.one then Except.ok final else Except.error _) = _
        simp only [constructed, notZero, Bool.false_eq_true, ↓reduceIte, order]

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.pairCandidate_source
#print axioms LeanCrypto.Proofs.BN254Tate.pair_eq_candidate
