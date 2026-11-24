import LeanCryptoProofs.HintedMillerCertificate
import LeanCryptoProofs.TateFinalGuards

set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing

theorem miller_from_hinted_trace (q p : Point) (qCurve : q.onCurve = true) (pCurve : p.onCurve = true)
    (rows : List (StepHint × MProd Fp12 (Option Point)))
    (initial : MProd Fp12 (Option Point)) (start : initial = ⟨Fp12.one, some q⟩)
    (length : rows.length = Nat.log2 LeanCrypto.BN254.G1.scalarPrime)
    (checked : hintedTraceCheck q p (Nat.log2 LeanCrypto.BN254.G1.scalarPrime + 1) 1 initial rows = true)
    (finiteEnd : (traceLast initial (rows.map Prod.snd)).snd = none) :
    miller q p = .ok (traceLast initial (rows.map Prod.snd)).fst := by
  have constructed := hintedTraceCheck_sound q p _ 1 initial rows checked
  rw [length] at constructed
  have folded : millerFold q p = .ok (traceLast initial (rows.map Prod.snd)) := by
    unfold millerFold
    dsimp only
    rw [Nat.add_sub_cancel]
    rw [← start]
    exact constructed
  rw [miller_source]
  simp only [qCurve, pCurve, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    folded, bind, Except.bind, finiteEnd]
  rfl

theorem power_from_trace (first : PowerState) (states : List PowerState)
    (initial : first.accumulator = Fp12.one) (checked : powerTraceCheck first states = true) :
    first.base.pow first.exponent = (traceLast first states).accumulator := by
  have constructed := powerTraceCheck_sound first states checked
  rw [initial] at constructed
  exact constructed

theorem pair_from_miller (first : LeanCrypto.BN254.G1.Affine) (second : LeanCrypto.BN254.G2.Affine)
    (firstCurve : first.onCurve = true) (secondCurve : second.onCurve = true)
    (subgroup : ((LeanCrypto.BN254.G2.Jacobian.ofAffine second).scalarMul LeanCrypto.BN254.G1.scalarPrime).isInfinity = true)
    (value : Fp12) (source : miller (embedG2 second) (embedG1 first) = .ok value) :
    pair first second = .ok (value.pow finalExponent) := by
  rw [pair_eq_candidate, pairCandidate_source]
  simp only [firstCurve, secondCurve, subgroup, Bool.not_true, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, source, bind, Except.bind]
  rfl

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.miller_from_hinted_trace
#print axioms LeanCrypto.Proofs.BN254Tate.power_from_trace
#print axioms LeanCrypto.Proofs.BN254Tate.pair_from_miller
