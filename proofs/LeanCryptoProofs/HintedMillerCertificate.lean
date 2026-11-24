import LeanCryptoProofs.QuotientLineCertificate

set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing

structure StepHint where
  doubled : LineHint
  added : LineHint

def hintedStepCheck (q p : Point) (bits index : Nat) (first second : MProd Fp12 (Option Point))
    (hint : StepHint) : Bool :=
  match first.snd with
  | none => false
  | some current => lineHintCheck current current p hint.doubled &&
    if LeanCrypto.BN254.G1.scalarPrime / 2 ^ (bits - index - 1) % 2 == 1 then
      match hint.doubled.result with
      | none => false
      | some doubled => lineHintCheck doubled q p hint.added &&
        millerStateEqual ⟨(first.fst.square.mul hint.doubled.factor).mul hint.added.factor, hint.added.result⟩ second
    else millerStateEqual ⟨first.fst.square.mul hint.doubled.factor, hint.doubled.result⟩ second

theorem hintedStepCheck_sound (q p : Point) (bits index : Nat) (first second : MProd Fp12 (Option Point))
    (hint : StepHint) (checked : hintedStepCheck q p bits index first second hint = true) :
    millerStep q p bits index first = .ok second := by
  cases currentEq : first.snd with
  | none => simp [hintedStepCheck, currentEq] at checked
  | some current =>
    have currentChecked := checked
    simp only [hintedStepCheck, currentEq] at currentChecked
    have fields := Bool.and_eq_true_iff.mp currentChecked
    have doubled := lineHintCheck_sound current current p hint.doubled fields.1
    by_cases odd : (LeanCrypto.BN254.G1.scalarPrime / 2 ^ (bits - index - 1) % 2 == 1) = true
    · cases nextEq : hint.doubled.result with
      | none => simp [odd, nextEq] at fields
      | some next =>
        have tail := fields.2
        simp only [if_pos odd, nextEq] at tail
        have components := Bool.and_eq_true_iff.mp tail
        have added := lineHintCheck_sound next q p hint.added components.1
        have output := millerStateEqual_sound _ second components.2
        simp only [millerStep, currentEq, doubled, bind, Except.bind, odd, ↓reduceIte, nextEq, added]
        exact congrArg Except.ok output
    · have output := millerStateEqual_sound _ second (show millerStateEqual _ second = true by
        simpa only [if_neg odd] using fields.2)
      simp only [millerStep, currentEq, doubled, bind, Except.bind, odd, Bool.false_eq_true, ↓reduceIte]
      exact congrArg Except.ok output

def hintedTraceCheck (q p : Point) (bits index : Nat) (first : MProd Fp12 (Option Point)) :
    List (StepHint × MProd Fp12 (Option Point)) → Bool
  | [] => true
  | (hint,next) :: rest => hintedStepCheck q p bits index first next hint && hintedTraceCheck q p bits (index+1) next rest

theorem hintedTraceCheck_sound (q p : Point) (bits index : Nat) (first : MProd Fp12 (Option Point))
    (rows : List (StepHint × MProd Fp12 (Option Point))) (checked : hintedTraceCheck q p bits index first rows = true) :
    (List.range' index rows.length).foldlM (fun state step => millerStep q p bits step state) first =
      .ok (traceLast first (rows.map Prod.snd)) := by
  induction rows generalizing index first with
  | nil => rfl
  | cons row rest ih =>
    obtain ⟨hint,next⟩ := row
    have components := Bool.and_eq_true_iff.mp checked
    have step := hintedStepCheck_sound q p bits index first next hint components.1
    simp only [List.length_cons, List.range'_succ, List.foldlM_cons, step, bind, Except.bind, List.map_cons, traceLast]
    exact ih (index+1) next components.2

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.hintedStepCheck_sound
#print axioms LeanCrypto.Proofs.BN254Tate.hintedTraceCheck_sound
