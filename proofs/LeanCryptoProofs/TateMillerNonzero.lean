import LeanCryptoProofs.TateMillerSource
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing BN254Fp12

theorem nativeLineAndSum_source (r s evaluation : Point) : nativeLineAndSum r s evaluation = (do
    if r.x == s.x && r.y == s.y.neg then
      let vertical := evaluation.x.sub r.x
      if vertical == Fp12.zero then throw "BN254 vertical line evaluated to zero."
      return (vertical, none)
    let slope ← if r.x == s.x && r.y == s.y then
      nativeDivide (r.x.square.mul (embedFp (LeanCrypto.BN254.G1.Fp.ofNat 3)))
        (r.y.mul (embedFp (LeanCrypto.BN254.G1.Fp.ofNat 2)))
      else nativeDivide (s.y.sub r.y) (s.x.sub r.x)
    let x3 := (slope.square.sub r.x).sub s.x
    let y3 := (slope.mul (r.x.sub x3)).sub r.y
    let line := (evaluation.y.sub r.y).sub (slope.mul (evaluation.x.sub r.x))
    let value ← nativeDivide line (evaluation.x.sub x3)
    if value == Fp12.zero then throw "BN254 pairing line evaluated to zero."
    return (value, some ⟨x3, y3⟩)) := rfl

theorem nativeLineAndSum_nonzero (r s evaluation : Point) (factor : Fp12) (next : Option Point)
    (success : nativeLineAndSum r s evaluation = .ok (factor, next)) : model factor ≠ 0 := by
  rw [nativeLineAndSum_source] at success
  simp only [bind, Except.bind, pure, Except.pure] at success
  repeat' split at success
  all_goals try simp only [Except.ok.injEq, Prod.mk.injEq] at success
  all_goals try cases success
  all_goals
    intro zero
    simp_all only [model_beq, model_zero, not_true_eq_false]

theorem millerStep_nonzero (q p : Point) (bits step : Nat)
    (state output : MProd Fp12 (Option Point)) (initial : model state.fst ≠ 0)
    (success : millerStep q p bits step state = .ok output) : model output.fst ≠ 0 := by
  cases current : state.snd with
  | none => simp [millerStep, current] at success
  | some point =>
    cases doubled : nativeLineAndSum point point p with
    | error message => simp [millerStep, current, doubled, bind, Except.bind] at success
    | ok result =>
      rcases result with ⟨factor, next⟩
      have factorNonzero := nativeLineAndSum_nonzero point point p factor next doubled
      have doubledNonzero : model (state.fst.square.mul factor) ≠ 0 := by
        rw [model_mul, model_square]
        exact mul_ne_zero (pow_ne_zero 2 initial) factorNonzero
      simp only [millerStep, current, doubled, bind, Except.bind] at success
      split at success
      · cases added : next with
        | none => simp [added] at success
        | some nextPoint =>
          cases addition : nativeLineAndSum nextPoint q p with
          | error message => simp [added, addition] at success
          | ok result =>
            rcases result with ⟨factor2, next2⟩
            have factor2Nonzero := nativeLineAndSum_nonzero nextPoint q p factor2 next2 addition
            simp only [added, addition, pure, Except.pure, Except.ok.injEq] at success
            cases success
            rw [model_mul]
            exact mul_ne_zero doubledNonzero factor2Nonzero
      · simp only [pure, Except.pure, Except.ok.injEq] at success
        cases success
        exact doubledNonzero

theorem millerFold_nonzero (q p : Point) (output : MProd Fp12 (Option Point))
    (success : millerFold q p = .ok output) : model output.fst ≠ 0 := by
  have invariant (steps : List Nat) (state output : MProd Fp12 (Option Point))
      (initial : model state.fst ≠ 0)
      (success : steps.foldlM
        (fun state step => millerStep q p (LeanCrypto.BN254.G1.scalarPrime.log2 + 1) step state)
          state = .ok output) : model output.fst ≠ 0 := by
    induction steps generalizing state with
    | nil => cases success; exact initial
    | cons step tail ih =>
      cases next : millerStep q p (LeanCrypto.BN254.G1.scalarPrime.log2 + 1) step state with
      | error message => simp [List.foldlM_cons, next, bind, Except.bind] at success
      | ok nextState =>
        simp only [List.foldlM_cons, next, bind, Except.bind] at success
        exact ih nextState (millerStep_nonzero q p _ step state nextState initial next) success
  exact invariant _ ⟨Fp12.one, some q⟩ output (by simp) success

theorem miller_success_nonzero (q p : Point) (output : Fp12)
    (success : miller q p = .ok output) : model output ≠ 0 := by
  rw [miller_source] at success
  split at success
  · cases success
  · cases folded : millerFold q p with
    | error message => simp [folded, bind, Except.bind] at success
    | ok state =>
      have nonzero := millerFold_nonzero q p state folded
      simp only [folded, bind, Except.bind] at success
      split at success
      · cases success
      · simp only [pure, Except.pure, Except.ok.injEq] at success
        cases success
        exact nonzero

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.nativeLineAndSum_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.nativeLineAndSum_source
#print axioms LeanCrypto.Proofs.BN254Tate.millerStep_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.millerFold_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.miller_success_nonzero
