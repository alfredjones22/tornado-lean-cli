import LeanCryptoProofs.TateFieldBridge
open Lean Elab Term Meta
elab "actualTateLineAndSum" : term =>
  mkConstWithFreshMVarLevels
    (mkPrivateNameCore `LeanCrypto.BN254.TatePairing `LeanCrypto.BN254.TatePairing.lineAndSum)

set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.G1 LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing

abbrev nativeLineAndSum (r s evaluation : Point) : Except String (Fp12 × Option Point) :=
  actualTateLineAndSum r s evaluation

def millerStep (q p : Point) (bits step : Nat) (state : MProd Fp12 (Option Point)) :
    Except String (MProd Fp12 (Option Point)) := do
  let some current := state.snd
    | throw "BN254 Miller accumulator reached infinity early."
  let (doubled, doubledPoint) ← nativeLineAndSum current current p
  let f := state.fst.square.mul doubled
  let bit := scalarPrime / 2 ^ (bits - step - 1) % 2
  if bit == 1 then
    let some current := doubledPoint
      | throw "BN254 Miller accumulator reached infinity before addition."
    let (added, addedPoint) ← nativeLineAndSum current q p
    return ⟨f.mul added, addedPoint⟩
  else return ⟨f, doubledPoint⟩

def millerFold (q p : Point) : Except String (MProd Fp12 (Option Point)) :=
  let bits := Nat.log2 scalarPrime + 1
  (List.range' 1 (bits - 1)).foldlM (fun state step => millerStep q p bits step state)
    ⟨Fp12.one, some q⟩

theorem miller_forIn_fold (q p : Point) (bits : Nat) (steps : List Nat)
    (state : MProd Fp12 (Option Point)) :
    forIn steps state (fun step current => ForInStep.yield <$> millerStep q p bits step current) =
      steps.foldlM (fun current step => millerStep q p bits step current) state := by
  simp

theorem miller_source (q p : Point) :
    miller q p = if !q.onCurve || !p.onCurve then
      .error "BN254 pairing point is off E(Fp12)."
    else do
      let state ← millerFold q p
      if state.snd.isSome then throw "BN254 Miller scalar did not reach infinity."
      return state.fst := by
  simp only [miller, Std.Legacy.Range.forIn_eq_forIn_range', pure_bind, bind_pure_comp]
  split
  · rfl
  · unfold millerFold
    rw [← miller_forIn_fold]
    congr 1
    simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
    congr 1
    funext step state
    cases current : state.snd with
    | none => simp [millerStep, current]; rfl
    | some point =>
      cases doubled : nativeLineAndSum point point p with
      | error message => simp [millerStep, current, doubled]; rfl
      | ok result =>
        rcases result with ⟨factor, next⟩
        simp only [millerStep, current, doubled, bind, Except.bind]
        split
        · cases added : next with
          | none => simp []; rfl
          | some nextPoint =>
            cases addition : nativeLineAndSum nextPoint q p <;> simp [addition]
        · simp []

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.miller_forIn_fold
#print axioms LeanCrypto.Proofs.BN254Tate.miller_source
