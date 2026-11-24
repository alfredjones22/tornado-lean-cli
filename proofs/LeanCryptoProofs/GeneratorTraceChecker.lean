import LeanCryptoProofs.NativePairingHom

set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing

def optionalPointEqual : Option Point → Option Point → Bool
  | none, none => true
  | some first, some second => first.x == second.x && first.y == second.y
  | _, _ => false

def millerStateEqual (first second : MProd Fp12 (Option Point)) : Bool :=
  first.fst == second.fst && optionalPointEqual first.snd second.snd

def millerStepCheck (q p : Point) (bits index : Nat) (first second : MProd Fp12 (Option Point)) : Bool :=
  match millerStep q p bits index first with
  | .error _ => false
  | .ok result => millerStateEqual result second

theorem optionalPointEqual_sound (first second : Option Point) (equal : optionalPointEqual first second = true) :
    first = second := by
  cases first with
  | none => cases second <;> simp_all [optionalPointEqual]
  | some first =>
    cases second with
    | none => simp [optionalPointEqual] at equal
    | some second =>
      have components := Bool.and_eq_true_iff.mp equal
      have x := BN254Fp12.model_injective ((BN254Fp12.model_beq first.x second.x).1 components.1)
      have y := BN254Fp12.model_injective ((BN254Fp12.model_beq first.y second.y).1 components.2)
      cases first
      cases second
      cases x
      cases y
      rfl

theorem millerStateEqual_sound (first second : MProd Fp12 (Option Point))
    (equal : millerStateEqual first second = true) : first = second := by
  have components := Bool.and_eq_true_iff.mp equal
  have value := BN254Fp12.model_injective ((BN254Fp12.model_beq first.fst second.fst).1 components.1)
  have point := optionalPointEqual_sound first.snd second.snd components.2
  cases first
  cases second
  cases value
  cases point
  rfl

theorem millerStepCheck_sound (q p : Point) (bits index : Nat) (first second : MProd Fp12 (Option Point))
    (checked : millerStepCheck q p bits index first second = true) :
    millerStep q p bits index first = .ok second := by
  cases actual : millerStep q p bits index first with
  | error message => simp [millerStepCheck, actual] at checked
  | ok result =>
    have equal : millerStateEqual result second = true := by simpa only [millerStepCheck, actual] using checked
    exact congrArg Except.ok (millerStateEqual_sound result second equal)

def traceLast {α : Type} (first : α) : List α → α
  | [] => first
  | next :: rest => traceLast next rest

def millerTraceCheck (q p : Point) (bits index : Nat) (first : MProd Fp12 (Option Point)) :
    List (MProd Fp12 (Option Point)) → Bool
  | [] => true
  | next :: rest => millerStepCheck q p bits index first next && millerTraceCheck q p bits (index + 1) next rest

theorem millerTraceCheck_sound (q p : Point) (bits index : Nat) (first : MProd Fp12 (Option Point))
    (states : List (MProd Fp12 (Option Point))) (checked : millerTraceCheck q p bits index first states = true) :
    (List.range' index states.length).foldlM (fun state step => millerStep q p bits step state) first =
      .ok (traceLast first states) := by
  induction states generalizing index first with
  | nil => rfl
  | cons next rest ih =>
    have components := Bool.and_eq_true_iff.mp checked
    have step := millerStepCheck_sound q p bits index first next components.1
    simp only [List.length_cons, List.range'_succ, List.foldlM_cons, step, bind, Except.bind, traceLast]
    exact ih (index + 1) next components.2

structure PowerState where
  base : Fp12
  accumulator : Fp12
  exponent : Nat

def powerStateEqual (first second : PowerState) : Bool :=
  first.base == second.base && first.accumulator == second.accumulator && first.exponent == second.exponent

def powerNext (state : PowerState) : PowerState :=
  ⟨state.base.square, if state.exponent % 2 == 1 then state.accumulator.mul state.base else state.accumulator,
    state.exponent / 2⟩

def powerTraceCheck (first : PowerState) : List PowerState → Bool
  | [] => first.exponent == 0
  | next :: rest => first.exponent != 0 && powerStateEqual (powerNext first) next && powerTraceCheck next rest

theorem powerStateEqual_sound (first second : PowerState) (equal : powerStateEqual first second = true) : first = second := by
  have components := Bool.and_eq_true_iff.mp equal
  have fields := Bool.and_eq_true_iff.mp components.1
  have base := BN254Fp12.model_injective ((BN254Fp12.model_beq first.base second.base).1 fields.1)
  have accumulator := BN254Fp12.model_injective ((BN254Fp12.model_beq first.accumulator second.accumulator).1 fields.2)
  have exponent := of_decide_eq_true components.2
  cases first
  cases second
  cases base
  cases accumulator
  cases exponent
  rfl

theorem powerTraceCheck_sound (first : PowerState) (states : List PowerState)
    (checked : powerTraceCheck first states = true) :
    first.base.powLoop first.exponent first.accumulator = (traceLast first states).accumulator := by
  induction states generalizing first with
  | nil =>
    have zero : first.exponent = 0 := of_decide_eq_true checked
    rw [zero, Fp12.powLoop]
    rfl
  | cons next rest ih =>
    have components := Bool.and_eq_true_iff.mp checked
    have transition := Bool.and_eq_true_iff.mp components.1
    have positive : first.exponent ≠ 0 := by
      intro zero
      simp [powerTraceCheck, zero] at checked
    have equal := powerStateEqual_sound (powerNext first) next transition.2
    have tail := ih next components.2
    rw [← equal] at tail
    rw [Fp12.powLoop, dif_neg positive, ← equal]
    simpa only [powerNext, traceLast, beq_iff_eq] using tail

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.optionalPointEqual_sound
#print axioms LeanCrypto.Proofs.BN254Tate.millerStateEqual_sound
#print axioms LeanCrypto.Proofs.BN254Tate.millerStepCheck_sound
#print axioms LeanCrypto.Proofs.BN254Tate.millerTraceCheck_sound
#print axioms LeanCrypto.Proofs.BN254Tate.powerStateEqual_sound
#print axioms LeanCrypto.Proofs.BN254Tate.powerTraceCheck_sound
