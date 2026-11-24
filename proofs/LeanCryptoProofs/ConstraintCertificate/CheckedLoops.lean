import LeanCryptoProofs.ConstraintCertificate.ConstraintAlgebra
set_option autoImplicit false

namespace LeanCrypto.Proofs.ConstraintCertificate

theorem forIn_success_invariant {A State : Type} (items : List A)
    (step : A → State → Except String (ForInStep State)) (invariant : State → Prop)
    (preserves : ∀ item ∈ items, ∀ state, invariant state → ∀ next,
      step item state = .ok next → invariant next.value)
    (initial : State) (initialInvariant : invariant initial)
    (output : State) (returned : ForIn.forIn items initial step = .ok output) : invariant output := by
  induction items generalizing initial output with
  | nil =>
    have equal : initial = output := Except.ok.inj returned
    simpa only [← equal] using initialInvariant
  | cons item rest ih =>
    rw [List.forIn_cons] at returned
    cases effect : step item initial with
    | error failure =>
      rw [effect] at returned
      change (Except.error failure : Except String State) = .ok output at returned
      contradiction
    | ok next =>
      rw [effect] at returned
      have nextInvariant := preserves item (by simp) initial initialInvariant next effect
      have tailPreserves : ∀ value ∈ rest, ∀ state, invariant state → ∀ next,
          step value state = .ok next → invariant next.value := by
        intro value member
        exact preserves value (by simp only [List.mem_cons]; exact Or.inr member)
      cases next with
      | done state =>
        have equal : state = output := Except.ok.inj returned
        simpa only [← equal] using nextInvariant
      | yield state =>
        exact ih tailPreserves state nextInvariant output returned

def checkEffect {A : Type} (check : A → Except String Unit) (item : A) (_ : Unit) :
    Except String (ForInStep Unit) := do
  check item
  pure (ForInStep.yield ())

theorem forIn_checks_succeed {A : Type} (items : List A) (check : A → Except String Unit)
    (returned : ForIn.forIn items () (checkEffect check) = .ok ()) :
    ∀ item ∈ items, check item = .ok () := by
  induction items with
  | nil => simp
  | cons first rest ih =>
    rw [List.forIn_cons] at returned
    cases result : check first with
    | error failure =>
      unfold checkEffect at returned
      rw [result] at returned
      change (Except.error failure : Except String Unit) = .ok () at returned
      contradiction
    | ok value =>
      cases value
      unfold checkEffect at returned
      rw [result] at returned
      change ForIn.forIn rest () (checkEffect check) = .ok () at returned
      intro item member
      rcases List.mem_cons.mp member with equal | member
      · simpa only [equal] using result
      · exact ih returned item member

end LeanCrypto.Proofs.ConstraintCertificate

#print axioms LeanCrypto.Proofs.ConstraintCertificate.forIn_success_invariant
#print axioms LeanCrypto.Proofs.ConstraintCertificate.forIn_checks_succeed
