import LeanCryptoProofs.ConstraintCertificate.DerivedRows
set_option autoImplicit false

namespace LeanCrypto.Proofs.ConstraintCertificate

open LeanCrypto.Groth16.ConstraintCertificate

theorem substituteStep_value (assignment : Nat → Fr) (rows : Array Linear) (rules : Array Rule)
    (zero : RowsZero assignment rows) (row : Linear) (instruction : Nat) (output : Linear)
    (returned : substituteStep rows rules row instruction = .ok output) :
    linearValue assignment output = linearValue assignment row := by
  unfold substituteStep at returned
  split at returned
  · change (Except.error "Invalid constraint-certificate substitution reference." : Except String Linear) = .ok output at returned
    contradiction
  · rename_i validInstruction
    dsimp only at returned
    split at returned
    · change (Except.error "Invalid constraint-certificate basis reference." : Except String Linear) = .ok output at returned
      contradiction
    · rename_i validBasis
      have basisBound : rules[instruction]!.row < rows.size := by omega
      split at returned
      · change (Except.error "Constraint-certificate substituted row is too wide." : Except String Linear) = .ok output at returned
        contradiction
      · have equal : addLinear row (scaleLinear ((modulus - coefficient rules[instruction]!.pivot row) % modulus)
            rows[rules[instruction]!.row]!) = output := Except.ok.inj returned
        rw [← equal, linear_add, linear_scale, rowsZero_get assignment rows zero _ basisBound, mul_zero, add_zero]

def substituteEffect (rows : Array Linear) (rules : Array Rule) (instruction : Nat) (row : Linear) :
    Except String (ForInStep Linear) := do
  let next ← substituteStep rows rules row instruction
  pure (ForInStep.yield next)

theorem substituteEffect_value (assignment : Nat → Fr) (rows : Array Linear) (rules : Array Rule)
    (zero : RowsZero assignment rows) (instruction : Nat) (row : Linear) (next : ForInStep Linear)
    (returned : substituteEffect rows rules instruction row = .ok next) :
    linearValue assignment next.value = linearValue assignment row := by
  unfold substituteEffect at returned
  cases effect : substituteStep rows rules row instruction with
  | error failure =>
    rw [effect] at returned
    change (Except.error failure : Except String (ForInStep Linear)) = .ok next at returned
    contradiction
  | ok output =>
    rw [effect] at returned
    have equal : ForInStep.yield output = next := Except.ok.inj returned
    rw [← equal]
    exact substituteStep_value assignment rows rules zero row instruction output effect

theorem substitute_source (rows : Array Linear) (rules : Array Rule) (initial : Linear) (program : List Nat) :
    substitute rows rules initial program =
      ForIn.forIn program (normalizeLinear initial) (substituteEffect rows rules) := by
  change ((do
    let result ← ForIn.forIn program (normalizeLinear initial) (substituteEffect rows rules)
    pure result) : Except String Linear) = _
  simp only [bind_pure]

theorem substitute_value (assignment : Nat → Fr) (rows : Array Linear) (rules : Array Rule)
    (zero : RowsZero assignment rows) (initial : Linear) (program : List Nat) (output : Linear)
    (returned : substitute rows rules initial program = .ok output) :
    linearValue assignment output = linearValue assignment initial := by
  rw [substitute_source] at returned
  apply forIn_success_invariant program (substituteEffect rows rules)
    (fun row => linearValue assignment row = linearValue assignment initial) _
    (normalizeLinear initial) (linear_normalize assignment initial) output returned
  intro instruction _ row previous next effect
  exact (substituteEffect_value assignment rows rules zero instruction row next effect).trans previous

theorem substituteEquation_values (assignment : Nat → Fr) (rows : Array Linear) (rules : Array Rule)
    (zero : RowsZero assignment rows) (nVars : Nat) (equation : Equation) (program : Substitution)
    (output : Equation) (returned : substituteEquation nVars rows rules equation program = .ok output) :
    linearValue assignment output.a = linearValue assignment equation.a ∧
      linearValue assignment output.b = linearValue assignment equation.b ∧
      linearValue assignment output.c = linearValue assignment equation.c := by
  unfold substituteEquation at returned
  cases aResult : substitute rows rules equation.a program.a with
  | error failure =>
    rw [aResult] at returned
    change (Except.error failure : Except String Equation) = .ok output at returned
    contradiction
  | ok a =>
    rw [aResult] at returned
    cases bResult : substitute rows rules equation.b program.b with
    | error failure =>
      rw [bResult] at returned
      change (Except.error failure : Except String Equation) = .ok output at returned
      contradiction
    | ok b =>
      rw [bResult] at returned
      cases cResult : substitute rows rules equation.c program.c with
      | error failure =>
        rw [cResult] at returned
        change (Except.error failure : Except String Equation) = .ok output at returned
        contradiction
      | ok c =>
        rw [cResult] at returned
        change (if !equationAdmitted nVars ⟨a, b, c⟩ then
          (throw "Constraint-certificate auxiliary elimination is incomplete." : Except String PUnit) >>= fun _ => _
          else (pure PUnit.unit : Except String PUnit) >>= fun _ => _) = .ok output at returned
        split at returned
        · change (Except.error "Constraint-certificate auxiliary elimination is incomplete." : Except String Equation) = .ok output at returned
          contradiction
        · split at returned
          · change (Except.error "Constraint-certificate polynomial is too large." : Except String Equation) = .ok output at returned
            contradiction
          · have equal : Equation.mk a b c = output := Except.ok.inj returned
            rw [← equal]
            exact ⟨substitute_value assignment rows rules zero equation.a program.a a aResult,
              substitute_value assignment rows rules zero equation.b program.b b bResult,
              substitute_value assignment rows rules zero equation.c program.c c cResult⟩

theorem substituteEquation_satisfies (assignment : Nat → Fr) (rows : Array Linear) (rules : Array Rule)
    (zero : RowsZero assignment rows) (nVars : Nat) (equation : Equation) (program : Substitution)
    (satisfied : Satisfies assignment equation) (output : Equation)
    (returned : substituteEquation nVars rows rules equation program = .ok output) : Satisfies assignment output := by
  obtain ⟨a, b, c⟩ := substituteEquation_values assignment rows rules zero nVars equation program output returned
  unfold Satisfies
  rw [a, b, c]
  exact satisfied

end LeanCrypto.Proofs.ConstraintCertificate

#print axioms LeanCrypto.Proofs.ConstraintCertificate.substituteStep_value
#print axioms LeanCrypto.Proofs.ConstraintCertificate.substituteEffect_value
#print axioms LeanCrypto.Proofs.ConstraintCertificate.substitute_source
#print axioms LeanCrypto.Proofs.ConstraintCertificate.substitute_value
#print axioms LeanCrypto.Proofs.ConstraintCertificate.substituteEquation_values
#print axioms LeanCrypto.Proofs.ConstraintCertificate.substituteEquation_satisfies
