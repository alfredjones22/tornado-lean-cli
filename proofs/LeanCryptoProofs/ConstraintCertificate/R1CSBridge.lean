import LeanCryptoProofs.ConstraintCertificate.CertificateSoundness
set_option autoImplicit false

namespace LeanCrypto.Proofs.ConstraintCertificate

open LeanCrypto.Groth16 LeanCrypto.Groth16.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr

theorem ofConstraint_satisfies (witness : Array Nat) (row : R1CS.Constraint) :
    Satisfies (fun index => model witness[index]!) (ofConstraint row) ↔
      R1CSModel.ConstraintSatisfied witness row := by
  simp only [Satisfies, ofConstraint, linearValue, evalSparse_sum,
    R1CSModel.ConstraintSatisfied, R1CSModel.linearValue]

theorem admitted_r1cs_row (nVars : Nat) (witness : Array Nat) (shape : witness.size = nVars)
    (row : R1CS.LinearCombination) (admitted : rowAdmitted nVars row.terms.toList = true) :
    R1CSModel.RowAdmitted witness row := by
  intro term member
  simp only [rowAdmitted, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at admitted
  have valid := admitted.2 term (Array.mem_toList_iff.mpr member)
  refine ⟨?_, valid.2⟩
  rw [shape]
  exact valid.1

/-- The source-equation proof and public certificate construct success of
the actual secret-witness R1CS checker. No R1CS acceptance is a premise. -/
theorem checkCertificate_constructs_r1cs (circuit : R1CS.Circuit) (witness : Array Nat)
    (nSignals : Nat) (linears : Array Linear) (nonlinear : Array Equation) (certificate : Certificate)
    (extended : Nat → Fr) (extendedConstant : extended 0 = 1)
    (agrees : ∀ index, index < circuit.nVars → extended index = model witness[index]!)
    (linearSources : RowsZero extended linears)
    (nonlinearSources : EquationsSatisfied extended nonlinear)
    (publicChecked : checkCertificate circuit.nVars nSignals linears nonlinear
      (circuit.constraints.map ofConstraint) certificate = .ok ())
    (shape : witness.size = circuit.nVars) (constant : witness[0]? = some 1)
    (canonical : ∀ value ∈ witness, value < Q) :
    R1CS.checkCircuit circuit witness = .ok circuit.constraints.size := by
  obtain ⟨_, targetAdmitted⟩ := checkCertificate_sound circuit.nVars nSignals linears nonlinear
    (circuit.constraints.map ofConstraint) certificate extended extendedConstant linearSources nonlinearSources publicChecked
  have targetSatisfied := checkCertificate_prefix_sound circuit.nVars nSignals linears nonlinear
    (circuit.constraints.map ofConstraint) certificate extended (fun index => model witness[index]!)
    extendedConstant agrees linearSources nonlinearSources publicChecked
  apply R1CSModel.checkCircuit_construct circuit witness shape constant canonical
  · intro row member
    have targetMember : ofConstraint row ∈ circuit.constraints.map ofConstraint := Array.mem_map.mpr ⟨row, member, rfl⟩
    have admitted := Array.all_eq_true_iff_forall_mem.mp targetAdmitted (ofConstraint row) targetMember
    simp only [ofConstraint, equationAdmitted, Bool.and_eq_true] at admitted
    exact ⟨admitted_r1cs_row circuit.nVars witness shape row.a admitted.1.1,
      admitted_r1cs_row circuit.nVars witness shape row.b admitted.1.2,
      admitted_r1cs_row circuit.nVars witness shape row.c admitted.2⟩
  · intro row member
    apply (ofConstraint_satisfies witness row).1
    exact targetSatisfied (ofConstraint row) (Array.mem_map.mpr ⟨row, member, rfl⟩)

theorem preparedCertificate_constructs_r1cs (circuit : R1CS.Circuit) (witness : Array Nat)
    (nSignals : Nat) (linears : Array Linear) (nonlinear : Array Equation) (certificate : Certificate)
    (checked : CheckedCertificate circuit.nVars nSignals linears nonlinear
      (circuit.constraints.map ofConstraint) certificate)
    (extended : Nat → Fr) (extendedConstant : extended 0 = 1)
    (agrees : ∀ index, index < circuit.nVars → extended index = model witness[index]!)
    (linearSources : RowsZero extended linears)
    (nonlinearSources : EquationsSatisfied extended nonlinear)
    (shape : witness.size = circuit.nVars) (constant : witness[0]? = some 1)
    (canonical : ∀ value ∈ witness, value < Q) :
    R1CS.checkCircuit circuit witness = .ok circuit.constraints.size :=
  checkCertificate_constructs_r1cs circuit witness nSignals linears nonlinear certificate extended extendedConstant
    agrees linearSources nonlinearSources (checkedCertificate_accepted circuit.nVars nSignals linears nonlinear
      (circuit.constraints.map ofConstraint) certificate checked) shape constant canonical

end LeanCrypto.Proofs.ConstraintCertificate

#print axioms LeanCrypto.Proofs.ConstraintCertificate.ofConstraint_satisfies
#print axioms LeanCrypto.Proofs.ConstraintCertificate.admitted_r1cs_row
#print axioms LeanCrypto.Proofs.ConstraintCertificate.checkCertificate_constructs_r1cs
#print axioms LeanCrypto.Proofs.ConstraintCertificate.preparedCertificate_constructs_r1cs
