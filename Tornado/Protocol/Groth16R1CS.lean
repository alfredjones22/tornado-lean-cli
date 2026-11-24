import LeanCrypto.Groth16.R1CS

/-! Definitional compatibility aliases for the standalone implementation. -/

namespace Tornado.Protocol.Groth16R1CS

export LeanCrypto.Groth16.R1CS (scalarPrime decodeLinearCombination decodeConstraint decodeCircuit decodeWitness rowIndicesValid evaluateRow checkConstraint checkCircuit evaluated_row_has_valid_indices checked_constraint_satisfies LinearCombination LinearCombination.mk LinearCombination.terms Constraint Constraint.mk Constraint.a Constraint.b Constraint.c Circuit Circuit.mk Circuit.nVars Circuit.nPublic Circuit.constraints)

end Tornado.Protocol.Groth16R1CS
