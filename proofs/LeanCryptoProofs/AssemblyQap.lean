import LeanCryptoProofs.ProofObservation
import LeanCryptoProofs.FFT.HConstruction

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanCrypto.Proofs.Groth16Assembly

open LeanCrypto.BN254 LeanCrypto.Groth16
open scoped BigOperators
local instance : Fact G1.scalarPrime.Prime := ⟨Primes.bn254_scalar_prime⟩
local instance : NeZero G1.scalarPrime := ⟨by decide⟩

/-- Scalar-level interpretation of public/private setup queries. Parameters
are the honest setup secrets; this relation is not computable from a key
hash. Proving key soundness and setup ceremony honesty remain assumptions. -/
structure QapRelation (key : Types.QueryKey) (values : QueryScalars)
    (witness h : Array Nat) (setup : IdealGroth16.Setup Fr)
    (a b c : Polynomial Fr) (tau : Fr) (domain : Nat) : Prop where
  alpha : values.alpha = setup.alpha
  beta : values.beta = setup.beta
  delta : values.delta = setup.delta
  aQueries : linearScalar values.a witness witness.size = a.eval tau
  bQueries : linearScalar values.b witness witness.size = b.eval tau
  privateQueries : linearScalar values.c (witness.extract (key.nPublic + 1) witness.size)
      key.queryC.size = (setup.beta * a.eval tau + setup.alpha * b.eval tau + c.eval tau -
        setup.gamma * setup.publicIC) / setup.delta
  hQueries : linearScalar values.h h h.size =
    (LeanCrypto.Proofs.FFT.coeffPolynomial h).eval tau * (tau ^ domain - 1) / setup.delta

/-- The independently specified key-query relation and QAP polynomial
identity derive compatibility; compatibility is not itself an assumption. -/
theorem offsets_compatible_from_qap (key : Types.QueryKey) (values : QueryScalars)
    (witness h : Array Nat) (setup : IdealGroth16.Setup Fr)
    (a b c : Polynomial Fr) (tau : Fr) (domain : Nat)
    (relation : QapRelation key values witness h setup a b c tau domain)
    (qap : a.eval tau * b.eval tau - c.eval tau =
      (LeanCrypto.Proofs.FFT.coeffPolynomial h).eval tau * (tau ^ domain - 1)) :
    setup.delta * kOffset key values witness h =
      aOffset values witness * bOffset values witness - setup.kappa := by
  dsimp only [kOffset, aOffset, bOffset, IdealGroth16.Setup.kappa]
  rw [relation.alpha, relation.beta, relation.aQueries, relation.bQueries,
    relation.privateQueries, relation.hQueries, ← qap, ← add_div,
    mul_div_cancel₀ _ setup.delta_ne_zero]
  ring

noncomputable def qapOffsets (key : Types.QueryKey) (values : QueryScalars)
    (witness h : Array Nat) (setup : IdealGroth16.Setup Fr)
    (a b c : Polynomial Fr) (tau : Fr) (domain : Nat)
    (relation : QapRelation key values witness h setup a b c tau domain)
    (qap : a.eval tau * b.eval tau - c.eval tau =
      (LeanCrypto.Proofs.FFT.coeffPolynomial h).eval tau * (tau ^ domain - 1)) :
    IdealGroth16.WitnessOffsets setup :=
  ⟨aOffset values witness, bOffset values witness, kOffset key values witness h,
    offsets_compatible_from_qap key values witness h setup a b c tau domain relation qap⟩

theorem scalarOutput_eq_ideal (key : Types.QueryKey) (values : QueryScalars)
    (witness h : Array Nat) (setup : IdealGroth16.Setup Fr)
    (a b c : Polynomial Fr) (tau : Fr) (domain : Nat)
    (relation : QapRelation key values witness h setup a b c tau domain)
    (qap : a.eval tau * b.eval tau - c.eval tau =
      (LeanCrypto.Proofs.FFT.coeffPolynomial h).eval tau * (tau ^ domain - 1)) (r s : Nat) :
    scalarOutput key values witness h r s = IdealGroth16.output
      (qapOffsets key values witness h setup a b c tau domain relation qap) ((r : Fr), (s : Fr)) := by
  unfold scalarOutput IdealGroth16.output qapOffsets
  rw [relation.delta]

/-- The original native serializer, with every exceptional outcome kept,
is a deterministic observation of the ideal Groth16 triple. This closes
MSM, coordinate normalization, negative-rs and encoding representation
bridges, conditional on honest setup/query relations and the QAP identity. -/
theorem serialization_eq_ideal_observer (key : Types.QueryKey) (values : QueryScalars)
    (witness h : Array Nat) (r s : Nat) (valid : ValidKey key)
    (dimensions : Dimensions key witness h) (canonical : Canonical witness h r s)
    (span : KeySpan key values) (setup : IdealGroth16.Setup Fr)
    (a b c : Polynomial Fr) (tau : Fr) (domain : Nat)
    (relation : QapRelation key values witness h setup a b c tau domain)
    (qap : a.eval tau * b.eval tau - c.eval tau =
      (LeanCrypto.Proofs.FFT.coeffPolynomial h).eval tau * (tau ^ domain - 1)) :
    MSM.solidityProofBytes (construction key witness h r s) =
      MSM.solidityProofBytes (canonicalPoints (witness.extract 1 (key.nPublic + 1))
        (IdealGroth16.output (qapOffsets key values witness h setup a b c tau domain relation qap)
          ((r : Fr), (s : Fr)))) := by
  rw [assembly_serialization_factors key values witness h r s valid dimensions canonical span,
    scalarOutput_eq_ideal key values witness h setup a b c tau domain relation qap r s]

end LeanCrypto.Proofs.Groth16Assembly

#print axioms LeanCrypto.Proofs.Groth16Assembly.offsets_compatible_from_qap
#print axioms LeanCrypto.Proofs.Groth16Assembly.scalarOutput_eq_ideal
#print axioms LeanCrypto.Proofs.Groth16Assembly.serialization_eq_ideal_observer
