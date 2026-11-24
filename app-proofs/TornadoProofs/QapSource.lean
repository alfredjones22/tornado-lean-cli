import TornadoProofs.ProofPrivacy

set_option autoImplicit false

namespace TornadoProofs.ProofPrivacy

open LeanCrypto.BN254 LeanCrypto.Groth16 LeanCrypto.Proofs.Groth16Assembly
local instance : Fact G1.scalarPrime.Prime := ⟨LeanCrypto.Proofs.Primes.bn254_scalar_prime⟩
local instance : NeZero G1.scalarPrime := ⟨by decide⟩

/-- Independent original sparse-key row semantics for one fixed witness.
The rows are mathematical constraint equations, not success of the native
R1CS checker, H calculation, quotient check or final pairing verifier. -/
structure HSource (witness : Array Nat) where
  domain : Nat
  polsA : Array Types.Polynomial
  polsB : Array Types.Polynomial
  a : Polynomial Fr
  b : Polynomial Fr
  c : Polynomial Fr
  domainValid : FFT.validSize domain = true
  domainBound : domain ≤ FFT.provingDomainSize
  domainMinimum : 2 ≤ domain
  witnessPositive : 0 < witness.size
  witnessCanonical : LeanCrypto.Proofs.FFT.Canonical witness
  validA : LeanCrypto.Proofs.FFT.ValidSparseInput domain witness polsA
  validB : LeanCrypto.Proofs.FFT.ValidSparseInput domain witness polsB
  aDegree : a.natDegree < domain
  bDegree : b.natDegree < domain
  cDegree : c.natDegree < domain
  aRows : ∀ row, row < domain →
    a.eval (LeanCrypto.Proofs.FFT.domainRoot domain ^ row) =
      LeanCrypto.Proofs.FFT.sparseRow witness polsA row
  bRows : ∀ row, row < domain →
    b.eval (LeanCrypto.Proofs.FFT.domainRoot domain ^ row) =
      LeanCrypto.Proofs.FFT.sparseRow witness polsB row
  constraints : ∀ row, row < domain →
    LeanCrypto.Proofs.FFT.sparseRow witness polsA row *
      LeanCrypto.Proofs.FFT.sparseRow witness polsB row =
        c.eval (LeanCrypto.Proofs.FFT.domainRoot domain ^ row)

/-- Construct the real H result and derive its mathematical QAP identity
at every setup point. Actual source admission proves native success. -/
theorem HSource.constructs (witness : Array Nat) (source : HSource witness) :
    ∃ h, FFT.calculateH source.domain witness source.polsA source.polsB = .ok h ∧
      LeanCrypto.Proofs.FFT.Canonical h ∧ h.size ≤ source.domain - 1 ∧
      ∀ tau : Fr, source.a.eval tau * source.b.eval tau - source.c.eval tau =
        (LeanCrypto.Proofs.FFT.coeffPolynomial h).eval tau * (tau ^ source.domain - 1) := by
  obtain ⟨h, built, canonical, _, equation⟩ := LeanCrypto.Proofs.FFT.calculateH_quotient
    source.domain witness source.polsA source.polsB source.domainValid source.domainBound
    source.domainMinimum source.witnessPositive source.witnessCanonical source.validA source.validB
    source.a source.b source.c source.aDegree source.bDegree source.cDegree
    source.aRows source.bRows source.constraints
  have dimension := LeanCrypto.Proofs.FFT.calculateH_success_dimension source.domain witness
    source.polsA source.polsB source.domainValid source.domainBound source.domainMinimum
    source.witnessPositive source.witnessCanonical source.validA source.validB h built
  refine ⟨h, built, canonical, dimension, ?_⟩
  have result := LeanCrypto.Proofs.FFT.calculateH_success_quotient source.domain witness
    source.polsA source.polsB source.domainValid source.domainBound source.domainMinimum
    source.witnessPositive source.witnessCanonical source.validA source.validB source.a source.b source.c
    source.aDegree source.bDegree source.cDegree source.aRows source.bRows source.constraints h built
  exact result.2.2.2

/-- Constructor for the privacy context from the actual native H return.
No quotient or accepted proof equation is supplied by the caller. -/
noncomputable def Context.fromH (key : Types.QueryKey) (values : QueryScalars)
    (witness h : Array Nat) (source : HSource witness)
    (returned : FFT.calculateH source.domain witness source.polsA source.polsB = .ok h)
    (setup : IdealGroth16.Setup Fr) (tau : Fr) (valid : ValidKey key)
    (dimensions : Dimensions key witness h) (span : KeySpan key values)
    (relation : QapRelation key values witness h setup source.a source.b source.c tau source.domain) : Context := by
  have result := LeanCrypto.Proofs.FFT.calculateH_success_quotient source.domain witness
    source.polsA source.polsB source.domainValid source.domainBound source.domainMinimum
    source.witnessPositive source.witnessCanonical source.validA source.validB source.a source.b source.c
    source.aDegree source.bDegree source.cDegree source.aRows source.bRows source.constraints h returned
  refine ⟨key, values, witness, h, setup, source.a, source.b, source.c, tau, source.domain,
    valid, dimensions, ?_, ?_, span, relation, result.2.2.2 tau⟩
  · apply Array.all_eq_true.mpr
    intro index bounded
    exact decide_eq_true (source.witnessCanonical index bounded)
  · apply Array.all_eq_true.mpr
    intro index bounded
    exact decide_eq_true (result.1 index bounded)

end TornadoProofs.ProofPrivacy

#print axioms TornadoProofs.ProofPrivacy.HSource.constructs
