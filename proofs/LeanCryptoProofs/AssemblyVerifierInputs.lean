import LeanCryptoProofs.ScalarPairing
import LeanCrypto.Groth16.Verify

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.NativeVerifier
open LeanCrypto.BN254 LeanCrypto.Groth16 Groth16Assembly
local instance : NeZero G1.scalarPrime := ⟨by decide⟩
local instance : Fact G1.scalarPrime.Prime := ⟨Primes.bn254_scalar_prime⟩

theorem scalarG1_injective : Function.Injective scalarG1 := by
  intro first second equal
  change first.val • g1 (G1.Jacobian.ofAffine G1.generator) =
    second.val • g1 (G1.Jacobian.ofAffine G1.generator) at equal
  have residues := nsmul_inj_mod.mp equal
  rw [BN254Group.generator_exact_order, Nat.mod_eq_of_lt first.val_lt,
    Nat.mod_eq_of_lt second.val_lt] at residues
  exact ZMod.val_injective _ residues

theorem normalizeG1_scalar (point : G1.Jacobian) (value : Fr) (admitted : G1Admitted point)
    (span : g1 point = scalarG1 value) (nonzero : value ≠ 0) :
    ∃ (affine : G1.Affine) (onCurve : affine.onCurve = true),
      point.toAffine = .ok (some affine) ∧ BN254Group.affinePoint affine onCurve = scalarG1 value := by
  obtain ⟨result, constructed, represented⟩ := BN254Group.toAffine_represents_groupPoint point admitted
  cases result with
  | none =>
    have zero : scalarG1 value = scalarG1 0 := by rw [map_zero]; exact span.symm.trans represented
    exact False.elim (nonzero (scalarG1_injective zero))
  | some affine =>
    obtain ⟨onCurve, equal⟩ := represented
    exact ⟨affine, onCurve, constructed, equal.symm.trans span⟩

theorem normalizeG2_scalar (point : G2.Jacobian) (value : Fr) (admitted : G2Admitted point)
    (span : g2 point = scalarG2 value) (nonzero : value ≠ 0) :
    ∃ (affine : G2.Affine) (onCurve : affine.onCurve = true),
      point.toAffine = .ok (some affine) ∧ BN254G2Group.affinePoint affine onCurve = scalarG2 value := by
  obtain ⟨result, constructed, represented⟩ := BN254G2Group.toAffine_represents_groupPoint point admitted
  cases result with
  | none =>
    have zero : scalarG2 value = scalarG2 0 := by rw [map_zero]; exact span.symm.trans represented
    exact False.elim (nonzero (BN254G2Group.scalarHom_injective zero))
  | some affine =>
    obtain ⟨onCurve, equal⟩ := represented
    exact ⟨affine, onCurve, constructed, equal.symm.trans span⟩

structure NormalizedAssembly (points : Types.ProofPoints) (triple : IdealGroth16.Triple Fr) where
  proof : Verify.Proof
  aCurve : proof.a.onCurve = true
  bCurve : proof.b.onCurve = true
  cCurve : proof.c.onCurve = true
  aNative : points.piA.toAffine = .ok (some proof.a)
  bNative : points.piB.toAffine = .ok (some proof.b)
  cNative : points.piC.toAffine = .ok (some proof.c)
  aSpan : BN254Group.affinePoint proof.a aCurve = scalarG1 triple.a
  bSpan : BN254G2Group.affinePoint proof.b bCurve = scalarG2 triple.b
  cSpan : BN254Group.affinePoint proof.c cCurve = scalarG1 triple.c

theorem construction_normalized (key : Types.QueryKey) (values : QueryScalars) (witness h : Array Nat) (r s : Nat)
    (valid : ValidKey key) (dimensions : Dimensions key witness h) (canonical : Canonical witness h r s)
    (span : KeySpan key values)
    (aNonzero : (scalarOutput key values witness h r s).a ≠ 0)
    (bNonzero : (scalarOutput key values witness h r s).b ≠ 0)
    (cNonzero : (scalarOutput key values witness h r s).c ≠ 0) :
    Nonempty (NormalizedAssembly (construction key witness h r s) (scalarOutput key values witness h r s)) := by
  obtain ⟨a, b, c⟩ := construction_admitted key witness h r s valid
  obtain ⟨am, bm, cm⟩ := construction_scalarOutput key values witness h r s valid dimensions canonical span
  obtain ⟨na, naCurve, naCall, naSpan⟩ := normalizeG1_scalar _ _ a am aNonzero
  obtain ⟨nb, nbCurve, nbCall, nbSpan⟩ := normalizeG2_scalar _ _ b bm bNonzero
  obtain ⟨nc, ncCurve, ncCall, ncSpan⟩ := normalizeG1_scalar _ _ c cm cNonzero
  exact ⟨⟨⟨na, nb, nc⟩, naCurve, nbCurve, ncCurve, naCall, nbCall, ncCall, naSpan, nbSpan, ncSpan⟩⟩

theorem scalarOutput_verifier_equation (key : Types.QueryKey) (values : QueryScalars)
    (witness h : Array Nat) (setup : IdealGroth16.Setup Fr)
    (a b c : Polynomial Fr) (tau : Fr) (domain : Nat)
    (relation : QapRelation key values witness h setup a b c tau domain)
    (qap : a.eval tau * b.eval tau - c.eval tau =
      (LeanCrypto.Proofs.FFT.coeffPolynomial h).eval tau * (tau ^ domain - 1)) (r s : Nat) :
    (scalarOutput key values witness h r s).a * (scalarOutput key values witness h r s).b =
      setup.alpha * setup.beta + setup.publicIC * setup.gamma +
        (scalarOutput key values witness h r s).c * setup.delta := by
  rw [scalarOutput_eq_ideal key values witness h setup a b c tau domain relation qap r s,
    IdealGroth16.output_canonical_c, div_mul_cancel₀ _ setup.delta_ne_zero]
  unfold IdealGroth16.Setup.kappa
  ring

end LeanCrypto.Proofs.NativeVerifier
#print axioms LeanCrypto.Proofs.NativeVerifier.scalarG1_injective
#print axioms LeanCrypto.Proofs.NativeVerifier.normalizeG1_scalar
#print axioms LeanCrypto.Proofs.NativeVerifier.normalizeG2_scalar
#print axioms LeanCrypto.Proofs.NativeVerifier.construction_normalized
#print axioms LeanCrypto.Proofs.NativeVerifier.scalarOutput_verifier_equation
