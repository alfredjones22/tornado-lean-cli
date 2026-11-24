import LeanCryptoProofs.AssemblyGroup
import LeanCryptoProofs.ScalarSubgroup
import LeanCryptoProofs.G2ScalarSubgroup

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanCrypto.Proofs.Groth16Assembly

open LeanCrypto.BN254 LeanCrypto.Groth16 LeanCrypto.Proofs.WindowedMSM
open scoped BigOperators
abbrev Fr := ZMod G1.scalarPrime
local instance : NeZero G1.scalarPrime := ⟨by decide⟩

noncomputable def scalarG1 : Fr →+ LeanCrypto.Proofs.BN254Group.curve.toAffine.Point :=
  ScalarSubgroup.scalarHom (g1 (G1.Jacobian.ofAffine G1.generator))
    LeanCrypto.Proofs.BN254Group.generator_order_annihilates
noncomputable abbrev scalarG2 := LeanCrypto.Proofs.BN254G2Group.scalarHom

/-- A setup relation is about decoded key queries in the proved groups.
It is not inferred from a file digest or from a successful proof check. -/
structure QueryScalars where
  alpha : Fr
  beta : Fr
  delta : Fr
  a : Nat → Fr
  b : Nat → Fr
  c : Nat → Fr
  h : Nat → Fr

structure KeySpan (key : Types.QueryKey) (values : QueryScalars) : Prop where
  alpha : g1 (decodedG1Value key.vkAlpha1) = scalarG1 values.alpha
  beta1 : g1 (decodedG1Value key.vkBeta1) = scalarG1 values.beta
  delta1 : g1 (decodedG1Value key.vkDelta1) = scalarG1 values.delta
  beta2 : g2 (decodedG2Value key.vkBeta2) = scalarG2 values.beta
  delta2 : g2 (decodedG2Value key.vkDelta2) = scalarG2 values.delta
  queryA : ∀ index, index < key.queryA.size →
    g1 (decodedG1Value key.queryA[index]!) = scalarG1 (values.a index)
  queryB1 : ∀ index, index < key.queryB1.size →
    g1 (decodedG1Value key.queryB1[index]!) = scalarG1 (values.b index)
  queryB2 : ∀ index, index < key.queryB2.size →
    g2 (decodedG2Value key.queryB2[index]!) = scalarG2 (values.b index)
  queryC : ∀ index, index < key.queryC.size →
    g1 (decodedG1Value key.queryC[index]!) = scalarG1 (values.c index)
  hExps : ∀ index, index < key.hExps.size →
    g1 (decodedG1Value key.hExps[index]!) = scalarG1 (values.h index)

def linearScalar (values : Nat → Fr) (scalars : Array Nat) (count : Nat) : Fr :=
  ∑ index ∈ Finset.range count, (scalars[index]! : Fr) * values index

theorem scalarG1_mul_nat (value : Nat) (scalar : Fr) :
    scalarG1 ((value : Fr) * scalar) = value • scalarG1 scalar :=
  ScalarSubgroup.scalarHom_mul_nat _ _ value scalar

theorem scalarG2_mul_nat (value : Nat) (scalar : Fr) :
    scalarG2 ((value : Fr) * scalar) = value • scalarG2 scalar :=
  ScalarSubgroup.scalarHom_mul_nat _ _ value scalar

theorem sumG1_scalar (points : Array Types.DecodedG1) (scalars : Array Nat)
    (values : Nat → Fr) (counts : points.size = scalars.size)
    (canonical : scalars.all (· < MSM.order) = true)
    (valid : ∀ point ∈ points, ValidG1 point)
    (span : ∀ index, index < points.size →
      g1 (decodedG1Value points[index]!) = scalarG1 (values index)) :
    g1 (sumG1 points scalars) = scalarG1 (linearScalar values scalars points.size) := by
  rw [sumG1_group points scalars counts canonical valid]
  unfold linearScalar
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index member
  rw [span index (Finset.mem_range.mp member), scalarG1_mul_nat]

theorem sumG2_scalar (points : Array Types.DecodedG2) (scalars : Array Nat)
    (values : Nat → Fr) (counts : points.size = scalars.size)
    (canonical : scalars.all (· < MSM.order) = true)
    (valid : ∀ point ∈ points, ValidG2 point)
    (span : ∀ index, index < points.size →
      g2 (decodedG2Value points[index]!) = scalarG2 (values index)) :
    g2 (sumG2 points scalars) = scalarG2 (linearScalar values scalars points.size) := by
  rw [sumG2_group points scalars counts canonical valid]
  unfold linearScalar
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index member
  rw [span index (Finset.mem_range.mp member), scalarG2_mul_nat]

theorem scalarG1_native (point : G1.Jacobian) (value : Nat) (scalar : Fr)
    (admitted : G1Admitted point) (span : g1 point = scalarG1 scalar) :
    g1 (point.scalarMul value) = scalarG1 ((value : Fr) * scalar) := by
  change LeanCrypto.Proofs.BN254Group.groupPoint (point.scalarMul value) = _
  change LeanCrypto.Proofs.BN254Group.groupPoint point = scalarG1 scalar at span
  rw [LeanCrypto.Proofs.BN254Group.scalarMul_groupPoint point value admitted, span,
    ← scalarG1_mul_nat]
  apply congrArg scalarG1
  change (((value % G1.scalarPrime : Nat) : Fr) * scalar) = (value : Fr) * scalar
  rw [ZMod.natCast_mod]

theorem scalarG2_native (point : G2.Jacobian) (value : Nat) (scalar : Fr)
    (admitted : G2Admitted point) (span : g2 point = scalarG2 scalar) :
    g2 (point.scalarMul value) = scalarG2 ((value : Fr) * scalar) := by
  change LeanCrypto.Proofs.BN254G2Group.groupPoint (point.scalarMul value) = _
  change LeanCrypto.Proofs.BN254G2Group.groupPoint point = scalarG2 scalar at span
  rw [LeanCrypto.Proofs.BN254G2Group.scalarMul_groupPoint point value admitted, span,
    scalarG2_mul_nat]

theorem minusRS_model (r s : Nat) :
    (((MSM.order - (r * s % MSM.order)) % MSM.order : Nat) : Fr) =
      -(r : Fr) * (s : Fr) := by
  change (((G1.scalarPrime - (r * s % G1.scalarPrime)) % G1.scalarPrime : Nat) : Fr) = _
  rw [ZMod.natCast_mod, Nat.cast_sub (Nat.mod_lt _ (by decide : 0 < G1.scalarPrime)).le,
    ZMod.natCast_self, ZMod.natCast_mod, Nat.cast_mul]
  ring

theorem extract_initial_span (points : Array Types.DecodedG1) (values : Nat → Fr)
    (span : ∀ index, index < points.size →
      g1 (decodedG1Value points[index]!) = scalarG1 (values index))
    (count : Nat) (bounded : count ≤ points.size) :
    ∀ index, index < (points.extract 0 count).size →
      g1 (decodedG1Value (points.extract 0 count)[index]!) = scalarG1 (values index) := by
  intro index bound
  have size : (points.extract 0 count).size = count := by simp [Nat.min_eq_left bounded]
  have original : index < points.size := by omega
  simpa only [getElem!_pos (points.extract 0 count) index bound, Array.getElem_extract,
    Nat.zero_add, getElem!_pos points index original] using span index original


end LeanCrypto.Proofs.Groth16Assembly

#print axioms LeanCrypto.Proofs.Groth16Assembly.scalarG1_mul_nat
#print axioms LeanCrypto.Proofs.Groth16Assembly.scalarG2_mul_nat
#print axioms LeanCrypto.Proofs.Groth16Assembly.sumG1_scalar
#print axioms LeanCrypto.Proofs.Groth16Assembly.sumG2_scalar
#print axioms LeanCrypto.Proofs.Groth16Assembly.scalarG1_native
#print axioms LeanCrypto.Proofs.Groth16Assembly.scalarG2_native
#print axioms LeanCrypto.Proofs.Groth16Assembly.minusRS_model
#print axioms LeanCrypto.Proofs.Groth16Assembly.extract_initial_span
