import LeanCryptoProofs.G1MSMConstruction
import LeanCryptoProofs.G2MSMConstruction
import LeanCryptoProofs.ScalarMulGroupLaw
import LeanCryptoProofs.G2ScalarMulGroupLaw

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanCrypto.Proofs.Groth16Assembly

open LeanCrypto.BN254 LeanCrypto.Groth16 LeanCrypto.Proofs.WindowedMSM

structure ValidKey (key : Types.QueryKey) : Prop where
  alpha : ValidG1 key.vkAlpha1
  beta1 : ValidG1 key.vkBeta1
  delta1 : ValidG1 key.vkDelta1
  beta2 : ValidG2 key.vkBeta2
  delta2 : ValidG2 key.vkDelta2
  queryA : ∀ point ∈ key.queryA, ValidG1 point
  queryB1 : ∀ point ∈ key.queryB1, ValidG1 point
  queryB2 : ∀ point ∈ key.queryB2, ValidG2 point
  queryC : ∀ point ∈ key.queryC, ValidG1 point
  hExps : ∀ point ∈ key.hExps, ValidG1 point

structure Dimensions (key : Types.QueryKey) (witness h : Array Nat) : Prop where
  nonempty : witness.isEmpty = false
  one : witness[0]? = some 1
  offset : key.nPublic + 1 ≤ witness.size
  queryA : key.queryA.size = witness.size
  queryB1 : key.queryB1.size = witness.size
  queryB2 : key.queryB2.size = witness.size
  queryC : key.queryC.size = witness.size - (key.nPublic + 1)
  hExps : h.size ≤ key.hExps.size

structure Canonical (witness h : Array Nat) (r s : Nat) : Prop where
  rBound : r < MSM.order
  sBound : s < MSM.order
  witness : witness.all (· < MSM.order) = true
  h : h.all (· < MSM.order) = true

def sumG1 (points : Array Types.DecodedG1) (scalars : Array Nat) : G1.Jacobian :=
  nativeWindowed (points.map decodedG1Value) scalars G1.Jacobian.infinity
    G1.Jacobian.add G1.Jacobian.double

def sumG2 (points : Array Types.DecodedG2) (scalars : Array Nat) : G2.Jacobian :=
  nativeWindowed (points.map decodedG2Value) scalars G2.Jacobian.infinity
    G2.Jacobian.add G2.Jacobian.double

/-- An explicit expression for the actual pure source, with decoding and
all error guards discharged from independent input conditions. -/
def construction (key : Types.QueryKey) (witness h : Array Nat) (r s : Nat) : Types.ProofPoints :=
  let a := ((sumG1 key.queryA witness).add (decodedG1Value key.vkAlpha1)).add
    ((decodedG1Value key.vkDelta1).scalarMul r)
  let b := ((sumG2 key.queryB2 witness).add (decodedG2Value key.vkBeta2)).add
    ((decodedG2Value key.vkDelta2).scalarMul s)
  let b1 := ((sumG1 key.queryB1 witness).add (decodedG1Value key.vkBeta1)).add
    ((decodedG1Value key.vkDelta1).scalarMul s)
  let cWitness := sumG1 key.queryC (witness.extract (key.nPublic + 1) witness.size)
  let hWitness := sumG1 (key.hExps.extract 0 h.size) h
  let minusRS := (MSM.order - (r * s % MSM.order)) % MSM.order
  ⟨a, b, ((((cWitness.add hWitness).add (a.scalarMul s)).add
    (b1.scalarMul r)).add ((decodedG1Value key.vkDelta1).scalarMul minusRS)),
    witness.extract 1 (key.nPublic + 1)⟩

theorem extract_valid {A : Type} (points : Array A) (property : A → Prop)
    (valid : ∀ point ∈ points, property point) (first last : Nat) :
    ∀ point ∈ points.extract first last, property point := by
  intro point member
  obtain ⟨index, bound, equal⟩ := Array.mem_extract_iff_getElem.mp member
  apply valid point
  rw [← equal]
  exact Array.getElem_mem (by omega)

theorem extract_canonical (values : Array Nat) (valid : values.all (· < MSM.order) = true)
    (first last : Nat) : (values.extract first last).all (· < MSM.order) = true := by
  apply Array.all_eq_true.mpr
  intro index bounded
  have member := Array.getElem_mem bounded
  have prop := extract_valid values (fun value => value < MSM.order)
    (fun value member => of_decide_eq_true ((Array.all_eq_true_iff_forall_mem.mp valid) value member)) first last
  exact decide_eq_true (prop _ member)

theorem assemble_construct (key : Types.QueryKey) (witness h : Array Nat) (r s : Nat)
    (valid : ValidKey key) (dimensions : Dimensions key witness h)
    (canonical : Canonical witness h r s) :
    MSM.assemble key witness h r s = .ok (construction key witness h r s) := by
  have privateShape : key.queryC.size = (witness.extract (key.nPublic + 1) witness.size).size := by
    simp [Array.size_extract, dimensions.queryC]
  have hShape : (key.hExps.extract 0 h.size).size = h.size := by
    simp [Array.size_extract, Nat.min_eq_left dimensions.hExps]
  have a := msmG1_construct key.queryA witness dimensions.queryA canonical.witness valid.queryA
  have b := msmG2_construct key.queryB2 witness dimensions.queryB2 canonical.witness valid.queryB2
  have b1 := msmG1_construct key.queryB1 witness dimensions.queryB1 canonical.witness valid.queryB1
  have c := msmG1_construct key.queryC _ privateShape
    (extract_canonical witness canonical.witness _ _) valid.queryC
  have hc := msmG1_construct _ h hShape canonical.h
    (extract_valid key.hExps ValidG1 valid.hExps _ _)
  have alpha := nativeG1Point_construct _ valid.alpha
  have delta1 := nativeG1Point_construct _ valid.delta1
  have beta1 := nativeG1Point_construct _ valid.beta1
  have beta2 := nativeG2Point_construct _ valid.beta2
  have delta2 := nativeG2Point_construct _ valid.delta2
  dsimp only [nativeG1Point] at alpha delta1 beta1
  dsimp only [nativeG2Point] at beta2 delta2
  unfold MSM.assemble
  simp only [dimensions.nonempty, dimensions.one, dimensions.queryA, dimensions.queryB1,
    dimensions.queryB2, dimensions.queryC,
    show ¬ key.nPublic + 1 > witness.size from Nat.not_lt.mpr dimensions.offset,
    show ¬ h.size > key.hExps.size from Nat.not_lt.mpr dimensions.hExps,
    canonical.witness, canonical.h, show ¬ r ≥ MSM.order from Nat.not_le.mpr canonical.rBound,
    show ¬ s ≥ MSM.order from Nat.not_le.mpr canonical.sBound,
    bne_self_eq_false, Bool.false_or, Bool.not_true, decide_false, Bool.false_eq_true, ↓reduceIte]
  simp only [a, b, b1, c, hc, alpha, delta1, beta1, beta2, delta2,
    bind, Except.bind, pure, Except.pure]
  rfl

end LeanCrypto.Proofs.Groth16Assembly

#print axioms LeanCrypto.Proofs.Groth16Assembly.extract_valid
#print axioms LeanCrypto.Proofs.Groth16Assembly.extract_canonical
#print axioms LeanCrypto.Proofs.Groth16Assembly.assemble_construct
