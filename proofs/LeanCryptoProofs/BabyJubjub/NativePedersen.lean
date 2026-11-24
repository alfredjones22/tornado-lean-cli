import LeanCryptoProofs.BabyJubjub.NativeGenerator
import LeanCryptoProofs.BabyJubjub.NativeWindows
import LeanCryptoProofs.BabyJubjub.ChartInjective

open Lean Elab Term Meta
elab "unfoldNativePedersenPoint" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic1 fun goal => goal.deltaTarget (· ==
    mkPrivateNameCore `LeanCrypto.Pedersen `LeanCrypto.pedersenPoint)

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjub
open LeanCrypto.Proofs.BabyJubjubWindows

abbrev nativePedersenPoint (input : ByteArray) : Except String RawPoint :=
  (pedersenFieldPrivate LeanCrypto.pedersenPoint) input

abbrev nativeChunkAt (input : ByteArray) (index : Nat) : Nat :=
  nativeChunk (input.extract (index*25) (min ((index+1)*25) input.size))

def nativePointStep (input : ByteArray) (result : RawPoint) (index : Nat) : Except String RawPoint := do
  let point ← nativeGenerator index
  let scalar := nativeChunkAt input index
  if scalar == 0 || scalar >= (pedersenFieldPrivate LeanCrypto.subgroupOrder) then
    throw s!"Invalid Pedersen scalar for chunk {index}"
  return nativeAddPoints result (nativeScalarMul point scalar)

theorem nativePedersenPoint_source (input : ByteArray) :
    nativePedersenPoint input =
      (List.range' 0 ((input.size+24)/25)).foldlM (nativePointStep input) nativeIdentity := by
  unfold nativePedersenPoint
  unfoldNativePedersenPoint
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.div_one, Nat.add_sub_cancel, pure_bind, bind_pure]
  have folded := List.forIn_yield_eq_foldlM
    (l := List.range' 0 ((input.size+24)/25))
    (fun index result => nativePointStep input result index) (fun _ _ point => point) nativeIdentity
  have mapIdentity (computation : Except String RawPoint) : (fun point => point) <$> computation=computation := by
    cases computation <;> rfl
  simp only [mapIdentity] at folded
  rw [← folded]
  congr 1
  funext index result
  unfold nativePointStep
  simp only [map_bind, bind_pure_comp]
  congr 1
  funext point
  split <;> rfl

theorem nativeChunkAt_bounds (input : ByteArray) (index : Nat)
    (inside : index < (input.size+24)/25) :
    0 < nativeChunkAt input index ∧ nativeChunkAt input index < LeanCrypto.Proofs.BabyJubjubPrimes.subgroupOrder := by
  apply nativeChunk_bounds
  · simp only [ByteArray.size_extract]
    have division := Nat.div_mul_le_self (input.size+24) 25
    have indexBound : index * 25 < input.size := by omega
    omega
  · simp only [ByteArray.size_extract]
    omega

theorem nativePointStep_construct (input : ByteArray) (result point : RawPoint) (index : Nat)
    (generated : nativeGenerator index=.ok point)
    (bounded : 0 < nativeChunkAt input index ∧
      nativeChunkAt input index < LeanCrypto.Proofs.BabyJubjubPrimes.subgroupOrder) :
    nativePointStep input result index=.ok (nativeAddPoints result (nativeScalarMul point (nativeChunkAt input index))) := by
  unfold nativePointStep
  rw [generated]
  have notZero : nativeChunkAt input index≠0 := Nat.ne_of_gt bounded.1
  have below : ¬ nativeChunkAt input index ≥ (pedersenFieldPrivate LeanCrypto.subgroupOrder) :=
    Nat.not_le_of_gt bounded.2
  have okBind {α β : Type} (value : α) (next : α → Except String β) :
      ((Except.ok value : Except String α) >>= next)=next value := rfl
  have invalid : (nativeChunkAt input index == 0 || decide (nativeChunkAt input index ≥
      (pedersenFieldPrivate LeanCrypto.subgroupOrder)))=false := by simp [notZero,below]
  simp only [okBind,invalid,Bool.false_eq_true,if_false]
  rfl

theorem nativeFold_construct (input : ByteArray) (indices : List Nat) (generators : Nat → RawPoint)
    (generated : ∀ index ∈ indices, nativeGenerator index=.ok (generators index))
    (valid : ∀ index ∈ indices, Admissible (generators index))
    (bounded : ∀ index ∈ indices, 0 < nativeChunkAt input index ∧
      nativeChunkAt input index < LeanCrypto.Proofs.BabyJubjubPrimes.subgroupOrder)
    (initial : RawPoint) (initialValid : Admissible initial) :
    ∃ result, indices.foldlM (nativePointStep input) initial=.ok result ∧ Admissible result ∧
      groupPoint result=groupPoint initial+
        (indices.map (fun index => nativeChunkAt input index • groupPoint (generators index))).sum := by
  induction indices generalizing initial with
  | nil => exact ⟨initial,rfl,initialValid,by simp⟩
  | cons index rest ih =>
    let next := nativeAddPoints initial (nativeScalarMul (generators index) (nativeChunkAt input index))
    have headValid := valid index (by simp)
    have nextValid : Admissible next := add_admissible _ _ initialValid
      (scalarMul_admissible _ _ headValid)
    obtain ⟨result,success,admitted,meaning⟩ := ih
      (fun i member => generated i (by simp [member]))
      (fun i member => valid i (by simp [member]))
      (fun i member => bounded i (by simp [member])) next nextValid
    refine ⟨result,?_,admitted,?_⟩
    · simp only [List.foldlM_cons,nativePointStep_construct input initial (generators index) index
        (generated index (by simp)) (bounded index (by simp))]
      exact success
    · rw [meaning]
      have nextMeaning : groupPoint next=groupPoint initial+nativeChunkAt input index • groupPoint (generators index) := by
        rw [add_groupPoint initial _ initialValid (scalarMul_admissible _ _ headValid),
          scalarMul_groupPoint _ _ headValid]
      rw [nextMeaning]
      simp only [List.map_cons,List.sum_cons]
      exact add_assoc _ _ _

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.nativePedersenPoint_source
#print axioms LeanCrypto.Proofs.BabyJubjub.nativeChunkAt_bounds
#print axioms LeanCrypto.Proofs.BabyJubjub.nativePointStep_construct
#print axioms LeanCrypto.Proofs.BabyJubjub.nativeFold_construct
