import TornadoProofs.Witness.ReferenceWindowGroup
import TornadoProofs.Witness.ReferenceWeights

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open LeanCrypto.Proofs.BabyJubjubWindows

abbrev GroupFrame (G : Type) := MProd (Option G) (MProd G G)

def groupStep {G : Type} [AddCommGroup G] (bits : Nat → Nat) (offset index : Nat)
    (frame : GroupFrame G) : GroupFrame G :=
  let base := if index = 0 then frame.2.1 else 2 • (2 • frame.2.2)
  let selected := digitAt bits offset index • base
  let previous := frame.1.getD 0
  ⟨some (previous+selected),base,8 • base⟩

def weightedFrame {G : Type} [AddCommGroup G] (bits : Nat → Nat) (offset : Nat)
    (base : G) (count : Nat) : GroupFrame G :=
  if count = 0 then ⟨none,base,base⟩ else
    ⟨some (windowValue (digits bits offset count) • base),
      (32 : Int)^(count-1) • base,8 • ((32 : Int)^(count-1) • base)⟩

theorem groupStep_weighted {G : Type} [AddCommGroup G]
    (bits : Nat → Nat) (offset index : Nat) (base : G) :
    groupStep bits offset index (weightedFrame bits offset base index)=weightedFrame bits offset base (index+1) := by
  by_cases zero : index=0
  · subst index
    simp [groupStep,weightedFrame,digits,digitAt,windowValue,List.range']
  · have positive : 0 < index := Nat.pos_of_ne_zero zero
    have exponent : index-1+1=index := by omega
    have advance := advance_weight base (index-1)
    rw [exponent] at advance
    simp only [groupStep,weightedFrame,if_neg zero,if_neg (by omega : index+1≠0),Option.getD_some,
      Nat.add_sub_cancel]
    rw [advance,←prefix_group_succ]

theorem groupFold_weighted {G : Type} [AddCommGroup G]
    (bits : Nat → Nat) (offset count : Nat) (base : G) :
    (List.range' 0 count).foldl (fun frame index => groupStep bits offset index frame) ⟨none,base,base⟩=
      weightedFrame bits offset base count := by
  induction count with
  | zero => simp [weightedFrame]
  | succ count ih =>
    rw [show count+1=count+1 from rfl,←List.range'_append]
    simp only [Nat.one_mul,Nat.zero_add,List.foldl_append,ih,List.range'_one,List.foldl_cons,List.foldl_nil]
    exact groupStep_weighted bits offset count base

theorem group_segment_value {G : Type} [AddCommGroup G] [Inhabited G]
    (bits : Nat → Nat) (bitBound : ∀ position, bits position<2) (offset windows : Nat) (base : G)
    (positive : 0 < windows) :
    segmentWith (groupOps bits) offset windows base=
      .ok (windowValue (digits bits offset windows) • base) := by
  have windowEquation (start : Nat) (point : G) := group_window_nativeNibble bits start point
    (bitBound start) (bitBound (start+1)) (bitBound (start+2)) (bitBound (start+3))
  have okBind {α β : Type} (value : α) (next : α → Except String β) :
      ((Except.ok value : Except String α) >>= next)=next value := rfl
  unfold segmentWith
  simp only [groupOps,windowEquation]
  simp only [groupWindows,pure_bind,okBind,map_pure]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.div_one,Nat.add_sub_cancel]
  simp only [beq_iff_eq,show windows≠0 from Nat.ne_of_gt positive,↓reduceIte]
  trans (do
    let frame ← forIn (List.range' 0 windows) (⟨none,base,base⟩ : GroupFrame G)
      (fun index frame => pure (ForInStep.yield (groupStep bits offset index frame)))
    match frame.1 with
    | some result => pure result
    | none => throw "Pedersen reference has no segment result.")
  · congr 1
    · congr 1
      funext index frame
      by_cases zero : index=0
      all_goals cases accumulator : frame.1
      all_goals simp [groupStep,digitAt,zero,accumulator,two_nsmul]
    · funext frame
      cases frame.1 <;> rfl
  · rw [List.forIn_pure_yield_eq_foldl]
    simp only [pure_bind,groupFold_weighted,weightedFrame,
      if_neg (Nat.ne_of_gt positive)]
    rfl

theorem group_program_value {G : Type} [AddCommGroup G] [Inhabited G]
    (commitment nullifier : Nat → Nat) (commitmentBits : ∀ position,commitment position<2)
    (nullifierBits : ∀ position,nullifier position<2) (bases : Array G) (width : bases.size=3) :
    programWith (groupOps commitment) (groupOps nullifier) bases=.ok
      (windowValue (digits commitment 0 50) • bases[0]!+
        windowValue (digits commitment 200 50) • bases[1]!+
        windowValue (digits commitment 400 24) • bases[2]!,
       windowValue (digits nullifier 0 50) • bases[0]!+
        windowValue (digits nullifier 200 12) • bases[1]!) := by
  have okBind {α β : Type} (value : α) (next : α → Except String β) :
      ((Except.ok value : Except String α) >>= next)=next value := rfl
  have c50 (offset : Nat) (point : G) := group_segment_value commitment commitmentBits offset 50 point (by decide)
  have c24 (offset : Nat) (point : G) := group_segment_value commitment commitmentBits offset 24 point (by decide)
  have n50 (offset : Nat) (point : G) := group_segment_value nullifier nullifierBits offset 50 point (by decide)
  have n12 (offset : Nat) (point : G) := group_segment_value nullifier nullifierBits offset 12 point (by decide)
  unfold programWith
  simp only [width,bne_self_eq_false,Bool.false_eq_true,if_false,c50,c24,n50,n12,okBind]
  simp only [groupOps,pure_bind]
  rfl

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.groupStep_weighted
#print axioms TornadoProofs.Witness.PedersenReference.groupFold_weighted
#print axioms TornadoProofs.Witness.PedersenReference.group_segment_value
#print axioms TornadoProofs.Witness.PedersenReference.group_program_value
