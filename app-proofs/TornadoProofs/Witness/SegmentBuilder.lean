import TornadoProofs.Witness.WindowBuilder
import TornadoProofs.Witness.ReferenceWeights

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule
open LeanCrypto.Proofs.BabyJubjubWindows

theorem buildSpec_map {A B : Type} (invariant : Array Footprint → Prop) (action : Builder A)
    (post : A → Prop) (transform : A → B) (spec : BuildSpec invariant action post) :
    BuildSpec invariant (transform <$> action) (fun output => ∃ input,output=transform input ∧ post input) := by
  rw [←bind_pure_comp]
  apply buildSpec_bind invariant _ _ _ _ spec
  intro input meaning
  exact buildSpec_pure invariant (transform input) _ ⟨input,rfl,meaning⟩

theorem buildSpec_forIn_zero {A : Type} (invariant : Array Footprint → Prop)
    (body : Nat → A → Builder (ForInStep A)) (relation : Nat → A → Prop)
    (count : Nat) (initial : A) (meaning : relation 0 initial)
    (stepSpec : ∀ index,index < count → ∀ state,relation index state →
      BuildSpec invariant (body index state) (fun returned => ∃ next,returned=.yield next ∧ relation (index+1) next)) :
    BuildSpec invariant (forIn (List.range' 0 count) initial body) (relation count) := by
  have constructed := buildSpec_forIn invariant body relation 0 count initial meaning
    (fun index _ upper state stateMeaning => stepSpec index (by omega) state stateMeaning)
  simpa only [Nat.zero_add] using constructed

abbrev SegmentFrame := MProd (Option PointRef) (MProd PointRef PointRef)

def SegmentMeaning {G : Type} [AddCommGroup G] (relation : PointRef → G → Prop)
    (bits : Nat → Nat) (offset : Nat) (base : G) (index : Nat) (frame : SegmentFrame) : Prop :=
  if index=0 then frame.1=none ∧ relation frame.2.1 base ∧ relation frame.2.2 base else
    ∃ accumulator,frame.1=some accumulator ∧ relation accumulator (windowValue (digits bits offset index) • base) ∧
      relation frame.2.1 ((32 : Int)^(index-1) • base) ∧
      relation frame.2.2 (8 • ((32 : Int)^(index-1) • base))

theorem segmentWith_buildSpec {G : Type} [AddCommGroup G]
    (invariant : Array Footprint → Prop) (edwards montgomery : PointRef → G → Prop)
    (ops : ReferenceOps Builder PointRef PointRef Nat) (bits : Nat → Nat)
    (offset windows : Nat) (base : G) (first : PointRef) (positive : 0 < windows)
    (conversion : BuildSpec invariant (ops.toMontgomery first) (fun result => montgomery result base))
    (advance16 : ∀ index,0 < index → index < windows → ∀ previous,
      montgomery previous (8 • ((32 : Int)^(index-1) • base)) →
      BuildSpec invariant (ops.windows.doubled previous)
        (fun result => montgomery result (16 • ((32 : Int)^(index-1) • base))))
    (advance32 : ∀ index,0 < index → index < windows → ∀ previous,
      montgomery previous (16 • ((32 : Int)^(index-1) • base)) →
      BuildSpec invariant (ops.windows.doubled previous)
        (fun result => montgomery result ((32 : Int)^index • base)))
    (window : ∀ index,index < windows → ∀ point,montgomery point ((32 : Int)^index • base) →
      BuildSpec invariant (windowWith ops.windows (offset+4*index) point) (fun result =>
        montgomery result.1 (digitAt bits offset index • ((32 : Int)^index • base)) ∧
        montgomery result.2 (8 • ((32 : Int)^index • base))))
    (addition : ∀ index,0 < index → index < windows → ∀ previous selected,
      montgomery previous (windowValue (digits bits offset index) • base) →
      montgomery selected (digitAt bits offset index • ((32 : Int)^index • base)) →
      BuildSpec invariant (ops.windows.added previous selected)
        (fun result => montgomery result (windowValue (digits bits offset (index+1)) • base)))
    (normalization : ∀ point,montgomery point (windowValue (digits bits offset windows) • base) →
      BuildSpec invariant (ops.toEdwards point)
        (fun result => edwards result (windowValue (digits bits offset windows) • base))) :
    BuildSpec invariant (segmentWith ops offset windows first)
      (fun result => edwards result (windowValue (digits bits offset windows) • base)) := by
  have notEmpty : (windows==0)=false := by simp [Nat.ne_of_gt positive]
  unfold segmentWith
  simp only [notEmpty,Bool.false_eq_true,if_false,pure_bind]
  apply buildSpec_bind invariant _ _ _ _ conversion
  intro converted convertedMeaning
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.div_one,Nat.add_sub_cancel]
  apply buildSpec_bind invariant _ _ (SegmentMeaning montgomery bits offset base windows) _
  · apply buildSpec_forIn_zero invariant _ (SegmentMeaning montgomery bits offset base) windows _
      (by exact ⟨rfl,convertedMeaning,convertedMeaning⟩)
    intro index upper frame meaning
    by_cases zero : index=0
    · subst index
      change frame.1=none ∧ montgomery frame.2.1 base ∧ montgomery frame.2.2 base at meaning
      simp only [bne_self_eq_false,Bool.false_eq_true,if_false]
      have firstWindow := window 0 upper frame.2.1 (by simpa using meaning.2.1)
      apply buildSpec_bind invariant _ _ _ _ firstWindow
      intro pair pairMeaning
      simp only [meaning.1]
      apply buildSpec_pure
      refine ⟨⟨some pair.1,frame.2.1,pair.2⟩,rfl,?_⟩
      simp only [SegmentMeaning,show (0+1 : Nat)≠0 from by decide,if_false,Nat.add_sub_cancel,pow_zero,one_zsmul]
      refine ⟨pair.1,rfl,?_,meaning.2.1,?_⟩
      · have prefixEq := prefix_group_succ base bits offset 0
        simp only [show windowValue (digits bits offset 0)=0 from rfl,zero_zsmul,zero_add,pow_zero,one_zsmul] at prefixEq
        rw [prefixEq]
        simpa only [pow_zero,one_zsmul] using pairMeaning.1
      · simpa only [pow_zero,one_zsmul] using pairMeaning.2
    · have indexPositive : 0 < index := Nat.pos_of_ne_zero zero
      simp only [SegmentMeaning,if_neg zero] at meaning
      obtain ⟨previous,accumulator,previousMeaning,nextMeaning,eightMeaning⟩ := meaning
      have nonzero : (index != 0)=true := by simp [zero]
      simp only [nonzero,if_true]
      apply buildSpec_bind invariant _ _ _ _ (advance16 index indexPositive upper frame.2.2 eightMeaning)
      intro sixteen sixteenMeaning
      apply buildSpec_bind invariant _ _ _ _ (advance32 index indexPositive upper sixteen sixteenMeaning)
      intro next nextMeaning
      apply buildSpec_bind invariant _ _ _ _ (window index upper next nextMeaning)
      intro pair pairMeaning
      simp only [accumulator]
      apply buildSpec_bind invariant _ _ _ _
        (buildSpec_map invariant _ _ some (addition index indexPositive upper previous pair.1 previousMeaning pairMeaning.1))
      rintro returned ⟨result,rfl,resultMeaning⟩
      apply buildSpec_pure
      refine ⟨⟨some result,next,pair.2⟩,rfl,?_⟩
      simp only [SegmentMeaning,if_neg (by omega : index+1≠0),Nat.add_sub_cancel]
      exact ⟨result,rfl,resultMeaning,nextMeaning,pairMeaning.2⟩
  · intro frame meaning
    simp only [SegmentMeaning,if_neg (Nat.ne_of_gt positive)] at meaning
    obtain ⟨result,accumulator,resultMeaning,_,_⟩ := meaning
    simp only [accumulator]
    exact normalization result resultMeaning

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.buildSpec_map
#print axioms TornadoProofs.Witness.PedersenReference.segmentWith_buildSpec
#print axioms TornadoProofs.Witness.PedersenReference.buildSpec_forIn_zero
