import TornadoProofs.Witness.BuilderSpec
import TornadoProofs.Witness.ReferenceWindowGroup

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule

def TableMeaning {G : Type} [AddCommGroup G] (relation : PointRef → G → Prop)
    (base : G) (count : Nat) (table : Array PointRef) : Prop :=
  table.size=count ∧ ∀ index,index < count → relation table[index]! ((index+1) • base)

theorem tableMeaning_two {G : Type} [AddCommGroup G] (relation : PointRef → G → Prop)
    (base : G) (first second : PointRef) (one : relation first base) (two : relation second (2 • base)) :
    TableMeaning relation base 2 #[first,second] := by
  refine ⟨rfl,?_⟩
  intro index bound
  interval_cases index
  · change relation first ((1 : Nat) • base)
    simpa only [one_nsmul] using one
  · change relation second ((2 : Nat) • base)
    exact two

theorem tableMeaning_push {G : Type} [AddCommGroup G] (relation : PointRef → G → Prop)
    (base : G) (count : Nat) (table : Array PointRef) (point : PointRef)
    (meaning : TableMeaning relation base count table) (next : relation point ((count+1) • base)) :
    TableMeaning relation base (count+1) (table.push point) := by
  refine ⟨by simp only [Array.size_push,meaning.1],?_⟩
  intro index bound
  have width := meaning.1
  by_cases old : index < count
  · have within : index < table.size := by omega
    have pushed : index < (table.push point).size := by simp only [Array.size_push]; omega
    simpa only [getElem!_pos (table.push point) index pushed,Array.getElem_push_lt within,←getElem!_pos table index within]
      using meaning.2 index old
  · have last : index=count := by omega
    subst index
    rw [←meaning.1] at next ⊢
    simpa only [getElem!_pos (table.push point) table.size (by simp),Array.getElem_push_eq] using next

def tableAction (ops : WindowOps Builder PointRef Nat) (base twice : PointRef) :
    Builder (MProd PointRef (Array PointRef)) :=
  forIn (List.range' 2 6) ⟨twice,#[base,twice]⟩ fun _ frame => do
    let next ← ops.added base frame.1
    return .yield ⟨next,frame.2.push next⟩

theorem windowWith_tableAction (ops : WindowOps Builder PointRef Nat) (offset : Nat) (base : PointRef) :
    windowWith ops offset base = (do
      let twice ← ops.doubled base
      let frame ← tableAction ops base twice
      let b0 ← ops.bit offset
      let b1 ← ops.bit (offset+1)
      let b2 ← ops.bit (offset+2)
      let sign ← ops.bit (offset+3)
      let chosen ← ops.choose b0 b1 b2 frame.2
      let selected ← ops.signed chosen sign
      return (selected,frame.1)) := by
  unfold windowWith tableAction
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size]
  rfl

theorem tableAction_buildSpec {G : Type} [AddCommGroup G]
    (invariant : Array Footprint → Prop) (relation : PointRef → G → Prop)
    (ops : WindowOps Builder PointRef Nat) (base : G) (first twice : PointRef)
    (firstMeaning : relation first base) (twiceMeaning : relation twice (2 • base))
    (addition : ∀ index,2 ≤ index → index < 8 → ∀ previous,relation previous (index • base) →
      BuildSpec invariant (ops.added first previous) (fun result => relation result ((index+1) • base))) :
    BuildSpec invariant (tableAction ops first twice)
      (fun frame => relation frame.1 (8 • base) ∧ TableMeaning relation base 8 frame.2) := by
  unfold tableAction
  apply buildSpec_forIn invariant _
    (fun index (frame : MProd PointRef (Array PointRef)) => relation frame.1 (index • base) ∧ TableMeaning relation base index frame.2)
    2 6 _ ⟨twiceMeaning,tableMeaning_two relation base first twice firstMeaning twiceMeaning⟩
  intro index lower upper frame meaning
  apply buildSpec_bind invariant _ _ _ _ (addition index lower upper frame.1 meaning.1)
  intro next nextMeaning
  apply buildSpec_pure
  exact ⟨⟨next,frame.2.push next⟩,rfl,nextMeaning,tableMeaning_push relation base index frame.2 next meaning.2 nextMeaning⟩

theorem windowWith_buildSpec {G : Type} [AddCommGroup G]
    (invariant : Array Footprint → Prop) (relation : PointRef → G → Prop) (bitRelation : Nat → Nat → Prop)
    (ops : WindowOps Builder PointRef Nat) (bits : Nat → Nat) (offset : Nat) (base : G) (first : PointRef)
    (firstMeaning : relation first base)
    (doubling : BuildSpec invariant (ops.doubled first) (fun result => relation result (2 • base)))
    (addition : ∀ index,2 ≤ index → index < 8 → ∀ previous,relation previous (index • base) →
      BuildSpec invariant (ops.added first previous) (fun result => relation result ((index+1) • base)))
    (bitSpec : ∀ position,BuildSpec invariant (ops.bit position) (fun result => bitRelation result (bits position)))
    (selection : ∀ b0 b1 b2 table,bitRelation b0 (bits offset) → bitRelation b1 (bits (offset+1)) →
      bitRelation b2 (bits (offset+2)) → TableMeaning relation base 8 table →
      BuildSpec invariant (ops.choose b0 b1 b2 table) (fun result => relation result
        ((PedersenWindows.selectorIndex (bits offset) (bits (offset+1)) (bits (offset+2))+1) • base)))
    (signing : ∀ point sign,relation point
        ((PedersenWindows.selectorIndex (bits offset) (bits (offset+1)) (bits (offset+2))+1) • base) →
      bitRelation sign (bits (offset+3)) → BuildSpec invariant (ops.signed point sign)
        (fun result => relation result (PedersenWindows.selectedWindow base
          (bits offset) (bits (offset+1)) (bits (offset+2)) (bits (offset+3))))) :
    BuildSpec invariant (windowWith ops offset first) (fun result =>
      relation result.1 (PedersenWindows.selectedWindow base (bits offset) (bits (offset+1))
        (bits (offset+2)) (bits (offset+3))) ∧ relation result.2 (8 • base)) := by
  rw [windowWith_tableAction]
  apply buildSpec_bind invariant _ _ _ _ doubling
  intro twice twiceMeaning
  apply buildSpec_bind invariant _ _ _ _
    (tableAction_buildSpec invariant relation ops base first twice firstMeaning twiceMeaning addition)
  intro frame frameMeaning
  apply buildSpec_bind invariant _ _ _ _ (bitSpec offset)
  intro b0 b0Meaning
  apply buildSpec_bind invariant _ _ _ _ (bitSpec (offset+1))
  intro b1 b1Meaning
  apply buildSpec_bind invariant _ _ _ _ (bitSpec (offset+2))
  intro b2 b2Meaning
  apply buildSpec_bind invariant _ _ _ _ (bitSpec (offset+3))
  intro sign signMeaning
  apply buildSpec_bind invariant _ _ _ _ (selection b0 b1 b2 frame.2 b0Meaning b1Meaning b2Meaning frameMeaning.2)
  intro chosen chosenMeaning
  apply buildSpec_bind invariant _ _ _ _ (signing chosen sign chosenMeaning signMeaning)
  intro selected selectedMeaning
  exact buildSpec_pure invariant (selected,frame.1) _ ⟨selectedMeaning,frameMeaning.1⟩

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.tableMeaning_two
#print axioms TornadoProofs.Witness.PedersenReference.tableMeaning_push
#print axioms TornadoProofs.Witness.PedersenReference.windowWith_tableAction
#print axioms TornadoProofs.Witness.PedersenReference.tableAction_buildSpec
#print axioms TornadoProofs.Witness.PedersenReference.windowWith_buildSpec
