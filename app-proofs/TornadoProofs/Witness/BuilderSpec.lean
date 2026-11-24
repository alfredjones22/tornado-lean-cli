import TornadoProofs.Witness.ReferenceControl
import TornadoProofs.Witness.FeistelSupport

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule

/-- A public compilation run preserves admitted earlier operations and gives
its returned node references the specified independent mathematical meaning. -/
def BuildSpec {A : Type} (invariant : Array Footprint → Prop) (action : Builder A) (post : A → Prop) : Prop :=
  ∀ initial result final,invariant initial → action initial=.ok (result,final) →
    invariant final ∧ post result

theorem buildSpec_pure {A : Type} (invariant : Array Footprint → Prop) (result : A)
    (post : A → Prop) (holds : post result) : BuildSpec invariant (pure result) post := by
  intro initial output final admitted compiled
  change Except.ok (result,initial)=.ok (output,final) at compiled
  have equal := Except.ok.inj compiled
  cases equal
  exact ⟨admitted,holds⟩

theorem buildSpec_bind {A B : Type} (invariant : Array Footprint → Prop)
    (first : Builder A) (next : A → Builder B) (middle : A → Prop) (post : B → Prop)
    (firstSpec : BuildSpec invariant first middle)
    (nextSpec : ∀ result,middle result → BuildSpec invariant (next result) post) :
    BuildSpec invariant (first >>= next) post := by
  intro initial result final admitted compiled
  change (do let pair ← first initial; next pair.1 pair.2)=.ok (result,final) at compiled
  obtain ⟨pair,firstBuilt,nextBuilt⟩ := TornadoProofs.Witness.Execution.bind_success _ _ _ compiled
  obtain ⟨preserved,meaning⟩ := firstSpec initial pair.1 pair.2 admitted firstBuilt
  exact nextSpec pair.1 meaning pair.2 result final preserved nextBuilt

theorem buildSpec_consequence {A : Type} (invariant : Array Footprint → Prop)
    (action : Builder A) (first second : A → Prop) (spec : BuildSpec invariant action first)
    (implies : ∀ result,first result → second result) : BuildSpec invariant action second := by
  intro initial result final admitted compiled
  obtain ⟨preserved,meaning⟩ := spec initial result final admitted compiled
  exact ⟨preserved,implies result meaning⟩

theorem buildSpec_forIn {A : Type} (invariant : Array Footprint → Prop) (body : Nat → A → Builder (ForInStep A))
    (relation : Nat → A → Prop) (start count : Nat) (initial : A) (initialMeaning : relation start initial)
    (stepSpec : ∀ index,start ≤ index → index < start+count → ∀ state,relation index state →
      BuildSpec invariant (body index state) (fun returned => ∃ next,returned=.yield next ∧ relation (index+1) next)) :
    BuildSpec invariant (forIn (List.range' start count) initial body) (relation (start+count)) := by
  induction count generalizing start initial with
  | zero => simpa only [List.range'_zero,List.forIn_nil,Nat.add_zero] using
      buildSpec_pure invariant initial (relation start) initialMeaning
  | succ count ih =>
    rw [List.range'_succ,List.forIn_cons]
    apply buildSpec_bind invariant (body start initial) _ _ _
      (stepSpec start (Nat.le_refl _) (by omega) initial initialMeaning)
    rintro returned ⟨next,rfl,nextMeaning⟩
    have restSpec := ih (start+1) next nextMeaning (by
      intro index lower upper state meaning
      exact stepSpec index (by omega) (by omega) state meaning)
    simpa only [Nat.add_assoc,Nat.add_comm 1 count] using restSpec

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.buildSpec_pure
#print axioms TornadoProofs.Witness.PedersenReference.buildSpec_bind
#print axioms TornadoProofs.Witness.PedersenReference.buildSpec_consequence
#print axioms TornadoProofs.Witness.PedersenReference.buildSpec_forIn
