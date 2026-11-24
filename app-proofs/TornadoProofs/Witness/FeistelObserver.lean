import TornadoProofs.Witness.FeistelLoop
import TornadoProofs.Witness.MiMCValues

set_option autoImplicit false

namespace TornadoProofs.Witness.Execution

open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.Groth16R1CS

theorem yield_forIn_foldlM {A State : Type} (items : List A) (initial : State)
    (step : A → State → Except String State) :
    ForIn.forIn items initial (fun item state => do
      let next ← step item state
      pure (ForInStep.yield next)) = items.foldlM (fun state item => step item state) initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn_cons, List.foldlM_cons]
    cases effect : step item initial with
    | error failure => simp only [bind, Except.bind]
    | ok next => simpa only [effect, bind, Except.bind, pure, Except.pure] using ih next

theorem foldlM_projection {A State Value : Type} (items : List A)
    (step : State → A → Except String State) (project : State → Value) (update : Value → A → Value)
    (preserves : ∀ state item next, step state item = .ok next → project next = update (project state) item)
    (initial output : State) (returned : items.foldlM step initial = .ok output) :
    project output = items.foldl update (project initial) := by
  induction items generalizing initial output with
  | nil =>
    have equal : initial = output := Except.ok.inj returned
    rw [← equal]
    rfl
  | cons item rest ih =>
    rw [List.foldlM_cons] at returned
    obtain ⟨next, first, tail⟩ := bind_success (step initial item) _ output returned
    rw [ih next output tail, List.foldl_cons, preserves initial item next first]

theorem executeRounds_fold (constants : Array Nat) (stage : Feistel) (key : Nat)
    (items : List Nat) (initial : FeistelFrame Assignment) :
    ForIn.forIn items initial (executeRoundEffect constants stage key) =
      items.foldlM (fun frame round => executeFeistelRound constants stage key round frame) initial :=
  yield_forIn_foldlM items initial (fun round frame => executeFeistelRound constants stage key round frame)

theorem executeRounds_pair (constants : Array Nat) (stage : Feistel) (key : Nat)
    (items : List Nat) (initial output : FeistelFrame Assignment)
    (returned : ForIn.forIn items initial (executeRoundEffect constants stage key) = .ok output) :
    framePair output = items.foldl (fun pair round => roundValues constants key round pair) (framePair initial) := by
  rw [executeRounds_fold] at returned
  exact foldlM_projection items (fun frame round => executeFeistelRound constants stage key round frame)
    framePair (fun pair round => roundValues constants key round pair)
    (fun frame round next effect => executeFeistelRound_pair constants stage key round frame next effect)
    initial output returned

theorem executeFinalRound_assigned (constants : Array Nat) (stage : Feistel) (key : Nat)
    (frame output : FeistelFrame Assignment)
    (returned : executeFeistelRound constants stage key 219 frame = .ok output) :
    Assigned output.state stage.leftOutput output.left ∧ Assigned output.state stage.rightOutput output.right := by
  unfold executeFeistelRound at returned
  obtain ⟨first, _, returned⟩ := bind_success _ _ output returned
  obtain ⟨second, _, returned⟩ := bind_success _ _ output returned
  simp only [Nat.lt_irrefl, ↓reduceIte] at returned
  obtain ⟨third, thirdBuilt, returned⟩ := bind_success _ _ output returned
  obtain ⟨fourth, fourthBuilt, returned⟩ := bind_success _ _ output returned
  have equal : FeistelFrame.mk fourth _ _ = output := Except.ok.inj returned
  subst output
  have left := write_success_preserves second third stage.leftOutput _ thirdBuilt
  have right := write_success_preserves third fourth stage.rightOutput _ fourthBuilt
  exact ⟨right.2.2 _ _ left.1, right.1⟩

theorem executeRounds_final_assigned (constants : Array Nat) (stage : Feistel) (key : Nat)
    (initial output : FeistelFrame Assignment)
    (returned : ForIn.forIn (List.range 220) initial (executeRoundEffect constants stage key) = .ok output) :
    Assigned output.state stage.leftOutput output.left ∧ Assigned output.state stage.rightOutput output.right := by
  rw [executeRounds_fold] at returned
  have shape : List.range 220 = List.range 219 ++ [219] := List.range_succ
  rw [shape, List.foldlM_append] at returned
  obtain ⟨before, _, tail⟩ := bind_success _ _ output returned
  have last : executeFeistelRound constants stage key 219 before = .ok output := by
    simpa only [List.foldlM_cons, List.foldlM_nil, bind_pure] using tail
  exact executeFinalRound_assigned constants stage key before output last

/-- Observable native MiMC outputs follow from actual VM round execution.
This postcondition is used after the separate public-DAG construction theorem
has produced execution, to discharge the native sponge equality check. -/
theorem executeFeistel_observer (constants : Array Nat) (state output : Assignment) (stage : Feistel)
    (key left right : Nat) (keyRead : state.read stage.key = .ok key)
    (leftRead : state.read stage.leftInput = .ok left) (rightRead : state.read stage.rightInput = .ok right)
    (keyBound : key < scalarPrime) (leftBound : left < scalarPrime) (rightBound : right < scalarPrime)
    (returned : executeFeistel constants state stage = .ok output) :
    ∃ pair : Nat × Nat, LeanCrypto.mimcPermutationWith constants left right key = .ok pair ∧
      output.read stage.leftOutput = .ok pair.1 ∧ output.read stage.rightOutput = .ok pair.2 := by
  rw [executeFeistel_source] at returned
  unfold executeFeistelBody at returned
  by_cases invalid : (constants.size != 220 || !stage.layoutValid state.values.size) = true
  · simp only [invalid, ↓reduceIte] at returned
    change (Except.error "MiMCFeistel round constants or signal layout are invalid." : Except String Assignment) = .ok output at returned
    contradiction
  · have validFalse : (constants.size != 220 || !stage.layoutValid state.values.size) = false := Bool.eq_false_iff.mpr invalid
    have size : constants.size = 220 := by
      have shape : (constants.size != 220) = false := (Bool.or_eq_false_iff.mp validFalse).1
      exact bne_eq_false_iff_eq.mp shape
    simp only [validFalse, Bool.false_eq_true, ↓reduceIte, keyRead, leftRead, rightRead, bind, Except.bind] at returned
    change (do
      let frame ← ForIn.forIn (List.range 220) (FeistelFrame.mk state left right)
        (executeRoundEffect constants stage key)
      pure frame.state) = .ok output at returned
    obtain ⟨final, rounds, returned⟩ := bind_success _ _ output returned
    have outputState : final.state = output := Except.ok.inj returned
    have pairValue := executeRounds_pair constants stage key (List.range 220)
      (FeistelFrame.mk state left right) final rounds
    have assigned := executeRounds_final_assigned constants stage key (FeistelFrame.mk state left right) final rounds
    refine ⟨(final.left, final.right), ?_, ?_, ?_⟩
    · rw [native_permutation_construct constants size, Nat.mod_eq_of_lt keyBound,
        Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound]
      change (Except.ok (let pair := permutationValues constants key left right; (pair.fst, pair.snd)) : Except String (Nat × Nat)) = _
      have pairEq : framePair final = permutationValues constants key left right := pairValue
      rw [← pairEq]
      rfl
    · rw [← outputState]
      exact assigned_read final.state stage.leftOutput final.left assigned.1
    · rw [← outputState]
      exact assigned_read final.state stage.rightOutput final.right assigned.2

end TornadoProofs.Witness.Execution

#print axioms TornadoProofs.Witness.Execution.yield_forIn_foldlM
#print axioms TornadoProofs.Witness.Execution.foldlM_projection
#print axioms TornadoProofs.Witness.Execution.executeRounds_fold
#print axioms TornadoProofs.Witness.Execution.executeRounds_pair
#print axioms TornadoProofs.Witness.Execution.executeFinalRound_assigned
#print axioms TornadoProofs.Witness.Execution.executeRounds_final_assigned
#print axioms TornadoProofs.Witness.Execution.executeFeistel_observer
