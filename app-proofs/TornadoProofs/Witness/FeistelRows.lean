import TornadoProofs.Witness.FeistelRowStep

set_option autoImplicit false

namespace TornadoProofs.Witness.Local

open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open TornadoProofs.Witness.Execution
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr

theorem prefixRows_sound (nodes : Array Node) (compiled : CompiledGraph) (constants : Array Nat)
    (stage : Feistel) (assignment : Nat → Fr) (constant : assignment 0 = 1)
    (rowValue : ∀ index, linearValue assignment (signalLinear nodes compiled index) = assignment index)
    (key : Nat) (keyValue : assignment stage.key = model key)
    (items : List Nat) (middle : ∀ round ∈ items, round < 219)
    (initial output : FeistelFrame Assignment) (rows : RowsFrame)
    (executed : items.foldlM (fun frame round => executeFeistelRound constants stage key round frame) initial = .ok output)
    (respects : Respects assignment output.state)
    (valid : SystemSatisfied assignment rows.snd.fst) (meaning : FrameMeaning assignment rows initial) :
    SystemSatisfied assignment
      (items.foldl (fun frame round => rowsRound nodes compiled constants stage round frame) rows).snd.fst ∧
      FrameMeaning assignment
        (items.foldl (fun frame round => rowsRound nodes compiled constants stage round frame) rows) output := by
  induction items generalizing initial output rows with
  | nil =>
    have equal : initial = output := Except.ok.inj executed
    subst output
    exact ⟨valid, meaning⟩
  | cons round rest ih =>
    rw [List.foldlM_cons] at executed
    obtain ⟨next, first, tail⟩ := bind_success (executeFeistelRound constants stage key round initial) _ output executed
    have extension : Extends next.state output.state := executeRounds_extends constants stage key rest next output
      ((executeRounds_fold constants stage key rest next).trans tail)
    have nextRespects := respects_backwards assignment next.state output.state extension respects
    obtain ⟨nextValid, nextMeaning⟩ := rowsRound_sound nodes compiled constants stage assignment constant rowValue
      key round keyValue initial next rows first nextRespects valid meaning
    have roundBound : round < 219 := middle round (by simp)
    have tailMiddle : ∀ index ∈ rest, index < 219 := by
      intro index member
      exact middle index (by simp only [List.mem_cons]; exact Or.inr member)
    have restSound := ih tailMiddle next output (rowsRound nodes compiled constants stage round rows)
      tail respects nextValid (nextMeaning roundBound)
    simpa only [List.foldl_cons] using restSound

/-- The actual frozen Feistel local-row generator emits equations satisfied
by the same independently interpreted public execution. No final constraint
checker or successful secret witness is assumed. -/
theorem feistelLocalSystem_sound (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (compiledGraph : CompiledGraph) (constants : Array Nat) (state after : SignalState) (stage : Feistel)
    (assignment : Nat → Fr) (constant : assignment 0 = 1)
    (rowValue : ∀ index, linearValue assignment (signalLinear resolver.nodes compiledGraph index) = assignment index)
    (compiled : compileFeistel resolver constants state stage = .ok after)
    (aliases : AliasesValid after values) (interpreted : SignalInterpretation after assignment values)
    (seed : LocalSystem) (valid : SystemSatisfied assignment seed) :
    SystemSatisfied assignment (feistelLocalSystem resolver.nodes compiledGraph constants seed stage) := by
  have executed := (compileFeistel_construct resolver inputs values denotes canonical constants state after stage compiled aliases).2
  rw [executeFeistel_source] at executed
  unfold executeFeistelBody at executed
  by_cases invalid : (constants.size != 220 || !stage.layoutValid (realize state values).values.size) = true
  · simp only [invalid, ↓reduceIte] at executed
    change (Except.error "MiMCFeistel round constants or signal layout are invalid." : Except String Assignment) = .ok (realize after values) at executed
    contradiction
  · have validFalse : (constants.size != 220 || !stage.layoutValid (realize state values).values.size) = false := Bool.eq_false_iff.mpr invalid
    simp only [validFalse, Bool.false_eq_true, ↓reduceIte] at executed
    change (do
      let key ← (realize state values).read stage.key
      let left ← (realize state values).read stage.leftInput
      let right ← (realize state values).read stage.rightInput
      let final ← ForIn.forIn (List.range 220) (FeistelFrame.mk (realize state values) left right)
        (executeRoundEffect constants stage key)
      pure final.state) = .ok (realize after values) at executed
    obtain ⟨key, keyRead, executed⟩ := bind_success ((realize state values).read stage.key) _ (realize after values) executed
    obtain ⟨left, leftRead, executed⟩ := bind_success ((realize state values).read stage.leftInput) _ (realize after values) executed
    obtain ⟨right, rightRead, executed⟩ := bind_success ((realize state values).read stage.rightInput) _ (realize after values) executed
    obtain ⟨final, rounds, executed⟩ := bind_success _ _ (realize after values) executed
    have finalState : final.state = realize after values := Except.ok.inj executed
    have finalRespects : Respects assignment final.state := by
      rw [finalState]
      exact signalInterpretation_assigned after assignment values interpreted
    let initial := FeistelFrame.mk (realize state values) left right
    have initialExtension := executeRounds_extends constants stage key (List.range 220) initial final rounds
    have initialRespects := respects_backwards assignment initial.state final.state initialExtension finalRespects
    have keyValue : assignment stage.key = model key :=
      initialRespects stage.key key (read_success_assigned (realize state values) stage.key key keyRead)
    let initialRows : RowsFrame := ⟨signalLinear resolver.nodes compiledGraph stage.leftInput,
      ⟨seed, signalLinear resolver.nodes compiledGraph stage.rightInput⟩⟩
    have initialMeaning : FrameMeaning assignment initialRows initial := by
      constructor
      · change linearValue assignment (signalLinear resolver.nodes compiledGraph stage.leftInput) = model left
        rw [rowValue]
        exact initialRespects stage.leftInput left (read_success_assigned (realize state values) stage.leftInput left leftRead)
      · change linearValue assignment (signalLinear resolver.nodes compiledGraph stage.rightInput) = model right
        rw [rowValue]
        exact initialRespects stage.rightInput right (read_success_assigned (realize state values) stage.rightInput right rightRead)
    rw [executeRounds_fold] at rounds
    have shape : List.range 220 = List.range 219 ++ [219] := List.range_succ
    rw [shape, List.foldlM_append] at rounds
    obtain ⟨beforeLast, beforeRounds, last⟩ := bind_success _ _ final rounds
    have lastExecuted : executeFeistelRound constants stage key 219 beforeLast = .ok final := by
      simpa only [List.foldlM_cons, List.foldlM_nil, bind_pure] using last
    have beforeRespects := respects_backwards assignment beforeLast.state final.state
      (executeRound_writes constants stage key 219 beforeLast final lastExecuted).1 finalRespects
    have allMiddle : ∀ index ∈ List.range 219, index < 219 := fun index member => List.mem_range.mp member
    obtain ⟨beforeValid, beforeMeaning⟩ := prefixRows_sound resolver.nodes compiledGraph constants stage assignment constant rowValue
      key keyValue (List.range 219) allMiddle initial beforeLast initialRows beforeRounds beforeRespects valid initialMeaning
    have lastValid := (rowsRound_sound resolver.nodes compiledGraph constants stage assignment constant rowValue key 219 keyValue
      beforeLast final ((List.range 219).foldl (fun frame round => rowsRound resolver.nodes compiledGraph constants stage round frame) initialRows)
      lastExecuted finalRespects beforeValid beforeMeaning).1
    have initialRowsEq : MProd.mk (signalLinear resolver.nodes compiledGraph stage.leftInput)
        (MProd.mk seed (signalLinear resolver.nodes compiledGraph stage.rightInput)) = initialRows := rfl
    rw [feistelLocalSystem_source, initialRowsEq, shape, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact lastValid

end TornadoProofs.Witness.Local

#print axioms TornadoProofs.Witness.Local.prefixRows_sound
#print axioms TornadoProofs.Witness.Local.feistelLocalSystem_sound
