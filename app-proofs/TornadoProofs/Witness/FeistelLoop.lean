import TornadoProofs.Witness.FeistelRound

set_option autoImplicit false

namespace TornadoProofs.Witness.Execution

open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

def compileRoundEffect (resolver : Resolver) (constants : Array Nat) (stage : Feistel) (key : Nat)
    (round : Nat) (frame : FeistelFrame SignalState) : Except String (ForInStep (FeistelFrame SignalState)) := do
  let next ← compileFeistelRound resolver constants stage key round frame
  pure (.yield next)

def executeRoundEffect (constants : Array Nat) (stage : Feistel) (key : Nat)
    (round : Nat) (frame : FeistelFrame Assignment) : Except String (ForInStep (FeistelFrame Assignment)) := do
  let next ← executeFeistelRound constants stage key round frame
  pure (.yield next)

theorem compileRoundEffect_construct (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (constants : Array Nat) (stage : Feistel) (key round : Nat)
    (frame : FeistelFrame SignalState) (output : ForInStep (FeistelFrame SignalState))
    (compiled : compileRoundEffect resolver constants stage key round frame = .ok output)
    (terminal : AliasesValid (stepValue output).state values) :
    AliasesValid frame.state values ∧
      executeRoundEffect constants stage values[key]! round (realizeFrame frame values) =
        .ok (mapStep (fun frame => realizeFrame frame values) output) := by
  unfold compileRoundEffect at compiled
  obtain ⟨next, nextBuilt, compiled⟩ := bind_success
    (compileFeistelRound resolver constants stage key round frame) _ output compiled
  have equal : ForInStep.yield next = output := Except.ok.inj compiled
  subst output
  obtain ⟨initial, runtime⟩ := compileFeistelRound_construct resolver inputs values denotes canonical
    constants stage key round frame next nextBuilt terminal
  refine ⟨initial, ?_⟩
  simp only [executeRoundEffect, runtime, mapStep, bind, Except.bind, pure, Except.pure]

theorem range_forIn {State : Type} (length : Nat) (initial : State)
    (step : Nat → State → Except String (ForInStep State)) :
    ForIn.forIn [0:length] initial step = ForIn.forIn (List.range length) initial step := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.range_eq_range']

def compileFeistelBody (resolver : Resolver) (constants : Array Nat) (state : SignalState)
    (stage : Feistel) : Except String SignalState := do
  if constants.size != 220 || !stage.layoutValid state.slots.size then
    throw "Public witness DAG Feistel layout or constants are invalid."
  let key ← state.read stage.key
  let left ← state.read stage.leftInput
  let right ← state.read stage.rightInput
  let frame ← ForIn.forIn (List.range 220) (FeistelFrame.mk state left right)
    (compileRoundEffect resolver constants stage key)
  pure frame.state

def executeFeistelBody (constants : Array Nat) (state : Assignment) (stage : Feistel) : Except String Assignment := do
  if constants.size != 220 || !stage.layoutValid state.values.size then
    throw "MiMCFeistel round constants or signal layout are invalid."
  let key ← state.read stage.key
  let left ← state.read stage.leftInput
  let right ← state.read stage.rightInput
  let frame ← ForIn.forIn (List.range 220) (FeistelFrame.mk state left right)
    (executeRoundEffect constants stage key)
  pure frame.state

theorem compileFeistel_source (resolver : Resolver) (constants : Array Nat) (state : SignalState) (stage : Feistel) :
    compileFeistel resolver constants state stage = compileFeistelBody resolver constants state stage := by
  unfold compileFeistel compileFeistelBody
  simp only [range_forIn]
  rfl

theorem executeFeistel_source (constants : Array Nat) (state : Assignment) (stage : Feistel) :
    executeFeistel constants state stage = executeFeistelBody constants state stage := by
  unfold executeFeistel executeFeistelBody
  simp only [range_forIn]
  rfl

theorem compileFeistel_constants_size (resolver : Resolver) (constants : Array Nat)
    (state output : SignalState) (stage : Feistel)
    (compiled : compileFeistel resolver constants state stage = .ok output) : constants.size = 220 := by
  by_cases size : constants.size = 220
  · exact size
  · have invalid : (constants.size != 220 || !stage.layoutValid state.slots.size) = true := by simp [size]
    simp only [compileFeistel, invalid, ↓reduceIte] at compiled
    change (Except.error "Public witness DAG Feistel layout or constants are invalid." : Except String SignalState) = .ok output at compiled
    contradiction

/-- All 220 rounds construct actual checked VM execution from public DAG
compilation and independent DAG values. No native execution, final hash, or
R1CS success is an input hypothesis. -/
theorem compileFeistel_construct (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (constants : Array Nat) (state output : SignalState) (stage : Feistel)
    (compiled : compileFeistel resolver constants state stage = .ok output)
    (terminal : AliasesValid output values) :
    AliasesValid state values ∧
      executeFeistel constants (realize state values) stage = .ok (realize output values) := by
  rw [compileFeistel_source] at compiled
  unfold compileFeistelBody at compiled
  by_cases bad : (constants.size != 220 || !stage.layoutValid state.slots.size) = true
  · simp only [bad, ↓reduceIte] at compiled
    change (Except.error "Public witness DAG Feistel layout or constants are invalid." : Except String SignalState) = .ok output at compiled
    contradiction
  · have badFalse : (constants.size != 220 || !stage.layoutValid state.slots.size) = false := Bool.eq_false_iff.mpr bad
    simp only [badFalse, Bool.false_eq_true, ↓reduceIte] at compiled
    change (do
      let key ← state.read stage.key
      let left ← state.read stage.leftInput
      let right ← state.read stage.rightInput
      let frame ← ForIn.forIn (List.range 220) (FeistelFrame.mk state left right)
        (compileRoundEffect resolver constants stage key)
      pure frame.state) = .ok output at compiled
    obtain ⟨key, keyRead, compiled⟩ := bind_success (state.read stage.key) _ output compiled
    obtain ⟨left, leftRead, compiled⟩ := bind_success (state.read stage.leftInput) _ output compiled
    obtain ⟨right, rightRead, compiled⟩ := bind_success (state.read stage.rightInput) _ output compiled
    obtain ⟨final, rounds, compiled⟩ := bind_success
      (ForIn.forIn (List.range 220) (FeistelFrame.mk state left right)
        (compileRoundEffect resolver constants stage key)) _ output compiled
    have finalState : final.state = output := Except.ok.inj compiled
    have finalAliases : AliasesValid final.state values := by simpa only [finalState] using terminal
    have simulation := forIn_construct_from_public (List.range 220)
      (compileRoundEffect resolver constants stage key) (executeRoundEffect constants stage values[key]!)
      (fun frame => realizeFrame frame values) (fun frame => AliasesValid frame.state values)
      (fun round before next built admitted =>
        (compileRoundEffect_construct resolver inputs values denotes canonical constants stage key round before next built admitted).1)
      (fun round before next built admitted =>
        (compileRoundEffect_construct resolver inputs values denotes canonical constants stage key round before next built admitted).2)
      (FeistelFrame.mk state left right) final rounds finalAliases
    refine ⟨simulation.1, ?_⟩
    rw [executeFeistel_source]
    simp only [executeFeistelBody, realize_size, badFalse, Bool.false_eq_true, ↓reduceIte]
    rw [signalRead_realize state values stage.key key keyRead]
    rw [signalRead_realize state values stage.leftInput left leftRead]
    rw [signalRead_realize state values stage.rightInput right rightRead]
    change (do
      let frame ← ForIn.forIn (List.range 220) (realizeFrame (FeistelFrame.mk state left right) values)
        (executeRoundEffect constants stage values[key]!)
      pure frame.state) = .ok (realize output values)
    rw [simulation.2]
    simp only [bind, Except.bind, realizeFrame, pure, Except.pure, finalState]

end TornadoProofs.Witness.Execution

#print axioms TornadoProofs.Witness.Execution.compileRoundEffect_construct
#print axioms TornadoProofs.Witness.Execution.range_forIn
#print axioms TornadoProofs.Witness.Execution.compileFeistel_source
#print axioms TornadoProofs.Witness.Execution.executeFeistel_source
#print axioms TornadoProofs.Witness.Execution.compileFeistel_constants_size
#print axioms TornadoProofs.Witness.Execution.compileFeistel_construct
