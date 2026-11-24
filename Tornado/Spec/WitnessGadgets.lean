import Tornado.Protocol.WitnessVM

set_option autoImplicit false

/-! Constructive local obligations for the actual pinned witness evaluator.
No theorem assumes that the final R1CS checker accepted an assignment. -/
namespace Tornado.Protocol.WitnessVM

open Tornado.Protocol.Groth16R1CS

def Assigned (state : Assignment) (index value : Nat) : Prop :=
  state.values[index]? = some (some value)

def Extends (before after : Assignment) : Prop :=
  after.values.size = before.values.size ∧
  ∀ index value, Assigned before index value → Assigned after index value

theorem assigned_read (state : Assignment) (index value : Nat)
    (assigned : Assigned state index value) : state.read index = .ok value := by
  have bound : index < state.values.size := by
    exact of_getElem?_eq_some (c := state.values) (i := index) assigned
  have slot : state.values[index]! = some value := by
    rw [getElem!_pos state.values index bound]
    exact Option.some.inj ((Array.getElem?_eq_getElem bound).symm.trans assigned)
  simp [Assignment.read, Nat.not_le_of_lt bound, slot, bind, Except.bind, pure, Except.pure]

theorem extends_refl (state : Assignment) : Extends state state := by
  exact ⟨rfl, fun _ _ h => h⟩

theorem extends_trans {first second third : Assignment}
    (left : Extends first second) (right : Extends second third) :
    Extends first third := by
  exact ⟨right.1.trans left.1, fun index value h => right.2 index value (left.2 index value h)⟩

theorem write_construct (state : Assignment) (index value : Nat)
    (indexBound : index < state.values.size) (valueBound : value < scalarPrime)
    (compatible : state.values[index]! = none ∨ state.values[index]! = some value) :
    ∃ next, state.write index value = .ok next ∧
      Assigned next index value ∧ Extends state next := by
  rcases compatible with empty | same
  · refine ⟨⟨state.values.set! index (some value)⟩, ?_, ?_, ?_⟩
    · simp [Assignment.write, Nat.not_le_of_lt indexBound, Nat.not_le_of_lt valueBound, empty, bind, Except.bind, pure, Except.pure]
    · simp [Assigned, indexBound]
    · refine ⟨by simp, ?_⟩
      intro other prior existing
      by_cases eq : index = other
      · subst other
        have eqNone : state.values[index]? = some none := by
          simpa [Array.getElem?_eq_getElem indexBound, getElem!_pos state.values index indexBound] using
            congrArg some empty
        rw [Assigned, eqNone] at existing
        cases existing
      · simpa [Assigned, eq] using existing
  · refine ⟨state, ?_, ?_, extends_refl state⟩
    · simp [Assignment.write, Nat.not_le_of_lt indexBound, Nat.not_le_of_lt valueBound, same, bind, Except.bind, pure, Except.pure]
    · simpa [Assigned, Array.getElem?_eq_getElem indexBound, getElem!_pos state.values index indexBound] using
        congrArg some same

theorem write_success_preserves (state next : Assignment) (index value : Nat)
    (success : state.write index value = .ok next) :
    Assigned next index value ∧ Extends state next := by
  by_cases inBounds : index >= state.values.size
  · simp [Assignment.write, inBounds, bind, Except.bind] at success
  by_cases valueBound : value >= scalarPrime
  · simp [Assignment.write, inBounds, valueBound, bind, Except.bind, pure, Except.pure] at success
  have compatible : state.values[index]! = none ∨ state.values[index]! = some value := by
    cases slot : state.values[index]! with
    | none => exact Or.inl rfl
    | some prior =>
      by_cases eq : prior = value
      · simp [eq]
      · simp [Assignment.write, inBounds, valueBound, slot, eq, bind, Except.bind,
          pure, Except.pure] at success
  rcases write_construct state index value (by omega) (by omega) compatible with
    ⟨made, written, spec⟩
  have eq : made = next := Except.ok.inj (written.symm.trans success)
  subst made
  exact spec

theorem assigned_slot (state : Assignment) (index value : Nat)
    (assigned : Assigned state index value) : state.values[index]! = some value := by
  have bound := of_getElem?_eq_some (c := state.values) (i := index) assigned
  rw [getElem!_pos state.values index bound]
  exact Option.some.inj ((Array.getElem?_eq_getElem bound).symm.trans assigned)

theorem write_success_other (state next : Assignment) (index value other : Nat)
    (success : state.write index value = .ok next) (different : index ≠ other) :
    next.values[other]! = state.values[other]! := by
  by_cases inBounds : index >= state.values.size
  · simp [Assignment.write, inBounds, bind, Except.bind] at success
  by_cases valueBound : value >= scalarPrime
  · simp [Assignment.write, inBounds, valueBound, bind, Except.bind, pure, Except.pure] at success
  cases slot : state.values[index]! with
  | none =>
    simp [Assignment.write, inBounds, valueBound, slot, bind, Except.bind,
      pure, Except.pure] at success
    subst next
    simp only [getElem!_def,
      Array.getElem?_setIfInBounds_ne different]
  | some prior =>
    by_cases eq : prior = value
    · simp [Assignment.write, inBounds, valueBound, slot, eq, bind, Except.bind,
        pure, Except.pure] at success
      subst next
      rfl
    · simp [Assignment.write, inBounds, valueBound, slot, eq, bind, Except.bind, pure, Except.pure] at success

def CompatibleWrites (state : Assignment) (writes : List (Nat × Nat)) : Prop :=
  ∀ index value, (index, value) ∈ writes →
    index < state.values.size ∧ value < scalarPrime ∧
    (state.values[index]! = none ∨ state.values[index]! = some value)

def ConsistentWrites (writes : List (Nat × Nat)) : Prop :=
  ∀ index first second, (index, first) ∈ writes → (index, second) ∈ writes → first = second

/-- This is precisely the `for`/`Assignment.write` loop used by the VM, with
its input pairs made explicit for induction. -/
def runAssignments (state : Assignment) (writes : List (Nat × Nat)) :
    Except String Assignment :=
  forIn writes state fun (index, value) current => do
    let next ← current.write index value
    pure (.yield next)

theorem runAssignments_construct (writes : List (Nat × Nat)) (state : Assignment)
    (compatible : CompatibleWrites state writes) (consistent : ConsistentWrites writes) :
    ∃ next, runAssignments state writes = .ok next ∧ Extends state next ∧
      ∀ index value, (index, value) ∈ writes → Assigned next index value := by
  induction writes generalizing state with
  | nil =>
    exact ⟨state, rfl, extends_refl state, by simp⟩
  | cons head rest ih =>
    rcases head with ⟨index, value⟩
    have headCompatible := compatible index value (by simp)
    rcases write_construct state index value headCompatible.1 headCompatible.2.1
      headCompatible.2.2 with ⟨middle, written, headAssigned, headExtends⟩
    have restCompatible : CompatibleWrites middle rest := by
      intro other prior member
      have original := compatible other prior (by simp [member])
      refine ⟨by simpa [headExtends.1] using original.1, original.2.1, ?_⟩
      by_cases eq : index = other
      · subst other
        have valuesEqual := consistent index value prior (by simp) (by simp [member])
        subst prior
        exact Or.inr (assigned_slot middle index value headAssigned)
      · rw [write_success_other state middle index value other written eq]
        exact original.2.2
    have restConsistent : ConsistentWrites rest := by
      intro other first second left right
      exact consistent other first second (by simp [left]) (by simp [right])
    rcases ih middle restCompatible restConsistent with
      ⟨next, tailWritten, tailExtends, tailAssigned⟩
    refine ⟨next, ?_, extends_trans headExtends tailExtends, ?_⟩
    · simpa only [runAssignments, List.forIn_cons, written, bind, Except.bind,
        pure, Except.pure] using tailWritten
    · intro other prior member
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        exact tailExtends.2 index value headAssigned
      · exact tailAssigned other prior member

def bitSum (width value : Nat) : Nat :=
  ((List.range width).map fun bit => 2 ^ bit * bitValue value bit).sum

theorem bitSum_mod (width value : Nat) : bitSum width value = value % 2 ^ width := by
  induction width with
  | zero => simp [bitSum, Nat.mod_one]
  | succ width ih =>
    simp only [bitSum, List.range_succ, List.map_append, List.sum_append,
      List.map_singleton, List.sum_cons, List.sum_nil, Nat.add_zero]
    change bitSum width value + 2 ^ width * bitValue value width = value % 2 ^ (width + 1)
    rw [ih, Nat.pow_succ, Nat.mod_mul]
    rfl

theorem bitSum_reconstruct (width value : Nat) (bound : value < 2 ^ width) :
    bitSum width value = value := by
  rw [bitSum_mod, Nat.mod_eq_of_lt bound]

theorem bitValue_idempotent (value bit : Nat) :
    bitValue value bit * bitValue value bit = bitValue value bit := by
  have bound := bitValue_is_binary value bit
  have cases : bitValue value bit = 0 ∨ bitValue value bit = 1 := by omega
  rcases cases with eq | eq <;> simp [eq]

theorem dualMux_construct (selector input0 input1 : Nat) (binary : selector < 2) :
    let output := dualMuxValues selector input0 input1
    selector * selector = selector ∧
    output.1 + selector * input0 = input0 + selector * input1 ∧
    output.2 + selector * input1 = input1 + selector * input0 := by
  have cases : selector = 0 ∨ selector = 1 := by omega
  rcases cases with eq | eq <;> subst selector <;>
    simp [dualMuxValues, Nat.add_comm]

theorem bitValue_fr_boolean (value bit : Nat) :
    bitValue value bit * ((bitValue value bit + scalarPrime - 1) % scalarPrime) % scalarPrime = 0 := by
  have bounded := bitValue_is_binary value bit
  have cases : bitValue value bit = 0 ∨ bitValue value bit = 1 := by omega
  rcases cases with eq | eq
  · simp [eq]
  · rw [eq]
    have subtract : 1 + scalarPrime - 1 = scalarPrime := by omega
    simp [subtract]

theorem modular_difference_add (left right : Nat) (rightBound : right < scalarPrime) :
    ((left + scalarPrime - right) % scalarPrime + right) % scalarPrime = left % scalarPrime := by
  rw [Nat.mod_add_mod, Nat.sub_add_cancel (show right ≤ left + scalarPrime by omega)]
  simp

/-- These are the exact modular Circom DualMux equations, with both native
input values independently bounded in Fr. No primality assumption is used. -/
theorem dualMux_fr_construct (selector input0 input1 : Nat) (binary : selector < 2)
    (input0Bound : input0 < scalarPrime) (input1Bound : input1 < scalarPrime) :
    let output := dualMuxValues selector input0 input1
    selector * ((1 + scalarPrime - selector) % scalarPrime) % scalarPrime = 0 ∧
    (((input1 + scalarPrime - input0) % scalarPrime) * selector + input0) % scalarPrime = output.1 ∧
    (((input0 + scalarPrime - input1) % scalarPrime) * selector + input1) % scalarPrime = output.2 := by
  have cases : selector = 0 ∨ selector = 1 := by omega
  rcases cases with eq | eq <;> subst selector
  · simp [dualMuxValues, Nat.mod_eq_of_lt input0Bound, Nat.mod_eq_of_lt input1Bound]
  · have subtract : 1 + scalarPrime - 1 = scalarPrime := by omega
    change 1 * ((1 + scalarPrime - 1) % scalarPrime) % scalarPrime = 0 ∧
      (((input1 + scalarPrime - input0) % scalarPrime) * 1 + input0) % scalarPrime = input1 ∧
      (((input0 + scalarPrime - input1) % scalarPrime) * 1 + input1) % scalarPrime = input0
    simp only [subtract, Nat.mod_self, Nat.one_mul, Nat.zero_mod, Nat.mul_one, true_and]
    rw [modular_difference_add input1 input0 input0Bound,
      modular_difference_add input0 input1 input1Bound,
      Nat.mod_eq_of_lt input0Bound, Nat.mod_eq_of_lt input1Bound]
    exact ⟨rfl, rfl⟩

theorem runAssignments_map (indices : List Nat) (state : Assignment)
    (indexAt valueAt : Nat → Nat) :
    runAssignments state (indices.map fun bit => (indexAt bit, valueAt bit)) =
      forIn indices state (fun bit current => do
        let next ← current.write (indexAt bit) (valueAt bit)
        pure (.yield next)) := by
  induction indices generalizing state with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.map_cons, runAssignments, List.forIn_cons]
    cases written : state.write (indexAt head) (valueAt head) with
    | error error => simp [bind, Except.bind]
    | ok next =>
      simpa only [written, bind, Except.bind, pure, Except.pure] using ih next

def num2BitsWrites (component : Num2BitsComponent) (value : Nat) : List (Nat × Nat) :=
  (List.range component.outputs.size).map fun bit =>
    (component.outputs[bit]!, bitValue value bit)

theorem executeNum2Bits_eq_loop (state : Assignment) (component : Num2BitsComponent)
    (value : Nat) (input : state.read component.input = .ok value)
    (width : component.outputs.size = 248) (bound : value < 2 ^ component.outputs.size) :
    executeNum2Bits state component = runAssignments state (num2BitsWrites component value) := by
  simp only [executeNum2Bits, input, bind, Except.bind, width,
    Nat.not_le_of_lt (show value < 2 ^ 248 by simpa [width] using bound),
    bne_self_eq_false, decide_false, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, pure, Except.pure]
  change
    (forIn (Std.Legacy.Range.mk 0 248 1 (by decide)) state (fun bit current => do
      let next ← current.write component.outputs[bit]! (bitValue value bit)
      pure (ForInStep.yield next)) >>= pure) = _
  rw [bind_pure]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [← List.range_eq_range']
  simpa only [num2BitsWrites, width] using
    (runAssignments_map (List.range 248) state (fun bit => component.outputs[bit]!)
      (bitValue value)).symm

/-- Input conditions concern original values and original graph slots. In
particular they do not mention evaluation success or an R1CS check. Output
aliases are allowed when their independently determined bit values agree. -/
structure Num2BitsInputs (state : Assignment) (component : Num2BitsComponent)
    (value : Nat) : Prop where
  input : Assigned state component.input value
  width : component.outputs.size = 248
  bound : value < 2 ^ component.outputs.size
  outputBounds : ∀ bit, bit < component.outputs.size → component.outputs[bit]! < state.values.size
  compatible : ∀ bit, bit < component.outputs.size →
    state.values[component.outputs[bit]!]! = none ∨
      state.values[component.outputs[bit]!]! = some (bitValue value bit)
  consistent : ∀ first second, first < component.outputs.size → second < component.outputs.size →
    component.outputs[first]! = component.outputs[second]! →
      bitValue value first = bitValue value second

theorem executeNum2Bits_construct (state : Assignment) (component : Num2BitsComponent)
    (value : Nat) (inputs : Num2BitsInputs state component value) :
    ∃ next, executeNum2Bits state component = .ok next ∧ Extends state next ∧
      (∀ bit, bit < component.outputs.size →
        Assigned next component.outputs[bit]! (bitValue value bit)) ∧
      (∀ bit, bit < component.outputs.size → bitValue value bit * bitValue value bit =
        bitValue value bit) ∧ bitSum component.outputs.size value = value := by
  have compatible : CompatibleWrites state (num2BitsWrites component value) := by
    intro index bit member
    rcases List.mem_map.mp member with ⟨position, bounded, equal⟩
    have bounded := List.mem_range.mp bounded
    cases equal
    exact ⟨inputs.outputBounds position bounded,
      Nat.lt_trans (bitValue_is_binary value position) (by decide),
      inputs.compatible position bounded⟩
  have consistent : ConsistentWrites (num2BitsWrites component value) := by
    intro index first second left right
    rcases List.mem_map.mp left with ⟨firstPosition, firstBound, firstEq⟩
    rcases List.mem_map.mp right with ⟨secondPosition, secondBound, secondEq⟩
    have slots : component.outputs[firstPosition]! = component.outputs[secondPosition]! :=
      (congrArg Prod.fst firstEq).trans (congrArg Prod.fst secondEq).symm
    have values := inputs.consistent firstPosition secondPosition
      (List.mem_range.mp firstBound) (List.mem_range.mp secondBound) slots
    exact (congrArg Prod.snd firstEq).symm.trans (values.trans (congrArg Prod.snd secondEq))
  rcases runAssignments_construct (num2BitsWrites component value) state compatible consistent with
    ⟨next, written, preserved, assigned⟩
  refine ⟨next, ?_, preserved, ?_, fun bit _ => bitValue_idempotent value bit,
    bitSum_reconstruct _ _ inputs.bound⟩
  · rw [executeNum2Bits_eq_loop state component value
      (assigned_read state component.input value inputs.input) inputs.width inputs.bound]
    exact written
  · intro bit bound
    apply assigned
    apply List.mem_map.mpr
    exact ⟨bit, List.mem_range.mpr bound, rfl⟩

def storedBitSum (state : Assignment) (component : Num2BitsComponent) : Nat :=
  ((List.range component.outputs.size).map fun bit =>
    2 ^ bit * (state.values[component.outputs[bit]!]!).getD 0).sum

/-- Equations use actual assigned signal values, rather than recomputing the
reference extractor in the conclusion. The boolean row is expressed as
`b*b=b`, and reconstruction is an equality of natural numbers, stronger than
the corresponding equality after reduction modulo Fr. -/
def Num2BitsEquations (state : Assignment) (component : Num2BitsComponent) (value : Nat) : Prop :=
  Assigned state component.input value ∧
  (∀ bit, bit < component.outputs.size → ∃ actual,
    Assigned state component.outputs[bit]! actual ∧ actual * actual = actual) ∧
  storedBitSum state component = value

theorem num2Bits_equations (before after : Assignment) (component : Num2BitsComponent)
    (value : Nat) (input : Assigned before component.input value)
    (preserved : Extends before after)
    (outputs : ∀ bit, bit < component.outputs.size →
      Assigned after component.outputs[bit]! (bitValue value bit))
    (bound : value < 2 ^ component.outputs.size) :
    Num2BitsEquations after component value := by
  refine ⟨preserved.2 component.input value input, ?_, ?_⟩
  · intro bit bounded
    exact ⟨bitValue value bit, outputs bit bounded, bitValue_idempotent value bit⟩
  · have equal : storedBitSum after component = bitSum component.outputs.size value := by
      unfold storedBitSum bitSum
      congr 1
      apply List.map_congr_left
      intro bit member
      rw [assigned_slot after component.outputs[bit]! (bitValue value bit)
        (outputs bit (List.mem_range.mp member))]
      rfl
    rw [equal, bitSum_reconstruct _ _ bound]

theorem executeNum2Bits_construct_equations (state : Assignment) (component : Num2BitsComponent)
    (value : Nat) (inputs : Num2BitsInputs state component value) :
    ∃ next, executeNum2Bits state component = .ok next ∧
      Extends state next ∧ Num2BitsEquations next component value := by
  rcases executeNum2Bits_construct state component value inputs with
    ⟨next, executed, preserved, outputs, _booleanity, _reconstruction⟩
  exact ⟨next, executed, preserved,
    num2Bits_equations state next component value inputs.input preserved outputs inputs.bound⟩

theorem runAssignments_success (writes : List (Nat × Nat)) (state next : Assignment)
    (success : runAssignments state writes = .ok next) :
    Extends state next ∧ ∀ index value, (index, value) ∈ writes → Assigned next index value := by
  induction writes generalizing state with
  | nil =>
    have equal : state = next := by simpa [runAssignments, pure, Except.pure] using success
    subst next
    exact ⟨extends_refl state, by simp⟩
  | cons head rest ih =>
    rcases head with ⟨index, value⟩
    cases written : state.write index value with
    | error error =>
      simp [runAssignments, List.forIn_cons, written, bind, Except.bind] at success
    | ok middle =>
      have tail : runAssignments middle rest = .ok next := by
        simpa only [runAssignments, List.forIn_cons, written, bind, Except.bind,
          pure, Except.pure] using success
      have headSpec := write_success_preserves state middle index value written
      have tailSpec := ih middle tail
      refine ⟨extends_trans headSpec.2 tailSpec.1, ?_⟩
      intro other prior member
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        exact tailSpec.1.2 index value headSpec.1
      · exact tailSpec.2 other prior member

def dualMuxWrites (level : MerkleLevel) (selector input0 input1 : Nat) : List (Nat × Nat) :=
  let output := dualMuxValues selector input0 input1
  [(level.leftOutput, output.1), (level.rightOutput, output.2)]

theorem executeDualMux_eq_writes (state : Assignment) (level : MerkleLevel)
    (selector input0 input1 : Nat)
    (leftRead : state.read level.leftInput = .ok input0)
    (rightRead : state.read level.rightInput = .ok input1)
    (selectorRead : state.read level.selector = .ok selector)
    (binary : selector < 2) :
    executeDualMux state level = (do
      let next ← runAssignments state (dualMuxWrites level selector input0 input1)
      pure (next, (dualMuxValues selector input0 input1).1,
        (dualMuxValues selector input0 input1).2)) := by
  have notGreater : ¬selector > 1 := by omega
  simp only [executeDualMux, leftRead, rightRead, selectorRead, bind, Except.bind,
    pure, Except.pure, notGreater, ↓reduceIte, dualMuxWrites,
    runAssignments, List.forIn_cons, List.forIn_nil]
  cases selected : dualMuxValues selector input0 input1 with
  | mk left right =>
    cases firstWrite : state.write level.leftOutput left with
    | error error => simp
    | ok middle =>
      cases secondWrite : middle.write level.rightOutput right with
      | error error => simp [secondWrite]
      | ok next => simp [secondWrite]

structure DualMuxInputs (state : Assignment) (level : MerkleLevel)
    (selector input0 input1 : Nat) : Prop where
  leftInput : Assigned state level.leftInput input0
  rightInput : Assigned state level.rightInput input1
  selectorInput : Assigned state level.selector selector
  binary : selector < 2
  compatible : CompatibleWrites state (dualMuxWrites level selector input0 input1)
  consistent : ConsistentWrites (dualMuxWrites level selector input0 input1)

def DualMuxEquations (state : Assignment) (level : MerkleLevel)
    (selector input0 input1 : Nat) : Prop :=
  Assigned state level.leftInput input0 ∧ Assigned state level.rightInput input1 ∧
  Assigned state level.selector selector ∧ selector * selector = selector ∧
  ∃ left right, Assigned state level.leftOutput left ∧ Assigned state level.rightOutput right ∧
    left + selector * input0 = input0 + selector * input1 ∧
    right + selector * input1 = input1 + selector * input0

theorem executeDualMux_construct (state : Assignment) (level : MerkleLevel)
    (selector input0 input1 : Nat) (inputs : DualMuxInputs state level selector input0 input1) :
    ∃ next, executeDualMux state level = .ok
        (next, (dualMuxValues selector input0 input1).1,
          (dualMuxValues selector input0 input1).2) ∧
      Extends state next ∧ DualMuxEquations next level selector input0 input1 := by
  rcases runAssignments_construct (dualMuxWrites level selector input0 input1) state
    inputs.compatible inputs.consistent with ⟨next, written, preserved, assigned⟩
  refine ⟨next, ?_, preserved, ?_⟩
  · rw [executeDualMux_eq_writes state level selector input0 input1
      (assigned_read state level.leftInput input0 inputs.leftInput)
      (assigned_read state level.rightInput input1 inputs.rightInput)
      (assigned_read state level.selector selector inputs.selectorInput) inputs.binary]
    rw [written]
    rfl
  · have equations := dualMux_construct selector input0 input1 inputs.binary
    refine ⟨preserved.2 _ _ inputs.leftInput, preserved.2 _ _ inputs.rightInput,
      preserved.2 _ _ inputs.selectorInput, equations.1, _, _, ?_, ?_, equations.2⟩
    · apply assigned
      simp [dualMuxWrites]
    · apply assigned
      simp [dualMuxWrites]

theorem dualMux_inputs_bounds (state : Assignment) (level : MerkleLevel)
    (selector input0 input1 : Nat) (inputs : DualMuxInputs state level selector input0 input1) :
    input0 < scalarPrime ∧ input1 < scalarPrime := by
  have left := (inputs.compatible level.leftOutput
    (dualMuxValues selector input0 input1).1 (by simp [dualMuxWrites])).2.1
  have right := (inputs.compatible level.rightOutput
    (dualMuxValues selector input0 input1).2 (by simp [dualMuxWrites])).2.1
  have cases : selector = 0 ∨ selector = 1 := by have := inputs.binary; omega
  rcases cases with eq | eq <;> subst selector
  · simpa [dualMuxValues] using And.intro left right
  · simpa [dualMuxValues] using And.intro right left

def DualMuxFrEquations (state : Assignment) (level : MerkleLevel)
    (selector input0 input1 : Nat) : Prop :=
  Assigned state level.leftInput input0 ∧ Assigned state level.rightInput input1 ∧
  Assigned state level.selector selector ∧
  selector * ((1 + scalarPrime - selector) % scalarPrime) % scalarPrime = 0 ∧
  ∃ left right, Assigned state level.leftOutput left ∧ Assigned state level.rightOutput right ∧
    (((input1 + scalarPrime - input0) % scalarPrime) * selector + input0) % scalarPrime = left ∧
    (((input0 + scalarPrime - input1) % scalarPrime) * selector + input1) % scalarPrime = right

theorem executeDualMux_construct_fr (state : Assignment) (level : MerkleLevel)
    (selector input0 input1 : Nat) (inputs : DualMuxInputs state level selector input0 input1) :
    ∃ next, executeDualMux state level = .ok
        (next, (dualMuxValues selector input0 input1).1,
          (dualMuxValues selector input0 input1).2) ∧
      Extends state next ∧ DualMuxFrEquations next level selector input0 input1 := by
  rcases executeDualMux_construct state level selector input0 input1 inputs with
    ⟨next, executed, preserved, naturalEquations⟩
  have bounds := dualMux_inputs_bounds state level selector input0 input1 inputs
  have equations := dualMux_fr_construct selector input0 input1 inputs.binary bounds.1 bounds.2
  have writes := runAssignments_construct (dualMuxWrites level selector input0 input1)
    state inputs.compatible inputs.consistent
  rcases writes with ⟨writtenState, written, _, assigned⟩
  have same : writtenState = next := by
    have step := executeDualMux_eq_writes state level selector input0 input1
      (assigned_read _ _ _ inputs.leftInput) (assigned_read _ _ _ inputs.rightInput)
      (assigned_read _ _ _ inputs.selectorInput) inputs.binary
    rw [written] at step
    have result := step.symm.trans executed
    exact congrArg Prod.fst (Except.ok.inj result)
  subst writtenState
  refine ⟨next, executed, preserved, naturalEquations.1, naturalEquations.2.1,
    naturalEquations.2.2.1, equations.1, _, _, ?_, ?_, equations.2⟩
  · exact assigned _ _ (by simp [dualMuxWrites])
  · exact assigned _ _ (by simp [dualMuxWrites])

def Num2BitsFrEquations (state : Assignment) (component : Num2BitsComponent) (value : Nat) : Prop :=
  Assigned state component.input value ∧
  (∀ bit, bit < component.outputs.size → ∃ actual,
    Assigned state component.outputs[bit]! actual ∧
      actual * ((actual + scalarPrime - 1) % scalarPrime) % scalarPrime = 0) ∧
  storedBitSum state component % scalarPrime = value % scalarPrime

theorem executeNum2Bits_construct_fr (state : Assignment) (component : Num2BitsComponent)
    (value : Nat) (inputs : Num2BitsInputs state component value) :
    ∃ next, executeNum2Bits state component = .ok next ∧
      Extends state next ∧ Num2BitsFrEquations next component value := by
  rcases executeNum2Bits_construct state component value inputs with
    ⟨next, executed, preserved, outputs, _booleanity, _reconstruction⟩
  have naturalEquations := num2Bits_equations state next component value inputs.input
    preserved outputs inputs.bound
  refine ⟨next, executed, preserved, naturalEquations.1, ?_, ?_⟩
  · intro bit bounded
    exact ⟨bitValue value bit, outputs bit bounded, bitValue_fr_boolean value bit⟩
  · rw [naturalEquations.2.2]

/-- The complete pre-refactor implementation, retained as a proof reference
for the small extraction of the actual selector stage. -/
def executeMerkleLevelOriginal (constants : Array Nat) (state : Assignment)
    (level : MerkleLevel) (sponge : SpongeLevel) :
    Except String Assignment := do
  let leftInput ← state.read level.leftInput
  let rightInput ← state.read level.rightInput
  let selector ← state.read level.selector
  if selector > 1 then throw "Merkle selector is not a bit."
  let (left, right) := dualMuxValues selector leftInput rightInput
  let withLeft ← state.write level.leftOutput left
  let withRight ← withLeft.write level.rightOutput right
  let mut firstInputs := withRight
  firstInputs ← firstInputs.write sponge.first.key 0
  firstInputs ← firstInputs.write sponge.first.leftInput left
  firstInputs ← firstInputs.write sponge.first.rightInput 0
  let first ← executeFeistel constants firstInputs sponge.first
  let intermediateLeft ← first.read sponge.first.leftOutput
  let intermediateRight ← first.read sponge.first.rightOutput
  let mut secondInputs := first
  secondInputs ← secondInputs.write sponge.second.key 0
  secondInputs ← secondInputs.write sponge.second.leftInput
    ((intermediateLeft + right) % scalarPrime)
  secondInputs ← secondInputs.write sponge.second.rightInput intermediateRight
  let second ← executeFeistel constants secondInputs sponge.second
  let hash ← second.read sponge.second.leftOutput
  let independentHash ← Tornado.Crypto.mimcHashPairWith constants left right
  if hash != independentHash then
    throw "Computed MiMC round signals disagree with the native sponge."
  second.write level.hashOutput hash

theorem executeMerkleLevel_factor_eq (constants : Array Nat) (state : Assignment)
    (level : MerkleLevel) (sponge : SpongeLevel) :
    executeMerkleLevel constants state level sponge =
      executeMerkleLevelOriginal constants state level sponge := by
  cases leftRead : state.read level.leftInput with
  | error error =>
    simp [executeMerkleLevel, executeDualMux, executeMerkleLevelOriginal, leftRead,
      bind, Except.bind]
  | ok leftInput =>
    cases rightRead : state.read level.rightInput with
    | error error =>
      simp [executeMerkleLevel, executeDualMux, executeMerkleLevelOriginal, leftRead,
        rightRead, bind, Except.bind]
    | ok rightInput =>
      cases selectorRead : state.read level.selector with
      | error error =>
        simp [executeMerkleLevel, executeDualMux, executeMerkleLevelOriginal, leftRead,
          rightRead, selectorRead, bind, Except.bind]
      | ok selector =>
        by_cases invalid : selector > 1
        · simp [executeMerkleLevel, executeDualMux, executeMerkleLevelOriginal, leftRead,
            rightRead, selectorRead, invalid, bind, Except.bind]
        · cases firstWrite : state.write level.leftOutput
              (dualMuxValues selector leftInput rightInput).1 with
          | error error =>
            simp [executeMerkleLevel, executeDualMux, executeMerkleLevelOriginal, leftRead,
              rightRead, selectorRead, invalid, firstWrite, bind, Except.bind, pure, Except.pure]
          | ok middle =>
            cases secondWrite : middle.write level.rightOutput
                (dualMuxValues selector leftInput rightInput).2 with
            | error error =>
              simp [executeMerkleLevel, executeDualMux, executeMerkleLevelOriginal, leftRead,
                rightRead, selectorRead, invalid, firstWrite, secondWrite,
                bind, Except.bind, pure, Except.pure]
            | ok next =>
              simp [executeMerkleLevel, executeDualMux, executeMerkleLevelOriginal, leftRead,
                rightRead, selectorRead, invalid, firstWrite, secondWrite,
                bind, Except.bind, pure, Except.pure]

#print axioms Tornado.Protocol.WitnessVM.assigned_read
#print axioms Tornado.Protocol.WitnessVM.extends_refl
#print axioms Tornado.Protocol.WitnessVM.extends_trans
#print axioms Tornado.Protocol.WitnessVM.write_construct
#print axioms Tornado.Protocol.WitnessVM.write_success_preserves
#print axioms Tornado.Protocol.WitnessVM.assigned_slot
#print axioms Tornado.Protocol.WitnessVM.write_success_other
#print axioms Tornado.Protocol.WitnessVM.runAssignments_construct
#print axioms Tornado.Protocol.WitnessVM.bitSum_mod
#print axioms Tornado.Protocol.WitnessVM.bitSum_reconstruct
#print axioms Tornado.Protocol.WitnessVM.bitValue_idempotent
#print axioms Tornado.Protocol.WitnessVM.dualMux_construct
#print axioms Tornado.Protocol.WitnessVM.bitValue_fr_boolean
#print axioms Tornado.Protocol.WitnessVM.modular_difference_add
#print axioms Tornado.Protocol.WitnessVM.dualMux_fr_construct
#print axioms Tornado.Protocol.WitnessVM.runAssignments_map
#print axioms Tornado.Protocol.WitnessVM.executeNum2Bits_eq_loop
#print axioms Tornado.Protocol.WitnessVM.executeNum2Bits_construct
#print axioms Tornado.Protocol.WitnessVM.num2Bits_equations
#print axioms Tornado.Protocol.WitnessVM.executeNum2Bits_construct_equations
#print axioms Tornado.Protocol.WitnessVM.runAssignments_success
#print axioms Tornado.Protocol.WitnessVM.executeDualMux_eq_writes
#print axioms Tornado.Protocol.WitnessVM.executeDualMux_construct
#print axioms Tornado.Protocol.WitnessVM.dualMux_inputs_bounds
#print axioms Tornado.Protocol.WitnessVM.executeDualMux_construct_fr
#print axioms Tornado.Protocol.WitnessVM.executeNum2Bits_construct_fr
#print axioms Tornado.Protocol.WitnessVM.executeMerkleLevel_factor_eq

end Tornado.Protocol.WitnessVM
