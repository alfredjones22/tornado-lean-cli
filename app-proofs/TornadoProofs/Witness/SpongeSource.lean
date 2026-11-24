import TornadoProofs.Witness.SpongeSimulation

set_option autoImplicit false

namespace TornadoProofs.Witness.Execution

open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.Groth16R1CS

theorem compileDualMux_reads (resolver : Resolver) (state : SignalState) (level : MerkleLevel)
    (output : SignalState × Nat × Nat) (compiled : compileDualMux resolver state level = .ok output) :
    ∃ left right selector, state.read level.leftInput = .ok left ∧
      state.read level.rightInput = .ok right ∧ state.read level.selector = .ok selector := by
  unfold compileDualMux at compiled
  obtain ⟨left, leftRead, compiled⟩ := bind_success (state.read level.leftInput) _ output compiled
  obtain ⟨right, rightRead, compiled⟩ := bind_success (state.read level.rightInput) _ output compiled
  obtain ⟨selector, selectorRead, _⟩ := bind_success (state.read level.selector) _ output compiled
  exact ⟨left, right, selector, leftRead, rightRead, selectorRead⟩

theorem executeDualMux_observer (state : Assignment) (level : MerkleLevel)
    (leftInput rightInput selector : Nat) (leftRead : state.read level.leftInput = .ok leftInput)
    (rightRead : state.read level.rightInput = .ok rightInput) (selectorRead : state.read level.selector = .ok selector)
    (output : Assignment × Nat × Nat) (returned : executeDualMux state level = .ok output) :
    output.2 = dualMuxValues selector leftInput rightInput := by
  unfold executeDualMux at returned
  simp only [leftRead, rightRead, selectorRead, bind, Except.bind] at returned
  by_cases invalid : selector > 1
  · simp only [invalid, ↓reduceIte] at returned
    change (Except.error "Merkle selector is not a bit." : Except String (Assignment × Nat × Nat)) = .ok output at returned
    contradiction
  · simp only [invalid, ↓reduceIte] at returned
    cases selected : dualMuxValues selector leftInput rightInput with
    | mk left right =>
      simp only [selected] at returned
      obtain ⟨first, _, returned⟩ := bind_success (state.write level.leftOutput left) _ output returned
      obtain ⟨second, _, returned⟩ := bind_success (first.write level.rightOutput right) _ output returned
      have equal : (second, left, right) = output := Except.ok.inj returned
      exact (congrArg Prod.snd equal).symm

theorem executeMerkleLevel_observer (constants : Array Nat) (state output : Assignment)
    (level : MerkleLevel) (sponge : SpongeLevel) (leftInput rightInput selector : Nat)
    (leftRead : state.read level.leftInput = .ok leftInput)
    (rightRead : state.read level.rightInput = .ok rightInput)
    (selectorRead : state.read level.selector = .ok selector)
    (returned : executeMerkleLevel constants state level sponge = .ok output) :
    ∃ hash, LeanCrypto.mimcHashPairWith constants (dualMuxValues selector leftInput rightInput).1
      (dualMuxValues selector leftInput rightInput).2 = .ok hash ∧ Assigned output level.hashOutput hash := by
  unfold executeMerkleLevel at returned
  obtain ⟨dualResult, dualBuilt, returned⟩ := bind_success (executeDualMux state level) _ output returned
  obtain ⟨dual, left, right⟩ := dualResult
  have selected := executeDualMux_observer state level leftInput rightInput selector
    leftRead rightRead selectorRead (dual, left, right) dualBuilt
  obtain ⟨firstKey, _, returned⟩ := bind_success _ _ output returned
  obtain ⟨firstLeft, _, returned⟩ := bind_success _ _ output returned
  obtain ⟨firstInputs, _, returned⟩ := bind_success _ _ output returned
  obtain ⟨first, _, returned⟩ := bind_success _ _ output returned
  obtain ⟨intermediateLeft, _, returned⟩ := bind_success _ _ output returned
  obtain ⟨intermediateRight, _, returned⟩ := bind_success _ _ output returned
  obtain ⟨secondKey, _, returned⟩ := bind_success _ _ output returned
  obtain ⟨secondLeft, _, returned⟩ := bind_success _ _ output returned
  obtain ⟨secondInputs, _, returned⟩ := bind_success _ _ output returned
  obtain ⟨second, _, returned⟩ := bind_success _ _ output returned
  obtain ⟨hash, _, returned⟩ := bind_success _ _ output returned
  obtain ⟨independent, independentBuilt, returned⟩ := bind_success
    (LeanCrypto.mimcHashPairWith constants left right) _ output returned
  by_cases mismatch : (hash != independent) = true
  · simp only [mismatch, ↓reduceIte] at returned
    change (Except.error "Computed MiMC round signals disagree with the native sponge." : Except String Assignment) = .ok output at returned
    contradiction
  · have equal : hash = independent := bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr mismatch)
    have finalWrite : second.write level.hashOutput hash = .ok output := by
      simpa only [mismatch, ↓reduceIte, bind, Except.bind, pure, Except.pure] using returned
    refine ⟨hash, ?_, (write_success_preserves second output level.hashOutput hash finalWrite).1⟩
    have pairEqual : (left, right) = dualMuxValues selector leftInput rightInput := selected
    rw [← pairEqual]
    simpa only [equal] using independentBuilt

/-- Exact source-input observer: the stored hash is native MiMC applied to
the two original signal reads in the order selected by the source bit.
Actual native execution is constructed internally from public compilation. -/
theorem compileMerkleLevel_source_hash (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (constants : Array Nat) (state output : SignalState) (level : MerkleLevel) (sponge : SpongeLevel)
    (compiled : compileMerkleLevel resolver constants state level sponge = .ok output)
    (selectorBit : SelectorBit state level values) (terminal : AliasesValid output values) :
    ∃ left right selector hash, state.read level.leftInput = .ok left ∧
      state.read level.rightInput = .ok right ∧ state.read level.selector = .ok selector ∧
      values[selector]! ≤ 1 ∧
      LeanCrypto.mimcHashPairWith constants (dualMuxValues values[selector]! values[left]! values[right]!).1
        (dualMuxValues values[selector]! values[left]! values[right]!).2 = .ok hash ∧
      (realize output values).read level.hashOutput = .ok hash := by
  have execution := (compileMerkleLevel_construct resolver inputs values denotes canonical constants state output
    level sponge compiled selectorBit terminal).2
  have source := compiled
  unfold compileMerkleLevel at source
  obtain ⟨dual, dualBuilt, _⟩ := bind_success (compileDualMux resolver state level) _ output source
  obtain ⟨left, right, selector, leftRead, rightRead, selectorRead⟩ := compileDualMux_reads resolver state level dual dualBuilt
  obtain ⟨hash, nativeHash, assigned⟩ := executeMerkleLevel_observer constants (realize state values) (realize output values)
    level sponge values[left]! values[right]! values[selector]!
    (signalRead_realize state values level.leftInput left leftRead)
    (signalRead_realize state values level.rightInput right rightRead)
    (signalRead_realize state values level.selector selector selectorRead) execution
  exact ⟨left, right, selector, hash, leftRead, rightRead, selectorRead, selectorBit selector selectorRead,
    nativeHash, assigned_read _ _ _ assigned⟩

end TornadoProofs.Witness.Execution

#print axioms TornadoProofs.Witness.Execution.compileDualMux_reads
#print axioms TornadoProofs.Witness.Execution.executeDualMux_observer
#print axioms TornadoProofs.Witness.Execution.executeMerkleLevel_observer
#print axioms TornadoProofs.Witness.Execution.compileMerkleLevel_source_hash
