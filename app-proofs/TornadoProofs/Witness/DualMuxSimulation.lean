import TornadoProofs.Witness.FeistelSupport

set_option autoImplicit false

namespace TornadoProofs.Witness.Execution

open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.Groth16R1CS

def SelectorBit (state : SignalState) (level : MerkleLevel) (values : Array Nat) : Prop :=
  ∀ selector, state.read level.selector = .ok selector → values[selector]! ≤ 1

theorem compileDualMux_construct (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (state : SignalState) (level : MerkleLevel) (output : SignalState × Nat × Nat)
    (compiled : compileDualMux resolver state level = .ok output)
    (selectorBit : SelectorBit state level values) (terminal : AliasesValid output.1 values) :
    AliasesValid state values ∧ executeDualMux (realize state values) level =
      .ok (realize output.1 values, values[output.2.1]!, values[output.2.2]!) := by
  unfold compileDualMux at compiled
  obtain ⟨leftInput, leftRead, compiled⟩ := bind_success (state.read level.leftInput) _ output compiled
  obtain ⟨rightInput, rightRead, compiled⟩ := bind_success (state.read level.rightInput) _ output compiled
  obtain ⟨selector, selectorRead, compiled⟩ := bind_success (state.read level.selector) _ output compiled
  obtain ⟨left, leftBuilt, compiled⟩ := bind_success (resolver.resolve (.select selector leftInput rightInput)) _ output compiled
  obtain ⟨right, rightBuilt, compiled⟩ := bind_success (resolver.resolve (.select selector rightInput leftInput)) _ output compiled
  obtain ⟨first, firstBuilt, compiled⟩ := bind_success (state.write level.leftOutput left) _ output compiled
  obtain ⟨second, secondBuilt, compiled⟩ := bind_success (first.write level.rightOutput right) _ output compiled
  have equal : (second, left, right) = output := Except.ok.inj compiled
  subst output
  obtain ⟨firstAliases, runtimeSecond⟩ := signalWrite_construct first second values canonical
    level.rightOutput right secondBuilt terminal
  obtain ⟨initialAliases, runtimeFirst⟩ := signalWrite_construct state first values canonical
    level.leftOutput left firstBuilt firstAliases
  have leftValue : values[left]! = (dualMuxValues values[selector]! values[leftInput]! values[rightInput]!).1 :=
    Symbolic.resolve_sound resolver inputs values denotes (.select selector leftInput rightInput) left leftBuilt
  have rightValue : values[right]! = (dualMuxValues values[selector]! values[leftInput]! values[rightInput]!).2 := by
    have resolved := Symbolic.resolve_sound resolver inputs values denotes (.select selector rightInput leftInput) right rightBuilt
    have swapped : (dualMuxValues values[selector]! values[rightInput]! values[leftInput]!).1 =
        (dualMuxValues values[selector]! values[leftInput]! values[rightInput]!).2 := by
      unfold dualMuxValues
      split <;> rfl
    exact resolved.trans swapped
  have binary := selectorBit selector selectorRead
  have valid : ¬values[selector]! > 1 := by omega
  refine ⟨initialAliases, ?_⟩
  simp only [executeDualMux, signalRead_realize state values level.leftInput leftInput leftRead,
    signalRead_realize state values level.rightInput rightInput rightRead,
    signalRead_realize state values level.selector selector selectorRead,
    valid, ↓reduceIte, bind, Except.bind]
  rw [← leftValue, runtimeFirst]
  simp only [pure, Except.pure]
  rw [← rightValue, runtimeSecond]

end TornadoProofs.Witness.Execution

#print axioms TornadoProofs.Witness.Execution.compileDualMux_construct
