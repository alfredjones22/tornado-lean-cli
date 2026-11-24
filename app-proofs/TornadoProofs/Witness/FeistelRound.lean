import TornadoProofs.Witness.FeistelSupport

set_option autoImplicit false

namespace TornadoProofs.Witness.Execution

open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.Groth16R1CS

def realizeFrame (frame : FeistelFrame SignalState) (values : Array Nat) : FeistelFrame Assignment :=
  ⟨realize frame.state values, values[frame.left]!, values[frame.right]!⟩

/-- One actual arithmetic round is constructed from the independently
interpreted public DAG and its successful public wiring. Final alias equality
flows backwards through all four checked signal writes. -/
theorem compileFeistelRound_construct (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (constants : Array Nat) (stage : Feistel) (key round : Nat)
    (frame output : FeistelFrame SignalState)
    (compiled : compileFeistelRound resolver constants stage key round frame = .ok output)
    (terminal : AliasesValid output.state values) :
    AliasesValid frame.state values ∧
      executeFeistelRound constants stage values[key]! round (realizeFrame frame values) =
        .ok (realizeFrame output values) := by
  unfold compileFeistelRound at compiled
  obtain ⟨constant, constantBuilt, compiled⟩ := bind_success (resolver.resolve (.constant constants[round]!)) _ output compiled
  obtain ⟨keyed, keyedBuilt, compiled⟩ := bind_success (resolver.resolve (.add frame.left key)) _ output compiled
  obtain ⟨t, tBuilt, compiled⟩ := bind_success (resolver.resolve (.add keyed constant)) _ output compiled
  obtain ⟨square, squareBuilt, compiled⟩ := bind_success (resolver.resolve (.mul t t)) _ output compiled
  obtain ⟨fourth, fourthBuilt, compiled⟩ := bind_success (resolver.resolve (.mul square square)) _ output compiled
  obtain ⟨fifth, fifthBuilt, compiled⟩ := bind_success (resolver.resolve (.mul fourth t)) _ output compiled
  obtain ⟨first, firstBuilt, compiled⟩ := bind_success (frame.state.write stage.t2[round]! square) _ output compiled
  obtain ⟨second, secondBuilt, compiled⟩ := bind_success (first.write stage.t4[round]! fourth) _ output compiled
  obtain ⟨next, nextBuilt, compiled⟩ := bind_success (resolver.resolve (.add frame.right fifth)) _ output compiled
  let tNat := (values[frame.left]! + values[key]! + constants[round]!) % scalarPrime
  let squareNat := tNat * tNat % scalarPrime
  let fourthNat := squareNat * squareNat % scalarPrime
  let fifthNat := fourthNat * tNat % scalarPrime
  let nextNat := (values[frame.right]! + fifthNat) % scalarPrime
  have constantValue : values[constant]! = constants[round]! :=
    Symbolic.resolve_sound resolver inputs values denotes (.constant constants[round]!) constant constantBuilt
  have keyedValue : values[keyed]! = (values[frame.left]! + values[key]!) % scalarPrime :=
    Symbolic.resolve_sound resolver inputs values denotes (.add frame.left key) keyed keyedBuilt
  have tValue : values[t]! = tNat := by
    have value := Symbolic.resolve_sound resolver inputs values denotes (.add keyed constant) t tBuilt
    simp only [Node.meaning, keyedValue, constantValue] at value
    simpa only [tNat, Nat.mod_add_mod] using value
  have squareValue : values[square]! = squareNat := by
    simpa only [Node.meaning, tValue] using
      Symbolic.resolve_sound resolver inputs values denotes (.mul t t) square squareBuilt
  have fourthValue : values[fourth]! = fourthNat := by
    simpa only [Node.meaning, squareValue] using
      Symbolic.resolve_sound resolver inputs values denotes (.mul square square) fourth fourthBuilt
  have fifthValue : values[fifth]! = fifthNat := by
    simpa only [Node.meaning, fourthValue, tValue] using
      Symbolic.resolve_sound resolver inputs values denotes (.mul fourth t) fifth fifthBuilt
  have nextValue : values[next]! = nextNat := by
    simpa only [Node.meaning, fifthValue] using
      Symbolic.resolve_sound resolver inputs values denotes (.add frame.right fifth) next nextBuilt
  by_cases middle : round < 219
  · simp only [middle, ↓reduceIte] at compiled
    obtain ⟨third, thirdBuilt, compiled⟩ := bind_success (second.write stage.leftRounds[round]! next) _ output compiled
    obtain ⟨fourthState, fourthStateBuilt, compiled⟩ := bind_success (third.write stage.rightRounds[round]! frame.left) _ output compiled
    have equal : FeistelFrame.mk fourthState next frame.left = output := Except.ok.inj compiled
    subst output
    obtain ⟨thirdAliases, runtimeFourth⟩ := signalWrite_construct third fourthState values canonical
      stage.rightRounds[round]! frame.left fourthStateBuilt terminal
    obtain ⟨secondAliases, runtimeThird⟩ := signalWrite_construct second third values canonical
      stage.leftRounds[round]! next thirdBuilt thirdAliases
    obtain ⟨firstAliases, runtimeSecond⟩ := signalWrite_construct first second values canonical
      stage.t4[round]! fourth secondBuilt secondAliases
    obtain ⟨initialAliases, runtimeFirst⟩ := signalWrite_construct frame.state first values canonical
      stage.t2[round]! square firstBuilt firstAliases
    refine ⟨initialAliases, ?_⟩
    simp only [executeFeistelRound, realizeFrame, middle, ↓reduceIte]
    change (do
      let firstState ← (realize frame.state values).write stage.t2[round]! squareNat
      let secondState ← firstState.write stage.t4[round]! fourthNat
      let thirdState ← secondState.write stage.leftRounds[round]! nextNat
      let fourthState ← thirdState.write stage.rightRounds[round]! values[frame.left]!
      pure (FeistelFrame.mk fourthState nextNat values[frame.left]!)) = _
    rw [← squareValue, runtimeFirst]
    dsimp only [bind, Except.bind]
    rw [← fourthValue, runtimeSecond]
    dsimp only [bind, Except.bind]
    rw [← nextValue, runtimeThird]
    dsimp only [bind, Except.bind]
    rw [runtimeFourth]
    rfl
  · simp only [middle, ↓reduceIte] at compiled
    obtain ⟨third, thirdBuilt, compiled⟩ := bind_success (second.write stage.leftOutput frame.left) _ output compiled
    obtain ⟨fourthState, fourthStateBuilt, compiled⟩ := bind_success (third.write stage.rightOutput next) _ output compiled
    have equal : FeistelFrame.mk fourthState frame.left next = output := Except.ok.inj compiled
    subst output
    obtain ⟨thirdAliases, runtimeFourth⟩ := signalWrite_construct third fourthState values canonical
      stage.rightOutput next fourthStateBuilt terminal
    obtain ⟨secondAliases, runtimeThird⟩ := signalWrite_construct second third values canonical
      stage.leftOutput frame.left thirdBuilt thirdAliases
    obtain ⟨firstAliases, runtimeSecond⟩ := signalWrite_construct first second values canonical
      stage.t4[round]! fourth secondBuilt secondAliases
    obtain ⟨initialAliases, runtimeFirst⟩ := signalWrite_construct frame.state first values canonical
      stage.t2[round]! square firstBuilt firstAliases
    refine ⟨initialAliases, ?_⟩
    simp only [executeFeistelRound, realizeFrame, middle, ↓reduceIte]
    change (do
      let firstState ← (realize frame.state values).write stage.t2[round]! squareNat
      let secondState ← firstState.write stage.t4[round]! fourthNat
      let thirdState ← secondState.write stage.leftOutput values[frame.left]!
      let fourthState ← thirdState.write stage.rightOutput nextNat
      pure (FeistelFrame.mk fourthState values[frame.left]! nextNat)) = _
    rw [← squareValue, runtimeFirst]
    dsimp only [bind, Except.bind]
    rw [← fourthValue, runtimeSecond]
    dsimp only [bind, Except.bind]
    rw [runtimeThird]
    dsimp only [bind, Except.bind]
    rw [← nextValue, runtimeFourth]
    dsimp only [bind, Except.bind]
    rfl

end TornadoProofs.Witness.Execution

#print axioms TornadoProofs.Witness.Execution.compileFeistelRound_construct
