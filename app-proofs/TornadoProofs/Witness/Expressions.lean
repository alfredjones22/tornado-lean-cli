import Tornado.Protocol.WitnessExpressions
import TornadoProofs.Witness.SymbolicValues

set_option autoImplicit false
namespace TornadoProofs.Witness.Symbolic
open Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.Groth16R1CS

def expressionValue (values : Array Nat) : Expression → Nat
  | .reference index => values[index]!
  | .constant value => value
  | .bit source position => bitValue (expressionValue values source) position
  | .add left right => (expressionValue values left + expressionValue values right) % scalarPrime
  | .sub left right => (expressionValue values left + scalarPrime - expressionValue values right % scalarPrime) % scalarPrime
  | .mul left right => expressionValue values left * expressionValue values right % scalarPrime
  | .inverse source => LeanCrypto.Groth16.FFT.powMod (expressionValue values source) (scalarPrime-2)
  | .select selector left right =>
    (dualMuxValues (expressionValue values selector) (expressionValue values left)
      (expressionValue values right)).1

theorem compileExpression_sound (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Denotes resolver.nodes inputs values) (expression : Expression) (result : Nat)
    (compiled : expression.compile resolver = .ok result) :
    values[result]! = expressionValue values expression := by
  induction expression generalizing result with
  | reference index =>
    have equal : index = result := by simpa [Expression.compile, pure, Except.pure] using compiled
    subst result
    rfl
  | constant value =>
    exact resolve_sound resolver inputs values denotes (.constant value) result compiled
  | bit source position ih =>
    cases sourceResult : source.compile resolver with
    | error err => simp [Expression.compile, sourceResult, bind, Except.bind] at compiled
    | ok index =>
      have operation : resolver.resolve (.bit index position) = .ok result := by
        simpa [Expression.compile, sourceResult, bind, Except.bind, pure, Except.pure] using compiled
      have sound := resolve_sound resolver inputs values denotes (.bit index position) result operation
      simpa only [Node.meaning, expressionValue, ih index sourceResult] using sound
  | inverse source ih =>
    cases sourceResult : source.compile resolver with
    | error err => simp [Expression.compile, sourceResult, bind, Except.bind] at compiled
    | ok index =>
      have operation : resolver.resolve (.inverse index) = .ok result := by
        simpa [Expression.compile, sourceResult, bind, Except.bind, pure, Except.pure] using compiled
      have sound := resolve_sound resolver inputs values denotes (.inverse index) result operation
      simpa only [Node.meaning, expressionValue, ih index sourceResult] using sound
  | add left right leftIH rightIH | sub left right leftIH rightIH | mul left right leftIH rightIH =>
    all_goals
      cases leftResult : left.compile resolver with
      | error err => simp [Expression.compile, leftResult, bind, Except.bind] at compiled
      | ok leftIndex =>
        cases rightResult : right.compile resolver with
        | error err => simp [Expression.compile, leftResult, rightResult, bind, Except.bind] at compiled
        | ok rightIndex =>
          simp only [Expression.compile, leftResult, rightResult, bind, Except.bind] at compiled
          have sound := resolve_sound resolver inputs values denotes _ result compiled
          simpa only [Node.meaning, expressionValue, leftIH leftIndex leftResult,
            rightIH rightIndex rightResult] using sound
  | select selector left right selectorIH leftIH rightIH =>
    cases selectorResult : selector.compile resolver with
    | error err => simp [Expression.compile, selectorResult, bind, Except.bind] at compiled
    | ok selectorIndex =>
      cases leftResult : left.compile resolver with
      | error err => simp [Expression.compile, selectorResult, leftResult, bind, Except.bind] at compiled
      | ok leftIndex =>
        cases rightResult : right.compile resolver with
        | error err => simp [Expression.compile, selectorResult, leftResult, rightResult, bind, Except.bind] at compiled
        | ok rightIndex =>
          simp only [Expression.compile, selectorResult, leftResult, rightResult,
            bind, Except.bind] at compiled
          have sound := resolve_sound resolver inputs values denotes _ result compiled
          simpa only [Node.meaning, expressionValue, selectorIH selectorIndex selectorResult,
            leftIH leftIndex leftResult, rightIH rightIndex rightResult] using sound

end TornadoProofs.Witness.Symbolic
#print axioms TornadoProofs.Witness.Symbolic.compileExpression_sound
