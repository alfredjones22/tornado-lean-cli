import Tornado.Protocol.WitnessSymbolic
import TornadoProofs.Witness.NativeField

set_option autoImplicit false
namespace TornadoProofs.Witness.Symbolic
open Tornado.Protocol.WitnessSymbolic

/-- Independent expression semantics. Later construction derives this relation
for the topologically evaluated public DAG and original source input. -/
def Denotes (nodes : Array Node) (inputs values : Array Nat) : Prop :=
  ∀ (index : Nat) (node : Node), nodes[index]? = some node → values[index]! = node.meaning inputs values

theorem constantAt_sound (nodes : Array Node) (inputs values : Array Nat)
    (denotes : Denotes nodes inputs values) (index value : Nat)
    (found : constantAt nodes index = some value) : values[index]! = value := by
  cases lookup : nodes[index]? with
  | none => simp [constantAt, lookup] at found
  | some node =>
    cases node <;> simp [constantAt, lookup] at found
    case constant actual =>
      subst value
      exact denotes index (.constant actual) lookup

theorem foldConstant_sound (nodes : Array Node) (inputs values : Array Nat)
    (denotes : Denotes nodes inputs values) (operation : Node) (value : Nat)
    (folded : foldConstant nodes operation = some value) :
    operation.meaning inputs values = value := by
  cases operation with
  | input index => simp [foldConstant] at folded
  | constant actual => simp [foldConstant] at folded
  | bit source position =>
    cases sourceValue : constantAt nodes source with
    | none => simp [foldConstant, sourceValue] at folded
    | some x =>
      have known := constantAt_sound nodes inputs values denotes source x sourceValue
      simp only [foldConstant, sourceValue, bind, Option.bind, pure,
        Option.some.injEq] at folded
      simpa only [Node.meaning, known] using folded
  | inverse source =>
    cases sourceValue : constantAt nodes source with
    | none => simp [foldConstant, sourceValue] at folded
    | some x =>
      have known := constantAt_sound nodes inputs values denotes source x sourceValue
      simp only [foldConstant, sourceValue, bind, Option.bind, pure,
        Option.some.injEq] at folded
      simpa only [Node.meaning, known] using folded
  | add left right | sub left right | mul left right =>
    all_goals
      cases leftValue : constantAt nodes left with
      | none => simp [foldConstant, leftValue] at folded
      | some x =>
        cases rightValue : constantAt nodes right with
        | none => simp [foldConstant, leftValue, rightValue] at folded
        | some y =>
          have leftKnown := constantAt_sound nodes inputs values denotes left x leftValue
          have rightKnown := constantAt_sound nodes inputs values denotes right y rightValue
          simp only [foldConstant, leftValue, rightValue, bind, Option.bind, pure,
            Option.some.injEq] at folded
          simpa only [Node.meaning, leftKnown, rightKnown] using folded
  | select selector left right =>
    cases selectorValue : constantAt nodes selector with
    | none => simp [foldConstant, selectorValue] at folded
    | some s =>
      cases leftValue : constantAt nodes left with
      | none => simp [foldConstant, selectorValue, leftValue] at folded
      | some x =>
        cases rightValue : constantAt nodes right with
        | none => simp [foldConstant, selectorValue, leftValue, rightValue] at folded
        | some y =>
          have selectorKnown := constantAt_sound nodes inputs values denotes selector s selectorValue
          have leftKnown := constantAt_sound nodes inputs values denotes left x leftValue
          have rightKnown := constantAt_sound nodes inputs values denotes right y rightValue
          simp only [foldConstant, selectorValue, leftValue, rightValue, bind, Option.bind,
            pure, Option.some.injEq] at folded
          simpa only [Node.meaning, selectorKnown, leftKnown, rightKnown] using folded

theorem checkOperation_sound (nodes : Array Node) (inputs values : Array Nat)
    (denotes : Denotes nodes inputs values) (operation : Node) (candidate : Nat)
    (checked : checkOperation nodes operation candidate = true) :
    values[candidate]! = operation.meaning inputs values := by
  cases lookup : nodes[candidate]? with
  | none => simp [checkOperation, lookup] at checked
  | some actual =>
    have known := denotes candidate actual lookup
    simp only [checkOperation, lookup, Bool.or_eq_true, decide_eq_true_eq] at checked
    rcases checked with same | folded
    · subst actual
      exact known
    · cases fold : foldConstant nodes operation with
      | none => simp [fold] at folded
      | some value =>
        simp only [fold, decide_eq_true_eq] at folded
        subst actual
        exact known.trans (foldConstant_sound nodes inputs values denotes operation value fold).symm

theorem resolve_sound (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Denotes resolver.nodes inputs values) (operation : Node) (candidate : Nat)
    (resolved : resolver.resolve operation = .ok candidate) :
    values[candidate]! = operation.meaning inputs values := by
  cases lookup : resolver.lookup[operationKey resolver.nodes operation]? with
  | none => simp [Resolver.resolve, lookup, bind, Except.bind] at resolved
  | some found =>
    cases valid : checkOperation resolver.nodes operation found with
    | false => simp [Resolver.resolve, lookup, valid, bind, Except.bind, pure, Except.pure] at resolved
    | true =>
      have equal : found = candidate := by
        simpa [Resolver.resolve, lookup, valid, bind, Except.bind, pure, Except.pure] using resolved
      subst found
      exact checkOperation_sound resolver.nodes inputs values denotes operation candidate valid

end TornadoProofs.Witness.Symbolic
#print axioms TornadoProofs.Witness.Symbolic.constantAt_sound
#print axioms TornadoProofs.Witness.Symbolic.foldConstant_sound
#print axioms TornadoProofs.Witness.Symbolic.checkOperation_sound
#print axioms TornadoProofs.Witness.Symbolic.resolve_sound
