import TornadoProofs.Witness.ByteConcat
import TornadoProofs.Witness.WithdrawalSource

set_option autoImplicit false
namespace TornadoProofs.Witness.Source
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.PedersenSchedule
open Tornado.Protocol.TornadoWitness
open TornadoProofs.Witness.Execution

def referenceOriginalBit (input : WithdrawalInput) (position : Nat) : Nat :=
  if position<248 then bitValue input.note.nullifier position else bitValue input.note.secret (position-248)

theorem originalBit_meaning (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (commitment : Bool) (position node : Nat)
    (compiled : originalBit resolver commitment position=.ok node) :
    position<(if commitment then 496 else 248) ∧
      values[node]! = bitValue inputs[if position<248 then 7 else 8]!
        (if position<248 then position else position-248) := by
  have bound : ¬position >= (if commitment then 496 else 248) := by
    intro outside
    simp [originalBit,outside,bind,Except.bind] at compiled
  simp only [originalBit,bound,↓reduceIte,pure_bind] at compiled
  obtain ⟨input,resolved,written⟩ := bind_success _ _ node compiled
  have inputValue := Symbolic.resolve_sound resolver inputs values denotes
    (.input (if position<248 then 7 else 8)) input resolved
  have bit := Symbolic.resolve_sound resolver inputs values denotes
    (.bit input (if position<248 then position else position-248)) node written
  refine ⟨by omega,?_⟩
  change values[node]! = bitValue values[input]! (if position<248 then position else position-248) at bit
  rw [inputValue] at bit
  exact bit

theorem originalBit_prefix_meaning (resolver : Resolver) (input : WithdrawalInput)
    (source : ValidWithdrawal input) (valid : tableValid resolver.nodes=true)
    (commitment : Bool) (position node : Nat) (compiled : originalBit resolver commitment position=.ok node) :
    position<(if commitment then 496 else 248) ∧
      (sourceValues resolver (inputPrefix input) input.note.commitment)[node]! = referenceOriginalBit input position := by
  obtain ⟨bound,value⟩ := originalBit_meaning resolver ((inputPrefix input).push input.note.commitment)
    (sourceValues resolver (inputPrefix input) input.note.commitment)
    (sourceValues_denotes resolver (inputPrefix input) input.note.commitment valid) commitment position node compiled
  refine ⟨bound,?_⟩
  unfold referenceOriginalBit
  by_cases low : position<248
  · simp only [low,↓reduceIte] at value ⊢
    rw [pushed_prefix (inputPrefix input) input.note.commitment (valid_prefix_size input source) 7 (by decide),
      inputPrefix_header input 7 (by decide)] at value
    exact value
  · simp only [low,↓reduceIte] at value ⊢
    rw [pushed_prefix (inputPrefix input) input.note.commitment (valid_prefix_size input source) 8 (by decide),
      inputPrefix_header input 8 (by decide)] at value
    exact value

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.originalBit_meaning
#print axioms TornadoProofs.Witness.Source.originalBit_prefix_meaning
