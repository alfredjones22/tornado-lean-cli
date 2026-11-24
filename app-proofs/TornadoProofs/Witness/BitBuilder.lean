import TornadoProofs.Witness.MuxBuilder
import TornadoProofs.Witness.ConcatBits

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.TornadoWitness Tornado.Protocol.WitnessVM

/-- Exact byte source of every bit consumed by the original compiler. -/
def noteBits (input : WithdrawalInput) (commitment : Bool) (position : Nat) : Nat :=
  bitValue (Source.nativeLittleEndian (if commitment then input.note.preimage else input.note.nullifierBytes)) position

theorem noteBits_binary (input : WithdrawalInput) (commitment : Bool) (position : Nat) :
    noteBits input commitment position < 2 := Nat.mod_lt _ (by decide)

theorem compiler_bit_source (resolver : Resolver) (commitment : Bool) (position : Nat)
    (initial final : Array Footprint) (node : Nat)
    (returned : (compilerWindows resolver commitment).bit position initial=.ok (node,final)) :
    originalBit resolver commitment position=.ok node ∧ final=initial := by
  dsimp only [compilerWindows,liftM,MonadLiftT.monadLift,MonadLift.monadLift,StateT.lift,
    bind,pure,Except.bind,Except.pure] at returned
  cases compiled : originalBit resolver commitment position with
  | error failure =>
    simp only [compiled] at returned
    cases returned
  | ok built =>
    have equal : (built,initial)=(node,final) := by
      simpa only [compiled,Except.ok.injEq] using returned
    cases equal
    exact ⟨rfl,rfl⟩

theorem bit_spec (resolver : Resolver) (input : WithdrawalInput)
    (source : Source.ValidWithdrawal input) (valid : tableValid resolver.nodes=true)
    (commitment : Bool) (position : Nat) :
    BuildSpec (Execution.StepsAdmitted (Execution.sourceValues resolver (inputPrefix input) input.note.commitment))
      ((compilerWindows resolver commitment).bit position)
      (fun result => BitMeaning (Execution.sourceValues resolver (inputPrefix input) input.note.commitment)
        result (noteBits input commitment position)) := by
  intro initial result final prior returned
  obtain ⟨compiled,rfl⟩ := compiler_bit_source resolver commitment position initial final result returned
  exact ⟨prior,Source.originalBit_native_meaning resolver input source valid commitment position result compiled⟩

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.noteBits_binary
#print axioms TornadoProofs.Witness.PedersenReference.compiler_bit_source
#print axioms TornadoProofs.Witness.PedersenReference.bit_spec
