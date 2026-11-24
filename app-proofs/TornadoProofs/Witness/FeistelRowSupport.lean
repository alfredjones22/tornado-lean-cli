import TornadoProofs.Witness.SpongeSource
import TornadoProofs.Witness.SignalRows

set_option autoImplicit false

namespace TornadoProofs.Witness.Local

open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.Groth16R1CS
open TornadoProofs.Witness.Execution
open LeanCrypto.Proofs.ConstraintCertificate LeanCrypto.Proofs.BN254Fr
open LeanCrypto.Groth16.ConstraintCertificate

def Respects (assignment : Nat → Fr) (state : Assignment) : Prop :=
  ∀ index value, Assigned state index value → assignment index = model value

theorem respects_backwards (assignment : Nat → Fr) (before after : Assignment)
    (extended : Extends before after) (respects : Respects assignment after) : Respects assignment before :=
  fun index value assigned => respects index value (extended.2 index value assigned)

theorem read_success_assigned (state : Assignment) (index value : Nat)
    (read : state.read index = .ok value) : Assigned state index value := by
  by_cases outside : index >= state.values.size
  · simp [Assignment.read, outside, bind, Except.bind] at read
  have bound : index < state.values.size := by omega
  cases slot : state.values[index]! with
  | none => simp [Assignment.read, outside, slot, bind, Except.bind, pure, Except.pure] at read
  | some prior =>
    have equal : prior = value := by
      simpa [Assignment.read, outside, slot, bind, Except.bind, pure, Except.pure] using read
    subst prior
    simpa only [Assigned, Array.getElem?_eq_getElem bound, getElem!_pos state.values index bound] using congrArg some slot

def nativeT (constants : Array Nat) (key round : Nat) (frame : FeistelFrame Assignment) : Nat :=
  (frame.left + key + constants[round]!) % scalarPrime

def nativeSquare (constants : Array Nat) (key round : Nat) (frame : FeistelFrame Assignment) : Nat :=
  nativeT constants key round frame * nativeT constants key round frame % scalarPrime

def nativeFourth (constants : Array Nat) (key round : Nat) (frame : FeistelFrame Assignment) : Nat :=
  nativeSquare constants key round frame * nativeSquare constants key round frame % scalarPrime

def nativeNext (constants : Array Nat) (key round : Nat) (frame : FeistelFrame Assignment) : Nat :=
  (frame.right + nativeFourth constants key round frame * nativeT constants key round frame % scalarPrime) % scalarPrime

def RoundWrites (constants : Array Nat) (stage : Feistel) (key round : Nat)
    (frame output : FeistelFrame Assignment) : Prop :=
  Extends frame.state output.state ∧
    Assigned output.state stage.t2[round]! (nativeSquare constants key round frame) ∧
    Assigned output.state stage.t4[round]! (nativeFourth constants key round frame) ∧
    if round < 219 then
      Assigned output.state stage.leftRounds[round]! (nativeNext constants key round frame) ∧
        Assigned output.state stage.rightRounds[round]! frame.left
    else Assigned output.state stage.leftOutput frame.left ∧
      Assigned output.state stage.rightOutput (nativeNext constants key round frame)

theorem executeRound_writes (constants : Array Nat) (stage : Feistel) (key round : Nat)
    (frame output : FeistelFrame Assignment)
    (returned : executeFeistelRound constants stage key round frame = .ok output) :
    RoundWrites constants stage key round frame output := by
  unfold executeFeistelRound at returned
  obtain ⟨first, firstBuilt, returned⟩ := bind_success _ _ output returned
  obtain ⟨second, secondBuilt, returned⟩ := bind_success _ _ output returned
  by_cases middle : round < 219
  · simp only [middle, ↓reduceIte] at returned
    obtain ⟨third, thirdBuilt, returned⟩ := bind_success _ _ output returned
    obtain ⟨fourth, fourthBuilt, returned⟩ := bind_success _ _ output returned
    have equal : FeistelFrame.mk fourth _ _ = output := Except.ok.inj returned
    subst output
    have firstSpec := write_success_preserves _ _ _ _ firstBuilt
    have secondSpec := write_success_preserves _ _ _ _ secondBuilt
    have thirdSpec := write_success_preserves _ _ _ _ thirdBuilt
    have fourthSpec := write_success_preserves _ _ _ _ fourthBuilt
    refine ⟨extends_trans (extends_trans (extends_trans firstSpec.2 secondSpec.2) thirdSpec.2) fourthSpec.2,
      fourthSpec.2.2 _ _ (thirdSpec.2.2 _ _ (secondSpec.2.2 _ _ firstSpec.1)),
      fourthSpec.2.2 _ _ (thirdSpec.2.2 _ _ secondSpec.1), ?_⟩
    simp only [middle, ↓reduceIte]
    exact ⟨fourthSpec.2.2 _ _ thirdSpec.1, fourthSpec.1⟩
  · simp only [middle, ↓reduceIte] at returned
    obtain ⟨third, thirdBuilt, returned⟩ := bind_success _ _ output returned
    obtain ⟨fourth, fourthBuilt, returned⟩ := bind_success _ _ output returned
    have equal : FeistelFrame.mk fourth _ _ = output := Except.ok.inj returned
    subst output
    have firstSpec := write_success_preserves _ _ _ _ firstBuilt
    have secondSpec := write_success_preserves _ _ _ _ secondBuilt
    have thirdSpec := write_success_preserves _ _ _ _ thirdBuilt
    have fourthSpec := write_success_preserves _ _ _ _ fourthBuilt
    refine ⟨extends_trans (extends_trans (extends_trans firstSpec.2 secondSpec.2) thirdSpec.2) fourthSpec.2,
      fourthSpec.2.2 _ _ (thirdSpec.2.2 _ _ (secondSpec.2.2 _ _ firstSpec.1)),
      fourthSpec.2.2 _ _ (thirdSpec.2.2 _ _ secondSpec.1), ?_⟩
    simp only [middle, ↓reduceIte]
    exact ⟨fourthSpec.2.2 _ _ thirdSpec.1, fourthSpec.1⟩

theorem executeRoundEffect_extends (constants : Array Nat) (stage : Feistel) (key round : Nat)
    (frame : FeistelFrame Assignment) (next : ForInStep (FeistelFrame Assignment))
    (returned : executeRoundEffect constants stage key round frame = .ok next) :
    Extends frame.state next.value.state := by
  unfold executeRoundEffect at returned
  obtain ⟨output, executed, returned⟩ := bind_success _ _ next returned
  have equal : ForInStep.yield output = next := Except.ok.inj returned
  rw [← equal]
  exact (executeRound_writes constants stage key round frame output executed).1

theorem executeRounds_extends (constants : Array Nat) (stage : Feistel) (key : Nat)
    (items : List Nat) (initial output : FeistelFrame Assignment)
    (returned : ForIn.forIn items initial (executeRoundEffect constants stage key) = .ok output) :
    Extends initial.state output.state := by
  apply LeanCrypto.Proofs.ConstraintCertificate.forIn_success_invariant items
    (executeRoundEffect constants stage key) (fun frame => Extends initial.state frame.state) _
    initial (extends_refl initial.state) output returned
  intro round _ frame previous next effect
  exact extends_trans previous (executeRoundEffect_extends constants stage key round frame next effect)


end TornadoProofs.Witness.Local

#print axioms TornadoProofs.Witness.Local.respects_backwards
#print axioms TornadoProofs.Witness.Local.read_success_assigned
#print axioms TornadoProofs.Witness.Local.executeRound_writes
#print axioms TornadoProofs.Witness.Local.executeRoundEffect_extends
#print axioms TornadoProofs.Witness.Local.executeRounds_extends
