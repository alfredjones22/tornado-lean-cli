import TornadoProofs.Witness.FeistelRowSupport

set_option autoImplicit false

namespace TornadoProofs.Witness.Local

open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open TornadoProofs.Witness.Execution

theorem compileFeistelRound_signalExtends (resolver : Resolver) (constants : Array Nat)
    (stage : Feistel) (key round : Nat) (frame output : FeistelFrame SignalState)
    (compiled : compileFeistelRound resolver constants stage key round frame = .ok output) :
    SignalExtends frame.state output.state := by
  unfold compileFeistelRound at compiled
  obtain ⟨constant, _, compiled⟩ := bind_success _ _ output compiled
  obtain ⟨keyed, _, compiled⟩ := bind_success _ _ output compiled
  obtain ⟨t, _, compiled⟩ := bind_success _ _ output compiled
  obtain ⟨square, _, compiled⟩ := bind_success _ _ output compiled
  obtain ⟨fourth, _, compiled⟩ := bind_success _ _ output compiled
  obtain ⟨fifth, _, compiled⟩ := bind_success _ _ output compiled
  obtain ⟨first, firstBuilt, compiled⟩ := bind_success _ _ output compiled
  obtain ⟨second, secondBuilt, compiled⟩ := bind_success _ _ output compiled
  obtain ⟨next, _, compiled⟩ := bind_success _ _ output compiled
  by_cases middle : round < 219
  · simp only [middle, ↓reduceIte] at compiled
    obtain ⟨third, thirdBuilt, compiled⟩ := bind_success _ _ output compiled
    obtain ⟨fourthState, fourthBuilt, compiled⟩ := bind_success _ _ output compiled
    have equal : FeistelFrame.mk fourthState _ _ = output := Except.ok.inj compiled
    subst output
    exact signalExtends_trans (signalExtends_trans (signalExtends_trans
      (signalWrite_extends _ _ _ _ firstBuilt) (signalWrite_extends _ _ _ _ secondBuilt))
      (signalWrite_extends _ _ _ _ thirdBuilt)) (signalWrite_extends _ _ _ _ fourthBuilt)
  · simp only [middle, ↓reduceIte] at compiled
    obtain ⟨third, thirdBuilt, compiled⟩ := bind_success _ _ output compiled
    obtain ⟨fourthState, fourthBuilt, compiled⟩ := bind_success _ _ output compiled
    have equal : FeistelFrame.mk fourthState _ _ = output := Except.ok.inj compiled
    subst output
    exact signalExtends_trans (signalExtends_trans (signalExtends_trans
      (signalWrite_extends _ _ _ _ firstBuilt) (signalWrite_extends _ _ _ _ secondBuilt))
      (signalWrite_extends _ _ _ _ thirdBuilt)) (signalWrite_extends _ _ _ _ fourthBuilt)

theorem compileRoundEffect_signalExtends (resolver : Resolver) (constants : Array Nat) (stage : Feistel)
    (key round : Nat) (frame : FeistelFrame SignalState) (next : ForInStep (FeistelFrame SignalState))
    (compiled : compileRoundEffect resolver constants stage key round frame = .ok next) :
    SignalExtends frame.state next.value.state := by
  unfold compileRoundEffect at compiled
  obtain ⟨output, built, compiled⟩ := bind_success _ _ next compiled
  have equal : ForInStep.yield output = next := Except.ok.inj compiled
  rw [← equal]
  exact compileFeistelRound_signalExtends resolver constants stage key round frame output built

theorem compileFeistel_signalExtends (resolver : Resolver) (constants : Array Nat) (state after : SignalState)
    (stage : Feistel) (compiled : compileFeistel resolver constants state stage = .ok after) :
    SignalExtends state after := by
  rw [compileFeistel_source] at compiled
  unfold compileFeistelBody at compiled
  by_cases invalid : (constants.size != 220 || !stage.layoutValid state.slots.size) = true
  · simp only [invalid, ↓reduceIte] at compiled
    change (Except.error "Public witness DAG Feistel layout or constants are invalid." : Except String SignalState) = .ok after at compiled
    contradiction
  · have validFalse : (constants.size != 220 || !stage.layoutValid state.slots.size) = false := Bool.eq_false_iff.mpr invalid
    simp only [validFalse, Bool.false_eq_true, ↓reduceIte] at compiled
    change (do
      let key ← state.read stage.key
      let left ← state.read stage.leftInput
      let right ← state.read stage.rightInput
      let frame ← ForIn.forIn (List.range 220) (FeistelFrame.mk state left right)
        (compileRoundEffect resolver constants stage key)
      pure frame.state) = .ok after at compiled
    obtain ⟨key, _, compiled⟩ := bind_success _ _ after compiled
    obtain ⟨left, _, compiled⟩ := bind_success _ _ after compiled
    obtain ⟨right, _, compiled⟩ := bind_success _ _ after compiled
    obtain ⟨final, rounds, compiled⟩ := bind_success _ _ after compiled
    have equal : final.state = after := Except.ok.inj compiled
    rw [← equal]
    apply LeanCrypto.Proofs.ConstraintCertificate.forIn_success_invariant (List.range 220)
      (compileRoundEffect resolver constants stage key) (fun frame => SignalExtends state frame.state) _
      (FeistelFrame.mk state left right) (signalExtends_refl state) final rounds
    intro round _ before previous next effect
    exact signalExtends_trans previous (compileRoundEffect_signalExtends resolver constants stage key round before next effect)

end TornadoProofs.Witness.Local

#print axioms TornadoProofs.Witness.Local.compileFeistelRound_signalExtends
#print axioms TornadoProofs.Witness.Local.compileRoundEffect_signalExtends
#print axioms TornadoProofs.Witness.Local.compileFeistel_signalExtends
