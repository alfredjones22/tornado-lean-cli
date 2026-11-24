import TornadoProofs.Witness.FeistelRows
import TornadoProofs.Witness.FeistelSignalExtends

set_option autoImplicit false

namespace TornadoProofs.Witness.Local

open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open TornadoProofs.Witness.Execution
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr

theorem interpreted_read (state : SignalState) (assignment : Nat → Fr) (values : Array Nat)
    (interpreted : SignalInterpretation state assignment values) (index node : Nat)
    (read : state.read index = .ok node) : assignment index = model values[node]! :=
  signalInterpretation_assigned state assignment values interpreted index values[node]!
    (read_success_assigned (realize state values) index values[node]! (signalRead_realize state values index node read))

theorem interpreted_write (state after : SignalState) (assignment : Nat → Fr) (values : Array Nat)
    (canonical : Primitive.Bounded values) (index node : Nat) (written : state.write index node = .ok after)
    (aliases : AliasesValid after values) (interpreted : SignalInterpretation after assignment values) :
    assignment index = model values[node]! := by
  have runtime := (signalWrite_construct state after values canonical index node written aliases).2
  exact signalInterpretation_assigned after assignment values interpreted index values[node]!
    (write_success_preserves (realize state values) (realize after values) index values[node]! runtime).1

theorem compileDualMux_details (resolver : Resolver) (state : SignalState) (level : MerkleLevel)
    (output : SignalState × Nat × Nat) (compiled : compileDualMux resolver state level = .ok output) :
    ∃ left right selector first, state.read level.leftInput = .ok left ∧
      state.read level.rightInput = .ok right ∧ state.read level.selector = .ok selector ∧
      resolver.resolve (.select selector left right) = .ok output.2.1 ∧
      resolver.resolve (.select selector right left) = .ok output.2.2 ∧
      state.write level.leftOutput output.2.1 = .ok first ∧
      first.write level.rightOutput output.2.2 = .ok output.1 := by
  unfold compileDualMux at compiled
  obtain ⟨left, leftRead, compiled⟩ := bind_success _ _ output compiled
  obtain ⟨right, rightRead, compiled⟩ := bind_success _ _ output compiled
  obtain ⟨selector, selectorRead, compiled⟩ := bind_success _ _ output compiled
  obtain ⟨leftOutput, leftResolved, compiled⟩ := bind_success _ _ output compiled
  obtain ⟨rightOutput, rightResolved, compiled⟩ := bind_success _ _ output compiled
  obtain ⟨first, firstWritten, compiled⟩ := bind_success _ _ output compiled
  obtain ⟨second, secondWritten, compiled⟩ := bind_success _ _ output compiled
  have equal : (second, leftOutput, rightOutput) = output := Except.ok.inj compiled
  subst output
  exact ⟨left, right, selector, first, leftRead, rightRead, selectorRead, leftResolved, rightResolved, firstWritten, secondWritten⟩

theorem dualMux_field_equations (selector left right : Nat) (binary : selector ≤ 1) :
    (model right - model left) * model selector =
        model (dualMuxValues selector left right).1 - model left ∧
      (model left - model right) * model selector =
        model (dualMuxValues selector left right).2 - model right ∧
      model selector * (model selector - 1) = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp binary with zero | one
  · subst selector
    simp [dualMuxValues, model]
  · subst selector
    simp [dualMuxValues, model]

end TornadoProofs.Witness.Local

#print axioms TornadoProofs.Witness.Local.interpreted_read
#print axioms TornadoProofs.Witness.Local.interpreted_write
#print axioms TornadoProofs.Witness.Local.compileDualMux_details
#print axioms TornadoProofs.Witness.Local.dualMux_field_equations
