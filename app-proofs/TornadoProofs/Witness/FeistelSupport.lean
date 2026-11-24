import TornadoProofs.Witness.CheckedSimulation
import TornadoProofs.Witness.Expressions
import TornadoProofs.Witness.SignalMonotone

set_option autoImplicit false

namespace TornadoProofs.Witness.Execution

open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.Groth16R1CS

theorem bind_success {A B : Type} (effect : Except String A) (next : A → Except String B)
    (output : B) (returned : effect >>= next = .ok output) :
    ∃ value, effect = .ok value ∧ next value = .ok output := by
  cases effect with
  | error failure => contradiction
  | ok value => exact ⟨value, rfl, returned⟩

theorem canonical_lookup (values : Array Nat) (canonical : Primitive.Bounded values) (index : Nat) :
    values[index]! < scalarPrime := by
  by_cases bounded : index < values.size
  · rw [getElem!_pos values index bounded]
    exact canonical values[index] (Array.mem_toList_iff.mpr (Array.getElem_mem bounded))
  · rw [getElem!_neg values index bounded]
    exact (by decide : 0 < scalarPrime)

theorem signalWrite_construct (state next : SignalState) (values : Array Nat)
    (canonical : Primitive.Bounded values) (index node : Nat)
    (written : state.write index node = .ok next) (aliases : AliasesValid next values) :
    AliasesValid state values ∧
      (realize state values).write index values[node]! = .ok (realize next values) :=
  ⟨signalWrite_aliases_backwards state next values index node written aliases,
    signalWrite_realize state next values index node written (canonical_lookup values canonical node) aliases⟩

end TornadoProofs.Witness.Execution

#print axioms TornadoProofs.Witness.Execution.bind_success
#print axioms TornadoProofs.Witness.Execution.canonical_lookup
#print axioms TornadoProofs.Witness.Execution.signalWrite_construct
