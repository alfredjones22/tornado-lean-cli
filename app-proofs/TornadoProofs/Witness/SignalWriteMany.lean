import TornadoProofs.Witness.SignalMonotone
import TornadoProofs.Witness.CheckedSimulationMem

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.Groth16R1CS

theorem forIn_range_zero {S : Type} (stop : Nat) (state : S)
    (step : Nat → S → Except String (ForInStep S)) :
    forIn (Std.Legacy.Range.mk 0 stop 1 (by decide)) state step =
      forIn (List.range stop) state step := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  rw [← List.range_eq_range']

theorem signalWriteMany_construct (state next : SignalState) (values indices roots : Array Nat)
    (compiled : state.writeMany indices roots = .ok next)
    (canonical : ∀ (index : Nat), values[index]! < scalarPrime)
    (aliases : AliasesValid next values) :
    AliasesValid state values ∧
      ((do
        let mut result := realize state values
        for i in [0:roots.size] do
          result ← result.write indices[i]! (roots.map (values[·]!))[i]!
        return result) : Except String Assignment) = .ok (realize next values) := by
  have count : indices.size=roots.size := by
    by_contra different
    simp [SignalState.writeMany,different,bind,Except.bind] at compiled
  have publicLoop : forIn (List.range roots.size) state (fun i current => do
      let next ← current.write indices[i]! roots[i]!
      pure (ForInStep.yield next)) = .ok next := by
    simp only [SignalState.writeMany,count,bne_self_eq_false,Bool.false_eq_true,
      ↓reduceIte] at compiled
    change (forIn (Std.Legacy.Range.mk 0 roots.size 1 (by decide)) state
      (fun i current => do
        let next ← current.write indices[i]! roots[i]!
        pure (ForInStep.yield next)) >>= pure) = .ok next at compiled
    rw [bind_pure,forIn_range_zero] at compiled
    exact compiled
  have backwards : ∀ i ∈ List.range roots.size, ∀ (before : SignalState) (step : ForInStep SignalState),
      (do let next ← before.write indices[i]! roots[i]!; pure (ForInStep.yield next)) =
        (.ok step : Except String (ForInStep SignalState)) →
      AliasesValid (stepValue step) values → AliasesValid before values := by
    intro i member before step returned terminal
    cases written : before.write indices[i]! roots[i]! with
    | error err => simp [written,bind,Except.bind] at returned
    | ok middle =>
      simp only [written,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at returned
      cases returned
      exact signalWrite_aliases_backwards before middle values _ _ written terminal
  have construct : ∀ i ∈ List.range roots.size, ∀ (before : SignalState) (step : ForInStep SignalState),
      (do let next ← before.write indices[i]! roots[i]!; pure (ForInStep.yield next)) =
        (.ok step : Except String (ForInStep SignalState)) →
      AliasesValid (stepValue step) values →
      (do let next ← (realize before values).write indices[i]! (roots.map (values[·]!))[i]!
          pure (ForInStep.yield next)) = .ok (mapStep (fun state => realize state values) step) := by
    intro i member before step returned terminal
    have bound : i<roots.size := List.mem_range.mp member
    cases written : before.write indices[i]! roots[i]! with
    | error err => simp [written,bind,Except.bind] at returned
    | ok middle =>
      simp only [written,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at returned
      cases returned
      have actual := signalWrite_realize before middle values _ _ written (canonical _) terminal
      have mapValue : (roots.map (values[·]!))[i]! = values[roots[i]!]! := by
        simp [getElem!_pos,bound]
      simp only [mapValue,actual,bind,Except.bind,pure,Except.pure,mapStep]
  have simulation := forIn_construct_from_public_mem (List.range roots.size) _
    (fun i (current : Assignment) => do
      let next ← current.write indices[i]! (roots.map (values[·]!))[i]!
      pure (ForInStep.yield next))
    (fun state => realize state values) (fun state => AliasesValid state values)
    backwards construct state next publicLoop aliases
  refine ⟨simulation.1,?_⟩
  simpa only [forIn_range_zero,pure_bind,bind_pure] using simulation.2

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.forIn_range_zero
#print axioms TornadoProofs.Witness.Execution.signalWriteMany_construct
