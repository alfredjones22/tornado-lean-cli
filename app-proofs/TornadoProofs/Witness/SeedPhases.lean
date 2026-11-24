import TornadoProofs.Witness.BasePhases

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

def seedPublicAction (resolver : Resolver) (index : Nat) (state : SignalState) : Except String SignalState := do
  let node ← if index == 0 then resolver.resolve (.constant 1) else resolver.resolve (.input index)
  state.write index node

theorem seed_stage_construct (resolver : Resolver) (data inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes data values)
    (canonical : ∀ (index : Nat), values[index]! < Tornado.Protocol.Groth16R1CS.scalarPrime)
    (index : Nat) (agreement : data[index]! = inputs[index]!) (constant : inputs[0]! = 1)
    (finalRoots : CompiledGraph) (state after : SignalState)
    (compiled : seedPublicAction resolver index state=.ok after)
    (terminal : SourceState finalRoots values after) :
    SourceState finalRoots values state ∧
      (realize state values).write index inputs[index]! = .ok (realize after values) := by
  let request : Node := if index==0 then .constant 1 else .input index
  have factored : seedPublicAction resolver index state = (do
      let node ← resolver.resolve request
      state.write index node) := by
    unfold seedPublicAction
    dsimp [request]
    split <;> rfl
  rw [factored] at compiled
  obtain ⟨node,built,written⟩ := bind_success _ _ after compiled
  have value : values[node]! = inputs[index]! := by
    by_cases zero : index=0
    · subst index
      simp only [request,beq_self_eq_true,↓reduceIte] at built
      have resolved := Symbolic.resolve_sound resolver data values denotes (.constant 1) node built
      simpa only [constant] using resolved
    · have nonzero : (index==0)=false := beq_eq_false_iff_ne.mpr zero
      simp only [request,nonzero,Bool.false_eq_true,↓reduceIte] at built
      exact (Symbolic.resolve_sound resolver data values denotes (.input index) node built).trans agreement
  have actual := signalWrite_realize state after values index node written (canonical _) terminal.1
  refine ⟨⟨signalWrite_aliases_backwards state after values _ _ written terminal.1,
    nodeFits_backwards finalRoots state after (signalWrite_extends state after _ _ written) terminal.2⟩,?_⟩
  simpa only [value] using actual

theorem seed_phase_construct (resolver : Resolver) (data inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes data values)
    (canonical : ∀ (index : Nat), values[index]! < Tornado.Protocol.Groth16R1CS.scalarPrime)
    (agreement : ∀ (index : Nat), index<49 → data[index]! = inputs[index]!) (constant : inputs[0]! = 1)
    (finalRoots : CompiledGraph) (state after : SignalState)
    (compiled : forIn (List.range 49) state (fun index current => do
      let next ← seedPublicAction resolver index current
      pure (ForInStep.yield next))=.ok after)
    (terminal : SourceState finalRoots values after) :
    SourceState finalRoots values state ∧
      forIn (List.range 49) (realize state values) (fun index current => do
        let next ← current.write index inputs[index]!
        pure (ForInStep.yield next))=.ok (realize after values) := by
  apply forIn_construct_from_public_mem (List.range 49) _ _ (fun state => realize state values)
    (SourceState finalRoots values) _ _ state after compiled terminal
  · intro index member before next returned terminal
    obtain ⟨middle,built,rest⟩ := bind_success (seedPublicAction resolver index before) _ next returned
    have same : ForInStep.yield middle=next := by simpa only [pure,Except.pure,Except.ok.injEq] using rest
    subst next
    exact (seed_stage_construct resolver data inputs values denotes canonical index
      (agreement index (List.mem_range.mp member)) constant finalRoots before middle built terminal).1
  · intro index member before next returned terminal
    obtain ⟨middle,built,rest⟩ := bind_success (seedPublicAction resolver index before) _ next returned
    have same : ForInStep.yield middle=next := by simpa only [pure,Except.pure,Except.ok.injEq] using rest
    subst next
    have actual := (seed_stage_construct resolver data inputs values denotes canonical index
      (agreement index (List.mem_range.mp member)) constant finalRoots before middle built terminal).2
    simp only [actual,bind,Except.bind,pure,Except.pure,mapStep]

theorem commitment_construct (resolver : Resolver) (data values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes data values)
    (canonical : ∀ (index : Nat), values[index]! < Tornado.Protocol.Groth16R1CS.scalarPrime)
    (commitment : Nat) (agreement : data[49]! = commitment) (signal : Nat)
    (finalRoots : CompiledGraph) (state after : SignalState) (node : Nat)
    (resolved : resolver.resolve (.input 49)=.ok node)
    (written : state.write signal node=.ok after)
    (terminal : SourceState finalRoots values after) :
    SourceState finalRoots values state ∧
      (realize state values).write signal commitment=.ok (realize after values) := by
  have value : values[node]! = commitment :=
    (Symbolic.resolve_sound resolver data values denotes (.input 49) node resolved).trans agreement
  have actual := signalWrite_realize state after values signal node written (canonical _) terminal.1
  refine ⟨⟨signalWrite_aliases_backwards state after values _ _ written terminal.1,
    nodeFits_backwards finalRoots state after (signalWrite_extends state after _ _ written) terminal.2⟩,?_⟩
  simpa only [value] using actual

theorem realize_empty (size : Nat) (values : Array Nat) :
    realize (SignalState.empty size) values=Assignment.empty size := by
  simp [realize,SignalState.empty,Assignment.empty]

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.seed_stage_construct
#print axioms TornadoProofs.Witness.Execution.seed_phase_construct
#print axioms TornadoProofs.Witness.Execution.commitment_construct
#print axioms TornadoProofs.Witness.Execution.realize_empty
