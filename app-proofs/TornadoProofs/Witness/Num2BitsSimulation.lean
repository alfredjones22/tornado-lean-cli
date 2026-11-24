import TornadoProofs.Witness.MetadataState

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.WitnessSymbolic
open Symbolic

def bitPublicStep (resolver : Resolver) (component : Num2BitsComponent)
    (input bit : Nat) (state : SignalState) : Except String (ForInStep SignalState) := do
  let node ← resolver.resolve (.bit input bit)
  let next ← state.write component.outputs[bit]! node
  pure (ForInStep.yield next)

theorem bitPublicStep_source (resolver : Resolver) (component : Num2BitsComponent)
    (input bit : Nat) (state : SignalState) (next : ForInStep SignalState)
    (returned : bitPublicStep resolver component input bit state=.ok next) :
    ∃ node after, resolver.resolve (.bit input bit)=.ok node ∧
      state.write component.outputs[bit]! node=.ok after ∧ next=.yield after := by
  obtain ⟨node,resolved,remaining⟩ := bind_success (resolver.resolve (.bit input bit)) _ next returned
  obtain ⟨after,written,result⟩ := bind_success (state.write component.outputs[bit]! node) _ next remaining
  have equal : ForInStep.yield after=next := by
    simpa only [pure,Except.pure,Except.ok.injEq] using result
  exact ⟨node,after,resolved,written,equal.symm⟩

theorem compileNum2Bits_publicLoop (resolver : Resolver) (state after : SignalState)
    (component : Num2BitsComponent) (input : Nat)
    (returned : compileNum2Bits resolver state component=.ok after)
    (read : state.read component.input=.ok input) :
    component.outputs.size=248 ∧
      forIn (List.range 248) state (bitPublicStep resolver component input)=.ok after := by
  by_cases width : component.outputs.size=248
  · refine ⟨width,?_⟩
    simp only [compileNum2Bits,width,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,read] at returned
    change (forIn (Std.Legacy.Range.mk 0 248 1 (by decide)) state
      (bitPublicStep resolver component input) >>= pure)=.ok after at returned
    rw [bind_pure,forIn_range_zero] at returned
    exact returned
  · simp [compileNum2Bits,width,bind,Except.bind] at returned

theorem compileNum2Bits_read (resolver : Resolver) (state after : SignalState)
    (component : Num2BitsComponent)
    (returned : compileNum2Bits resolver state component=.ok after) :
    ∃ input, state.read component.input=.ok input := by
  by_cases width : component.outputs.size=248
  · cases read : state.read component.input with
    | error err => simp [compileNum2Bits,width,read,bind,Except.bind,pure,Except.pure] at returned
    | ok input => exact ⟨input,rfl⟩
  · simp [compileNum2Bits,width,bind,Except.bind] at returned

theorem compileNum2Bits_extends (resolver : Resolver) (state after : SignalState)
    (component : Num2BitsComponent)
    (returned : compileNum2Bits resolver state component=.ok after) : SignalExtends state after := by
  obtain ⟨input,read⟩ := compileNum2Bits_read resolver state after component returned
  have loop := (compileNum2Bits_publicLoop resolver state after component input returned read).2
  apply LeanCrypto.Proofs.ConstraintCertificate.forIn_success_invariant _ _
    (SignalExtends state) _ state (signalExtends_refl state) after loop
  intro bit member before extension next result
  obtain ⟨node,middle,_,written,equal⟩ := bitPublicStep_source resolver component input bit before next result
  subst next
  exact signalExtends_trans extension (signalWrite_extends before middle _ _ written)

theorem compileNum2Bits_construct (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Denotes resolver.nodes inputs values)
    (canonical : ∀ (index : Nat), values[index]! < Tornado.Protocol.Groth16R1CS.scalarPrime)
    (state after : SignalState) (component : Num2BitsComponent)
    (sourceBound : ∀ input, state.read component.input=.ok input → values[input]! < 2^248)
    (returned : compileNum2Bits resolver state component=.ok after)
    (aliases : AliasesValid after values) :
    AliasesValid state values ∧
      executeNum2Bits (realize state values) component=.ok (realize after values) := by
  obtain ⟨input,read⟩ := compileNum2Bits_read resolver state after component returned
  obtain ⟨width,loop⟩ := compileNum2Bits_publicLoop resolver state after component input returned read
  have backwards : ∀ bit before next, bitPublicStep resolver component input bit before=.ok next →
      AliasesValid (stepValue next) values → AliasesValid before values := by
    intro bit before next result terminal
    obtain ⟨node,middle,_,written,equal⟩ := bitPublicStep_source resolver component input bit before next result
    subst next
    exact signalWrite_aliases_backwards before middle values _ _ written terminal
  have construct : ∀ bit before next, bitPublicStep resolver component input bit before=.ok next →
      AliasesValid (stepValue next) values →
      (do let after ← (realize before values).write component.outputs[bit]! (bitValue values[input]! bit)
          pure (ForInStep.yield after))=.ok (mapStep (fun state => realize state values) next) := by
    intro bit before next result terminal
    obtain ⟨node,middle,resolved,written,equal⟩ := bitPublicStep_source resolver component input bit before next result
    subst next
    have value : values[node]! = bitValue values[input]! bit := by
      simpa only [Node.meaning] using resolve_sound resolver inputs values denotes (.bit input bit) node resolved
    have actual := signalWrite_realize before middle values _ _ written (canonical _) terminal
    rw [← value]
    simp only [actual,bind,Except.bind,pure,Except.pure,mapStep]
  have simulated := forIn_construct_from_public (List.range 248)
    (bitPublicStep resolver component input)
    (fun bit current => do
      let after ← current.write component.outputs[bit]! (bitValue values[input]! bit)
      pure (ForInStep.yield after))
    (fun state => realize state values) (fun state => AliasesValid state values)
    backwards construct state after loop aliases
  refine ⟨simulated.1,?_⟩
  rw [executeNum2Bits_eq_loop (realize state values) component values[input]!
    (signalRead_realize state values component.input input read) width
    (by simpa only [width] using sourceBound input read)]
  simpa only [num2BitsWrites,width,runAssignments_map] using simulated.2

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.bitPublicStep_source
#print axioms TornadoProofs.Witness.Execution.compileNum2Bits_publicLoop
#print axioms TornadoProofs.Witness.Execution.compileNum2Bits_read
#print axioms TornadoProofs.Witness.Execution.compileNum2Bits_extends
#print axioms TornadoProofs.Witness.Execution.compileNum2Bits_construct
