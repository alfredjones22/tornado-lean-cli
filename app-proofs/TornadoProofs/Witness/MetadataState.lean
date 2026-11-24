import TornadoProofs.Witness.PrimitiveSimulation
import TornadoProofs.Witness.SignalRows
import TornadoProofs.Witness.FeistelSupport
import LeanCryptoProofs.ConstraintCertificate.CheckedLoops

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.WitnessSymbolic

def NodeFits (compiled : CompiledGraph) (state : SignalState) : Prop :=
  ∀ (index node : Nat), state.slots[index]?=some (some node) → compiled.signalRoots[index]! = node

theorem signalRead_slot (state : SignalState) (index node : Nat)
    (returned : state.read index=.ok node) : state.slots[index]?=some (some node) := by
  by_cases out : index>=state.slots.size
  · simp [SignalState.read,out,bind,Except.bind] at returned
  have bound : index<state.slots.size := by omega
  cases slot : state.slots[index]! with
  | none => simp [SignalState.read,out,slot,bind,Except.bind,pure,Except.pure] at returned
  | some prior =>
    have equal : prior=node := by
      simpa [SignalState.read,out,slot,bind,Except.bind,pure,Except.pure] using returned
    subst prior
    rw [getElem!_pos state.slots index bound] at slot
    simpa only [Array.getElem?_eq_getElem bound] using congrArg some slot

theorem nodeFits_backwards (compiled : CompiledGraph) (before after : SignalState)
    (extension : SignalExtends before after) (fit : NodeFits compiled after) : NodeFits compiled before := by
  intro index node assigned
  exact fit index node (extension.2 index node assigned)

theorem nodeFits_inputs (compiled : CompiledGraph) (state : SignalState)
    (fit : NodeFits compiled state) (indices roots : Array Nat)
    (returned : indices.mapM state.read=.ok roots) : roots=indices.map (compiled.signalRoots[·]!) := by
  have mapped := arrayMapM_value state.read indices roots (compiled.signalRoots[·]!) id
    (fun index root read => (fit index root (signalRead_slot state index root read)).symm) returned
  simpa only [Array.map_id] using mapped

theorem forIn_backwards {A S : Type} (items : List A)
    (step : A → S → Except String (ForInStep S)) (predicate : S → Prop)
    (backwards : ∀ item before next, step item before=.ok next →
      predicate (stepValue next) → predicate before)
    (initial final : S) (returned : forIn items initial step=.ok final)
    (terminal : predicate final) : predicate initial := by
  have simulation := forIn_construct_from_public items step step id predicate backwards
    (fun _ _ next known _ => by cases next <;> simpa only [mapStep,id_eq] using known)
    initial final returned terminal
  exact simulation.1

theorem signalWriteMany_extends (state after : SignalState) (indices roots : Array Nat)
    (returned : state.writeMany indices roots=.ok after) : SignalExtends state after := by
  have count : indices.size=roots.size := by
    by_contra different
    simp [SignalState.writeMany,different,bind,Except.bind] at returned
  simp only [SignalState.writeMany,count,bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at returned
  change (forIn (Std.Legacy.Range.mk 0 roots.size 1 (by decide)) state (fun i current => do
    let next ← current.write indices[i]! roots[i]!
    pure (ForInStep.yield next)) >>= pure)=.ok after at returned
  rw [bind_pure,forIn_range_zero] at returned
  apply LeanCrypto.Proofs.ConstraintCertificate.forIn_success_invariant _ _
    (SignalExtends state) _ state (signalExtends_refl state) after returned
  intro index member before extension next result
  cases written : before.write indices[index]! roots[index]! with
  | error err => simp [written,bind,Except.bind] at result
  | ok middle =>
    simp only [written,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at result
    cases result
    exact signalExtends_trans extension (signalWrite_extends before middle _ _ written)

theorem compilePrimitiveStage_extends (resolver : Resolver) (state after : SignalState)
    (primitive : Tornado.Protocol.WitnessVM.Primitive)
    (returned : compilePrimitiveStage resolver state primitive=.ok after) : SignalExtends state after := by
  by_cases shape : primitive.shapeValid state.slots.size=true
  · cases read : primitive.inputs.mapM state.read with
    | error err => simp [compilePrimitiveStage,shape,read,bind,Except.bind,pure,Except.pure] at returned
    | ok inputs =>
      cases built : compilePrimitive resolver primitive.kind inputs with
      | error err => simp [compilePrimitiveStage,shape,read,built,bind,Except.bind,pure,Except.pure] at returned
      | ok outputs =>
        apply signalWriteMany_extends state after primitive.outputs outputs
        simpa [compilePrimitiveStage,shape,read,built,bind,Except.bind,pure,Except.pure] using returned
  · have invalid := Bool.eq_false_of_not_eq_true shape
    simp [compilePrimitiveStage,invalid,bind,Except.bind] at returned

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.signalRead_slot
#print axioms TornadoProofs.Witness.Execution.nodeFits_backwards
#print axioms TornadoProofs.Witness.Execution.nodeFits_inputs
#print axioms TornadoProofs.Witness.Execution.forIn_backwards
#print axioms TornadoProofs.Witness.Execution.signalWriteMany_extends
#print axioms TornadoProofs.Witness.Execution.compilePrimitiveStage_extends
