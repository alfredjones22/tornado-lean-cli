import TornadoProofs.Witness.BuilderSpec
import TornadoProofs.Witness.BabyJubjubEdwardsAdd
import TornadoProofs.Witness.FootprintMeaning
import TornadoProofs.Witness.PrimitiveCompiler

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BN254Fr

/-- Meaning of the exact two ordered DAG roots returned by the public builder. -/
def MontgomeryMeaning (values : Array Nat) (reference : PointRef) (point : Point) : Prop :=
  ∃ equation : Montgomery (model values[reference.1]!) (model values[reference.2]!),
    montgomeryPoint _ _ equation=point

def EdwardsMeaning (values : Array Nat) (reference : PointRef) (point : Point) : Prop :=
  ∃ equation : Edwards (model values[reference.1]!) (model values[reference.2]!),
    toMontgomery ⟨model values[reference.1]!,model values[reference.2]!,equation⟩=point

theorem kind_tag_injective {first second : Primitive.Kind} (equal : first.tag=second.tag) : first=second := by
  cases first <;> cases second <;> simp_all [Primitive.Kind.tag]

theorem admitted_push (values : Array Nat) (steps : Array Footprint) (kind : Primitive.Kind)
    (inputs outputs : Array Nat) (prior : Execution.StepsAdmitted values steps)
    (admitted : kind.Admitted (inputs.map (values[·]!))) :
    Execution.StepsAdmitted values (steps.push ⟨kind.tag,inputs,outputs⟩) := by
  intro footprint member other tag
  rcases Array.mem_push.mp member with member | equal
  · exact prior footprint member other tag
  · subst footprint
    have same : kind=other := kind_tag_injective tag
    subst other
    exact admitted

theorem operation_source (resolver : Resolver) (kind : String) (inputs outputs : Array Nat)
    (initial final : Array Footprint)
    (returned : operation resolver kind inputs initial=.ok (outputs,final)) :
    compilePrimitive resolver kind inputs=.ok outputs ∧ final=initial.push ⟨kind,inputs,outputs⟩ := by
  dsimp only [operation,bind,StateT.bind,liftM,StateT.lift,Functor.map,StateT.map,
    modify,modifyGet,StateT.modifyGet,StateT.pure,pure,Except.bind,Except.pure] at returned
  dsimp only [MonadLiftT.monadLift,MonadLift.monadLift,MonadStateOf.modifyGet,
    StateT.lift,StateT.modifyGet,bind,pure,Except.bind,Except.pure] at returned
  cases compiled : compilePrimitive resolver kind inputs with
  | error error =>
    simp only [compiled] at returned
    cases returned
  | ok built =>
    have equal : (built,initial.push ⟨kind,inputs,built⟩)=(outputs,final) := by
      simpa only [compiled,Except.ok.injEq] using returned
    cases equal
    exact ⟨rfl,rfl⟩

theorem operation_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (kind : Primitive.Kind)
    (inputIDs : Array Nat) (size : inputIDs.size=kind.inputCount)
    (admitted : kind.Admitted (inputIDs.map (values[·]!))) :
    BuildSpec (Execution.StepsAdmitted values) (operation resolver kind.tag inputIDs)
      (fun outputIDs => outputIDs.map (values[·]!)=kind.values (inputIDs.map (values[·]!))) := by
  intro initial outputIDs final prior returned
  obtain ⟨compiled,rfl⟩ := operation_source resolver kind.tag inputIDs outputIDs initial final returned
  exact ⟨admitted_push values initial kind inputIDs outputIDs prior admitted,
    Primitive.compilePrimitive_values resolver inputs values denotes kind inputIDs outputIDs size admitted compiled⟩

theorem mapped_index (values ids actual : Array Nat) (mapped : ids.map (values[·]!)=actual)
    (index : Nat) (bound : index < actual.size) : values[ids[index]!]! =actual[index]! := by
  have size := congrArg Array.size mapped
  simp only [Array.size_map] at size
  have valid : index < ids.size := by omega
  have validMap : index < (ids.map (values[·]!)).size := by simpa only [Array.size_map] using valid
  calc
    values[ids[index]!]! =(ids.map (values[·]!))[index]! := by
      simp only [getElem!_pos ids index valid,getElem!_pos (ids.map (values[·]!)) index validMap,Array.getElem_map]
    _ =actual[index]! := by rw [mapped]

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.kind_tag_injective
#print axioms TornadoProofs.Witness.PedersenReference.admitted_push
#print axioms TornadoProofs.Witness.PedersenReference.operation_source
#print axioms TornadoProofs.Witness.PedersenReference.operation_spec
#print axioms TornadoProofs.Witness.PedersenReference.mapped_index
