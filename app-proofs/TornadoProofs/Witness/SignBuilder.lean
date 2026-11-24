import TornadoProofs.Witness.MuxBuilder

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BN254Fr

theorem signed_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (commitment : Bool)
    (reference : PointRef) (point : Point) (sign bit : Nat)
    (meaning : MontgomeryMeaning values reference point) (signMeaning : BitMeaning values sign bit)
    (binary : bit < 2) :
    BuildSpec (Execution.StepsAdmitted values) ((compilerWindows resolver commitment).signed reference sign)
      (fun result => MontgomeryMeaning values result (if bit=0 then point else -point)) := by
  let ids := #[reference.2,sign]
  let i := ids.map (values[·]!)
  have signValue : i[1]! = bit := by simpa [i,ids,BitMeaning] using signMeaning
  have admitted : Primitive.Kind.window4.Admitted i := by change i[1]! < 2; rw [signValue]; exact binary
  change BuildSpec _ (do
    let outputs ← operation resolver Primitive.Kind.window4.tag ids
    return (reference.1,outputs[0]!)) _
  apply buildSpec_bind _ _ _ _ _ (operation_spec resolver inputs values denotes .window4 ids rfl admitted)
  intro outputs mapped
  apply buildSpec_pure
  obtain ⟨curve,group⟩ := meaning
  have y := mapped_index values outputs (Primitive.window4 i)
    (by simpa only [Primitive.Kind.values] using mapped) 0 (by change 0<1; omega)
  have equation := PedersenWindows.window4_sign_model i (by rw [signValue]; exact binary)
  rw [signValue] at equation
  have firstValue : i[0]! = values[reference.2]! := by simp [i,ids]
  rw [firstValue] at equation
  have yModel : model values[outputs[0]!]! = if bit=0 then model values[reference.2]! else -model values[reference.2]! := by
    rw [y]
    exact equation
  by_cases zero : bit=0
  · rw [if_pos zero] at yModel ⊢
    refine ⟨by rw [yModel]; exact curve,?_⟩
    simpa only [yModel] using group
  · rw [if_neg zero] at yModel ⊢
    refine ⟨by rw [yModel]; exact montgomery_neg_curve _ _ curve,?_⟩
    have negation := montgomeryPoint_neg _ _ curve
    simpa only [yModel,group] using negation

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.signed_spec
