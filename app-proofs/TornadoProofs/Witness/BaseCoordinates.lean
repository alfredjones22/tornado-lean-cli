import TornadoProofs.Witness.InputConstruction
import LeanCryptoProofs.BabyJubjub.NativePedersenNotes
import Tornado.Protocol.PublicWitnessCertificate

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic Tornado.Protocol.PedersenSchedule
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BN254Fr
open Execution

def referenceScheduleInline (resolver : Resolver) (graph : SelectedGraph) : Except String Reference := do
  if graph.bases.map BaseSeed.index != #[28551,28552,30747,30748,32867,32868,33871,33872,35967,35968] then
    throw "Pedersen reference base slots differ."
  let x0 ← resolver.resolve (.constant graph.bases[0]!.value)
  let y0 ← resolver.resolve (.constant graph.bases[1]!.value)
  let x1 ← resolver.resolve (.constant graph.bases[2]!.value)
  let y1 ← resolver.resolve (.constant graph.bases[3]!.value)
  let x2 ← resolver.resolve (.constant graph.bases[4]!.value)
  let y2 ← resolver.resolve (.constant graph.bases[5]!.value)
  let ((commitment,nullifier),steps) ← (referenceProgram resolver #[(x0,y0),(x1,y1),(x2,y2)]).run #[]
  return ⟨commitment,nullifier,steps⟩

theorem referenceSchedule_inline (resolver : Resolver) (graph : SelectedGraph) :
    referenceSchedule resolver graph=referenceScheduleInline resolver graph := by
  unfold referenceSchedule referenceScheduleInline
  simp only [forIn_range_zero, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.forIn_cons, List.forIn_nil, bind_assoc, pure_bind]
  rfl

theorem referenceSchedule_nodes (resolver : Resolver) (graph : SelectedGraph) (reference : Reference)
    (returned : referenceSchedule resolver graph=.ok reference) :
    ∃ x0 y0 x1 y1 x2 y2,
      resolver.resolve (.constant graph.bases[0]!.value)=.ok x0 ∧
      resolver.resolve (.constant graph.bases[1]!.value)=.ok y0 ∧
      resolver.resolve (.constant graph.bases[2]!.value)=.ok x1 ∧
      resolver.resolve (.constant graph.bases[3]!.value)=.ok y1 ∧
      resolver.resolve (.constant graph.bases[4]!.value)=.ok x2 ∧
      resolver.resolve (.constant graph.bases[5]!.value)=.ok y2 ∧
      (referenceProgram resolver #[(x0,y0),(x1,y1),(x2,y2)]).run #[]=
        .ok ((reference.commitment,reference.nullifier),reference.steps) := by
  rw [referenceSchedule_inline] at returned
  unfold referenceScheduleInline at returned
  split at returned
  · cases returned
  · simp only [pure_bind] at returned
    obtain ⟨x0,b0,returned⟩ := bind_success _ _ _ returned
    obtain ⟨y0,b1,returned⟩ := bind_success _ _ _ returned
    obtain ⟨x1,b2,returned⟩ := bind_success _ _ _ returned
    obtain ⟨y1,b3,returned⟩ := bind_success _ _ _ returned
    obtain ⟨x2,b4,returned⟩ := bind_success _ _ _ returned
    obtain ⟨y2,b5,returned⟩ := bind_success _ _ _ returned
    obtain ⟨⟨⟨commitment,nullifier⟩,steps⟩,program,returned⟩ := bind_success _ _ _ returned
    have equal : Reference.mk commitment nullifier steps=reference := Except.ok.inj returned
    cases equal
    exact ⟨x0,y0,x1,y1,x2,y2,b0,b1,b2,b3,b4,b5,program⟩

def receiptCoordinates (graph : SelectedGraph) (bases : CertifiedPedersenBases graph) : Array (Nat×Nat) :=
  #[(bases.first.x,bases.first.y),(bases.second.x,bases.second.y),(bases.third.x,bases.third.y)]

theorem certifiedRaw_edwards (index : Nat) (receipt : LeanCrypto.Pedersen.CertifiedGenerator index) :
    ∃ curve : Edwards (model receipt.x) (model receipt.y),
      toMontgomery ⟨model receipt.x,model receipt.y,curve⟩=groupPoint (certifiedRaw index receipt) := by
  have valid := (certifiedRaw_source index receipt).2.1
  have affine := (certifiedRaw_source index receipt).2.2.1
  have equal := Option.some.inj ((native_affine_construct _ valid).symm.trans affine)
  have x := congrArg (fun pair : Nat×Nat => model pair.1) equal
  have y := congrArg (fun pair : Nat×Nat => model pair.2) equal
  simp only [model_val] at x y
  have curve : Edwards (model receipt.x) (model receipt.y) := by
    rw [← x,← y]
    exact normalized_curve _ valid
  refine ⟨curve,?_⟩
  rw [groupPoint_admitted _ valid]
  apply congrArg toMontgomery
  apply epoint_ext
  · exact x.symm
  · exact y.symm

theorem certifiedBase_coordinate (graph : SelectedGraph) (bases : CertifiedPedersenBases graph)
    (index : Nat) (bound : index<10) :
    graph.bases[index]!.value=(pedersenSeedCoordinates bases.first bases.second bases.third)[index]!.2 := by
  have size : graph.bases.size=10 := by
    have equal := congrArg Array.size bases.binding
    simpa only [Array.size_map,pedersenSeedCoordinates] using equal
  have actual : index<graph.bases.size := by omega
  have mapped : index<(graph.bases.map fun base => (base.index,base.value)).size := by
    simpa only [Array.size_map] using actual
  have equal := congrArg (fun coordinates : Array (Nat×Nat) => coordinates[index]!.2) bases.binding
  simpa only [getElem!_pos (graph.bases.map fun base => (base.index,base.value)) index mapped,
    Array.getElem_map,getElem!_pos graph.bases index actual] using equal

theorem receiptCoordinates_edwards (graph : SelectedGraph) (bases : CertifiedPedersenBases graph)
    (index : Nat) (bound : index<3) :
    ∃ curve : Edwards (model (receiptCoordinates graph bases)[index]!.1)
        (model (receiptCoordinates graph bases)[index]!.2),
      toMontgomery ⟨model (receiptCoordinates graph bases)[index]!.1,
        model (receiptCoordinates graph bases)[index]!.2,curve⟩=
          groupPoint (firstThreeGenerators bases.first bases.second bases.third index) := by
  interval_cases index
  · simpa only [receiptCoordinates,firstThreeGenerators,dif_pos (by decide : 0<3),firstThreeReceipts]
      using certifiedRaw_edwards 0 bases.first
  · simpa only [receiptCoordinates,firstThreeGenerators,dif_pos (by decide : 1<3),firstThreeReceipts]
      using certifiedRaw_edwards 1 bases.second
  · simpa only [receiptCoordinates,firstThreeGenerators,dif_pos (by decide : 2<3),firstThreeReceipts]
      using certifiedRaw_edwards 2 bases.third

theorem referenceSchedule_base_coordinates (resolver : Resolver) (graph : SelectedGraph)
    (inputs values : Array Nat) (denotes : Symbolic.Denotes resolver.nodes inputs values)
    (certified : CertifiedPedersenBases graph) (reference : Reference)
    (returned : referenceSchedule resolver graph=.ok reference) :
    ∃ bases : Array PointRef, bases.size=3 ∧
      (referenceProgram resolver bases).run #[]=
        .ok ((reference.commitment,reference.nullifier),reference.steps) ∧
      ∀ index<3, values[bases[index]!.1]! = (receiptCoordinates graph certified)[index]!.1 ∧
        values[bases[index]!.2]! = (receiptCoordinates graph certified)[index]!.2 := by
  obtain ⟨x0,y0,x1,y1,x2,y2,b0,b1,b2,b3,b4,b5,program⟩ := referenceSchedule_nodes resolver graph reference returned
  have x0Meaning : values[x0]! = certified.first.x :=
    (Symbolic.resolve_sound resolver inputs values denotes _ _ b0).trans
      (certifiedBase_coordinate graph certified 0 (by decide))
  have y0Meaning : values[y0]! = certified.first.y :=
    (Symbolic.resolve_sound resolver inputs values denotes _ _ b1).trans
      (certifiedBase_coordinate graph certified 1 (by decide))
  have x1Meaning : values[x1]! = certified.second.x :=
    (Symbolic.resolve_sound resolver inputs values denotes _ _ b2).trans
      (certifiedBase_coordinate graph certified 2 (by decide))
  have y1Meaning : values[y1]! = certified.second.y :=
    (Symbolic.resolve_sound resolver inputs values denotes _ _ b3).trans
      (certifiedBase_coordinate graph certified 3 (by decide))
  have x2Meaning : values[x2]! = certified.third.x :=
    (Symbolic.resolve_sound resolver inputs values denotes _ _ b4).trans
      (certifiedBase_coordinate graph certified 4 (by decide))
  have y2Meaning : values[y2]! = certified.third.y :=
    (Symbolic.resolve_sound resolver inputs values denotes _ _ b5).trans
      (certifiedBase_coordinate graph certified 5 (by decide))
  refine ⟨#[(x0,y0),(x1,y1),(x2,y2)],rfl,program,?_⟩
  intro index bound
  interval_cases index
  · exact ⟨x0Meaning,y0Meaning⟩
  · exact ⟨x1Meaning,y1Meaning⟩
  · exact ⟨x2Meaning,y2Meaning⟩

theorem referenceSchedule_base_meaning (resolver : Resolver) (graph : SelectedGraph)
    (inputs values : Array Nat) (denotes : Symbolic.Denotes resolver.nodes inputs values)
    (certified : CertifiedPedersenBases graph) (reference : Reference)
    (returned : referenceSchedule resolver graph=.ok reference) :
    ∃ bases : Array PointRef, bases.size=3 ∧
      (referenceProgram resolver bases).run #[]=
        .ok ((reference.commitment,reference.nullifier),reference.steps) ∧
      ∀ index<3, ∃ curve : Edwards (model values[bases[index]!.1]!) (model values[bases[index]!.2]!),
        toMontgomery ⟨model values[bases[index]!.1]!,model values[bases[index]!.2]!,curve⟩=
          groupPoint (firstThreeGenerators certified.first certified.second certified.third index) := by
  obtain ⟨bases,size,program,coordinates⟩ :=
    referenceSchedule_base_coordinates resolver graph inputs values denotes certified reference returned
  refine ⟨bases,size,program,?_⟩
  intro index bound
  obtain ⟨curve,meaning⟩ := receiptCoordinates_edwards graph certified index bound
  obtain ⟨x,y⟩ := coordinates index bound
  have actualCurve : Edwards (model values[bases[index]!.1]!) (model values[bases[index]!.2]!) := by
    rw [x,y]
    exact curve
  refine ⟨actualCurve,?_⟩
  simpa only [x,y] using meaning

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.referenceSchedule_inline
#print axioms TornadoProofs.Witness.PedersenReference.referenceSchedule_nodes
#print axioms TornadoProofs.Witness.PedersenReference.certifiedRaw_edwards
#print axioms TornadoProofs.Witness.PedersenReference.certifiedBase_coordinate
#print axioms TornadoProofs.Witness.PedersenReference.receiptCoordinates_edwards
#print axioms TornadoProofs.Witness.PedersenReference.referenceSchedule_base_coordinates
#print axioms TornadoProofs.Witness.PedersenReference.referenceSchedule_base_meaning
