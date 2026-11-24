import TornadoProofs.Witness.ReferenceControl

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule
open Tornado.Protocol.WitnessSymbolic

theorem compiler_segment_eq (resolver : Resolver) (commitment : Bool) (offset windows : Nat) (base : PointRef) :
    segment resolver commitment offset windows base = segmentWith (compilerOps resolver commitment) offset windows base := by
  unfold segment segmentWith compilerOps
  simp only [compiler_window_eq, compilerWindows, ← bind_pure_comp, pure_bind, bind_assoc]
  congr 3
  all_goals funext argument
  all_goals congr 3
  all_goals funext argument
  all_goals congr 3
  · funext index frame
    cases frame.1 <;> rfl
  · funext frame
    cases frame.1 <;> rfl
  · funext frame
    cases frame.1 <;> rfl
  · cases argument.1 <;> rfl

theorem compiler_program_eq (resolver : Resolver) (bases : Array PointRef) :
    referenceProgram resolver bases = programWith (compilerOps resolver true) (compilerOps resolver false) bases := by
  unfold referenceProgram programWith
  simp only [compiler_segment_eq, compilerOps]

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.compiler_segment_eq
#print axioms TornadoProofs.Witness.PedersenReference.compiler_program_eq
