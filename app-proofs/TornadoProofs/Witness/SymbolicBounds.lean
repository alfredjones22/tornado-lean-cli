import TornadoProofs.Witness.SymbolicValues
import TornadoProofs.Witness.PrimitiveBounds

set_option autoImplicit false
namespace TornadoProofs.Witness.Symbolic
open Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.Groth16R1CS

theorem tableValid_node (nodes : Array Node) (valid : tableValid nodes = true)
    (index : Nat) (bound : index < nodes.size) : nodeValid index nodes[index]! = true :=
  List.all_eq_true.mp valid index (List.mem_range.mpr bound)

theorem tableValid_topological (nodes : Array Node) (valid : tableValid nodes = true) :
    Topological nodes := by
  intro index bound source member
  have checked := tableValid_node nodes valid index bound
  simp only [nodeValid, Bool.and_eq_true] at checked
  have refs := checked.1
  exact of_decide_eq_true (List.all_eq_true.mp refs source member)

theorem tableValid_constant (nodes : Array Node) (valid : tableValid nodes = true)
    (index value : Nat) (bound : index < nodes.size) (node : nodes[index]! = .constant value) :
    value < scalarPrime := by
  have checked := tableValid_node nodes valid index bound
  simpa only [nodeValid, node, Node.references, List.all_nil, Bool.true_and,
    decide_eq_true_eq] using checked

theorem meaningAt_bounded (inputs values : Nat → Nat) (node : Node)
    (inputBound : ∀ index, inputs index < scalarPrime)
    (referenceBound : ∀ index ∈ node.references, values index < scalarPrime)
    (constantBound : ∀ value, node = .constant value → value < scalarPrime) :
    meaningAt inputs values node < scalarPrime := by
  cases node with
  | input index => exact inputBound index
  | constant value => exact constantBound value rfl
  | bit source position =>
    have binary := bitValue_is_binary (values source) position
    have primeLarge : 2 < scalarPrime := by decide
    exact Nat.lt_trans binary primeLarge
  | add left right => exact Nat.mod_lt _ (by decide)
  | sub left right => exact Nat.mod_lt _ (by decide)
  | mul left right => exact Nat.mod_lt _ (by decide)
  | inverse source => exact LeanCrypto.Proofs.BN254Fr.powMod_bounded _ _
  | select selector left right =>
    have leftBound := referenceBound left (by simp [Node.references])
    have rightBound := referenceBound right (by simp [Node.references])
    simp only [meaningAt, dualMuxValues]
    split <;> assumption

theorem dagValue_bounded (nodes : Array Node) (inputs : Array Nat)
    (valid : tableValid nodes = true) (inputBound : ∀ (index : Nat), inputs[index]! < scalarPrime)
    (index : Nat) (bound : index < nodes.size) :
    dagValue nodes (inputs[·]!) index < scalarPrime := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
    rw [dagValue]
    apply meaningAt_bounded _ _ _ inputBound
    · intro source member
      have earlier := tableValid_topological nodes valid index bound source member
      rw [dif_pos earlier]
      exact ih source earlier (by omega)
    · intro value equal
      exact tableValid_constant nodes valid index value bound equal

theorem mathematicalValues_bounded (nodes : Array Node) (inputs : Array Nat)
    (valid : tableValid nodes = true) (inputBound : ∀ (index : Nat), inputs[index]! < scalarPrime) :
    Primitive.Bounded (mathematicalValues nodes inputs) := by
  intro value member
  have member' : value ∈ mathematicalValues nodes inputs := by simpa using member
  rcases Array.mem_iff_getElem.mp member' with ⟨index,bound,equal⟩
  have bound' : index < nodes.size := by simpa only [mathematicalValues_size] using bound
  rw [← equal]
  have valueBound := dagValue_bounded nodes inputs valid inputBound index bound'
  simpa only [← mathematicalValues_get nodes inputs index bound',
    getElem!_pos (mathematicalValues nodes inputs) index bound] using valueBound

end TornadoProofs.Witness.Symbolic
#print axioms TornadoProofs.Witness.Symbolic.tableValid_node
#print axioms TornadoProofs.Witness.Symbolic.tableValid_topological
#print axioms TornadoProofs.Witness.Symbolic.tableValid_constant
#print axioms TornadoProofs.Witness.Symbolic.meaningAt_bounded
#print axioms TornadoProofs.Witness.Symbolic.dagValue_bounded
#print axioms TornadoProofs.Witness.Symbolic.mathematicalValues_bounded
