import TornadoProofs.Witness.Symbolic

set_option autoImplicit false
namespace TornadoProofs.Witness.Symbolic
open Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.Groth16R1CS

def meaningAt (inputs values : Nat → Nat) : Node → Nat
  | .input index => inputs index
  | .constant value => value
  | .bit source position => bitValue (values source) position
  | .add left right => (values left + values right) % scalarPrime
  | .sub left right => (values left + scalarPrime - values right % scalarPrime) % scalarPrime
  | .mul left right => values left * values right % scalarPrime
  | .inverse source => LeanCrypto.Groth16.FFT.powMod (values source) (scalarPrime-2)
  | .select selector left right =>
    (dualMuxValues (values selector) (values left) (values right)).1

theorem meaningAt_array (inputs values : Array Nat) (node : Node) :
    meaningAt (inputs[·]!) (values[·]!) node = node.meaning inputs values := by
  cases node <;> rfl

theorem meaningAt_congr (inputs : Nat → Nat) (left right : Nat → Nat) (node : Node)
    (same : ∀ index ∈ node.references, left index = right index) :
    meaningAt inputs left node = meaningAt inputs right node := by
  cases node with
  | input index => rfl
  | constant value => rfl
  | bit source position =>
    simp only [meaningAt, same source (by simp [Node.references])]
  | inverse source =>
    simp only [meaningAt, same source (by simp [Node.references])]
  | add a b | sub a b | mul a b =>
    all_goals simp only [meaningAt, same a (by simp [Node.references]),
      same b (by simp [Node.references])]
  | select selector a b =>
    simp only [meaningAt, same selector (by simp [Node.references]),
      same a (by simp [Node.references]), same b (by simp [Node.references])]

/-- Total well-founded interpretation. All recursive references strictly
 decrease; malformed forward edges receive zero and are rejected separately. -/
def dagValue (nodes : Array Node) (inputs : Nat → Nat) (index : Nat) : Nat :=
  meaningAt inputs (fun source => if _h : source < index then
    dagValue nodes inputs source else 0) nodes[index]!
termination_by index

def Topological (nodes : Array Node) : Prop :=
  ∀ index < nodes.size, ∀ source ∈ nodes[index]!.references, source < index

def mathematicalValues (nodes : Array Node) (inputs : Array Nat) : Array Nat :=
  Array.ofFn fun index : Fin nodes.size => dagValue nodes (inputs[·]!) index.val

theorem mathematicalValues_size (nodes : Array Node) (inputs : Array Nat) :
    (mathematicalValues nodes inputs).size = nodes.size := by
  simp [mathematicalValues]

theorem mathematicalValues_get (nodes : Array Node) (inputs : Array Nat)
    (index : Nat) (bound : index < nodes.size) :
    (mathematicalValues nodes inputs)[index]! = dagValue nodes (inputs[·]!) index := by
  simp [mathematicalValues, getElem!_pos, bound]

theorem mathematicalValues_denotes (nodes : Array Node) (inputs : Array Nat)
    (topological : Topological nodes) :
    Denotes nodes inputs (mathematicalValues nodes inputs) := by
  intro index node lookup
  have bound := of_getElem?_eq_some lookup
  have actual : nodes[index]! = node := by
    rw [getElem!_pos nodes index bound]
    exact Option.some.inj ((Array.getElem?_eq_getElem bound).symm.trans lookup)
  rw [mathematicalValues_get nodes inputs index bound]
  rw [dagValue]
  rw [← meaningAt_array, actual]
  apply meaningAt_congr
  intro source member
  have earlier : source < index := topological index bound source (by simpa [actual] using member)
  rw [dif_pos earlier, mathematicalValues_get nodes inputs source (by omega)]

end TornadoProofs.Witness.Symbolic
#print axioms TornadoProofs.Witness.Symbolic.meaningAt_array
#print axioms TornadoProofs.Witness.Symbolic.meaningAt_congr
#print axioms TornadoProofs.Witness.Symbolic.mathematicalValues_size
#print axioms TornadoProofs.Witness.Symbolic.mathematicalValues_get
#print axioms TornadoProofs.Witness.Symbolic.mathematicalValues_denotes
