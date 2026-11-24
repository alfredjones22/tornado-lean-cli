import TornadoProofs.Witness.CompleteAssignment
import TornadoProofs.Witness.GlobalRows

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

def witnessValues (roots values : Array Nat) (count : Nat) : Array Nat :=
  ((List.range count).map (fun index => values[roots[index]!]!)).toArray

theorem witnessValues_size (roots values : Array Nat) (count : Nat) :
    (witnessValues roots values count).size=count := by simp [witnessValues]

theorem witnessValues_get (roots values : Array Nat) (count index : Nat) (bound : index<count) :
    (witnessValues roots values count)[index]! = values[roots[index]!]! := by
  simp [witnessValues,getElem!_pos,bound]

theorem witnessValues_canonical (roots values : Array Nat) (count : Nat)
    (canonical : Primitive.Bounded values) :
    ∀ value∈witnessValues roots values count,value<Tornado.Protocol.Groth16R1CS.scalarPrime := by
  intro value member
  have mapped : value∈(List.range count).map (fun index => values[roots[index]!]!) := by
    simpa only [witnessValues,List.mem_toArray] using member
  obtain ⟨index,_,equal⟩ := List.mem_map.mp mapped
  rw [←equal]
  exact canonical_lookup values canonical _

theorem witnessValues_constant (roots values : Array Nat) (count : Nat) (positive : 0<count)
    (constant : values[roots[0]!]! = 1) : (witnessValues roots values count)[0]?=some 1 := by
  have bound : 0<(witnessValues roots values count).size := by simpa only [witnessValues_size] using positive
  have value : (witnessValues roots values count)[0]! = 1 :=
    (witnessValues_get roots values count 0 positive).trans constant
  simpa only [Array.getElem?_eq_getElem bound,
    getElem!_pos (witnessValues roots values count) 0 bound] using congrArg some value

theorem graph_layout_dimensions (graph : SelectedGraph) (layout : graph.layoutValid=true) :
    graph.nSignals=36528 ∧ graph.nVars=28300 := by
  have signals : graph.nSignals=36528 := by
    by_contra different
    simp [SelectedGraph.layoutValid,different] at layout
  have vars : graph.nVars=28300 := by
    by_contra different
    simp [SelectedGraph.layoutValid,different] at layout
  exact ⟨signals,vars⟩

theorem localSystem_shape (nodes : Array Node) (compiled : CompiledGraph) (graph : SelectedGraph)
    (system : LocalSystem) (generated : generateLocalSystem nodes compiled graph=.ok system) :
    compiled.signalRoots.size=graph.nSignals := by
  by_contra different
  simp [generateLocalSystem,generateLocalSystemWith,different,bind,Except.bind] at generated

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.witnessValues_size
#print axioms TornadoProofs.Witness.Execution.witnessValues_get
#print axioms TornadoProofs.Witness.Execution.witnessValues_canonical
#print axioms TornadoProofs.Witness.Execution.witnessValues_constant
#print axioms TornadoProofs.Witness.Execution.graph_layout_dimensions
#print axioms TornadoProofs.Witness.Execution.localSystem_shape
