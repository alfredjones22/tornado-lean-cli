import TornadoProofs.Witness.MerkleMeaning

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

def nativePathStep (constants inputs : Array Nat) (index current : Nat) : Except String Nat :=
  let selected := dualMuxValues inputs[29+index]! current inputs[9+index]!
  LeanCrypto.mimcHashPairWith constants selected.1 selected.2

def nativePathPrefix (constants inputs : Array Nat) (commitment count : Nat) : Except String Nat :=
  (List.range count).foldlM (fun current index => nativePathStep constants inputs index current) commitment

theorem nativePathPrefix_succ (constants inputs : Array Nat) (commitment count : Nat) :
    nativePathPrefix constants inputs commitment (count+1) =
      (nativePathPrefix constants inputs commitment count >>= nativePathStep constants inputs count) := by
  simp only [nativePathPrefix,List.range_succ,List.foldlM_append,List.foldlM_cons,List.foldlM_nil,bind_pure]

theorem source_path_prefix (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (trace : CompilationTrace resolver graph compiled) (inputs : Array Nat) (commitment : Nat)
    (size : inputs.size=49) (constant : inputs[0]! = 1)
    (hashes : ∀ index<20,SlotHash Tornado.Crypto.mimcConstants compiled (sourceValues resolver inputs commitment) graph.merkle[index]!)
    (count : Nat) (bound : count≤20) :
    nativePathPrefix Tornado.Crypto.mimcConstants inputs commitment count =
      .ok (if count=0 then commitment else
        (sourceValues resolver inputs commitment)[compiled.signalRoots[graph.merkle[count-1]!.hashOutput]!]!) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have small : count<20 := by omega
    have previous := ih (by omega)
    rw [nativePathPrefix_succ,previous]
    simp only [bind,Except.bind,Nat.succ_ne_zero,↓reduceIte,Nat.succ_sub_one]
    have routing := graph_merkle_routing graph trace.layout count small
    have leftValue : (sourceValues resolver inputs commitment)[compiled.signalRoots[graph.merkle[count]!.leftInput]!]! =
        (if count=0 then commitment else (sourceValues resolver inputs commitment)[compiled.signalRoots[graph.merkle[count-1]!.hashOutput]!]!) := by
      rw [routing.1]
      by_cases zero : count=0
      · simp only [zero,↓reduceIte,(graph_layout_publicSignals graph trace.layout).1,
          source_commitment_meaning resolver graph compiled trace inputs commitment size]
      · simp only [zero,↓reduceIte]
    have rightValue := source_prefix_meaning resolver graph compiled trace inputs commitment size constant
      (9+count) (by omega)
    have selectorValue := source_prefix_meaning resolver graph compiled trace inputs commitment size constant
      (29+count) (by omega)
    have result := hashes count small
    unfold SlotHash at result
    dsimp only at result
    rw [routing.2.1,routing.2.2,leftValue,rightValue,selectorValue] at result
    exact result

theorem source_path_root (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (trace : CompilationTrace resolver graph compiled) (inputs : Array Nat) (commitment : Nat)
    (size : inputs.size=49) (constant : inputs[0]! = 1)
    (canonical : Primitive.Bounded inputs) (commitmentBound : commitment<Field.q)
    (binary : ∀ index<20,inputs[29+index]! ≤ 1)
    (aliases : ∀ pair∈compiled.commitmentAliases.toList,
      (sourceValues resolver inputs commitment)[pair.1]! = (sourceValues resolver inputs commitment)[pair.2]!)
    (nativeRoot : nativePathPrefix Tornado.Crypto.mimcConstants inputs commitment 20=.ok inputs[1]!) :
    (sourceValues resolver inputs commitment)[compiled.publicRoot.1]! =
      (sourceValues resolver inputs commitment)[compiled.publicRoot.2]! := by
  have hashes := merkle_phase_slotHashes resolver graph compiled trace (inputs.push commitment)
    (sourceValues resolver inputs commitment) (sourceValues_denotes resolver inputs commitment trace.table)
    (sourceValues_bounded resolver inputs commitment trace.table canonical commitmentBound)
    (source_selectors_admitted resolver graph compiled trace inputs commitment size constant binary)
    (by simpa only [AliasesValid,trace.aliases] using aliases)
  have folded := source_path_prefix resolver graph compiled trace inputs commitment size constant hashes 20 (by decide)
  have equal : inputs[1]! = (sourceValues resolver inputs commitment)[compiled.signalRoots[graph.merkle[19]!.hashOutput]!]! := by
    exact Except.ok.inj (nativeRoot.symm.trans folded)
  rw [complete_read_root trace.final compiled trace.complete graph.rootSignal compiled.publicRoot.1 trace.publicRootRead,
    (graph_layout_publicSignals graph trace.layout).2,
    source_prefix_meaning resolver graph compiled trace inputs commitment size constant 1 (by decide),
    complete_read_root trace.final compiled trace.complete graph.merkle[19]!.hashOutput compiled.publicRoot.2 trace.computedRootRead]
  exact equal

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.nativePathPrefix_succ
#print axioms TornadoProofs.Witness.Execution.source_path_prefix
#print axioms TornadoProofs.Witness.Execution.source_path_root
