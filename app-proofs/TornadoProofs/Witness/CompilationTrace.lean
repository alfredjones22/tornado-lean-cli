import TornadoProofs.Witness.SeedPhases
import TornadoProofs.Witness.Num2BitsPhases
import TornadoProofs.Witness.MerklePhases
import TornadoProofs.Witness.CompleteAssignment

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

structure CompilationTrace (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph) where
  seeded : SignalState
  withCommitment : SignalState
  withBits : SignalState
  withBases : SignalState
  withPrimitives : SignalState
  final : SignalState
  commitmentNode : Nat
  layout : graph.layoutValid=true
  table : tableValid resolver.nodes=true
  seedsBuilt : forIn (List.range 49) (SignalState.empty graph.nSignals) (fun index state => do
    let next ← seedPublicAction resolver index state
    pure (ForInStep.yield next))=.ok seeded
  commitmentResolved : resolver.resolve (.input 49)=.ok commitmentNode
  commitmentBuilt : seeded.write graph.commitmentSignal commitmentNode=.ok withCommitment
  bitsBuilt : forIn graph.num2bits withCommitment (fun component state => do
    let next ← compileNum2Bits resolver state component
    pure (ForInStep.yield next))=.ok withBits
  basesBuilt : forIn graph.bases withBits (fun base state => do
    let next ← basePublicAction resolver base state
    pure (ForInStep.yield next))=.ok withBases
  primitivesBuilt : forIn graph.primitives withBases (fun primitive state => do
    let next ← compilePrimitiveStage resolver state primitive
    pure (ForInStep.yield next))=.ok withPrimitives
  merkleBuilt : forIn (List.range 20) withPrimitives (fun index state => do
    let next ← compileMerkleLevel resolver Tornado.Crypto.mimcConstants state graph.merkle[index]! graph.feistel[index]!
    pure (ForInStep.yield next))=.ok final
  publicRootRead : final.read graph.rootSignal=.ok compiled.publicRoot.1
  computedRootRead : final.read graph.merkle[19]!.hashOutput=.ok compiled.publicRoot.2
  publicNullifierRead : final.read 2=.ok compiled.publicNullifier.1
  computedNullifierRead : final.read 28300=.ok compiled.publicNullifier.2
  complete : final.slots=compiled.signalRoots.map some
  aliases : final.commitmentAliases=compiled.commitmentAliases

theorem compileGraph_trace (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (publicCompiled : compileGraph resolver graph=.ok compiled) :
    Nonempty (CompilationTrace resolver graph compiled) := by
  unfold compileGraph at publicCompiled
  have layout : graph.layoutValid=true := by
    by_contra invalid
    have rejected := Bool.eq_false_of_not_eq_true invalid
    simp [compileGraphWith,rejected,bind,Except.bind] at publicCompiled
  have table : tableValid resolver.nodes=true := by
    by_contra invalid
    have rejected := Bool.eq_false_of_not_eq_true invalid
    simp [compileGraphWith,rejected,bind,Except.bind] at publicCompiled
  unfold compileGraphWith at publicCompiled
  simp only [layout,table,Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte,
    forIn_range_zero,pure_bind] at publicCompiled
  obtain ⟨seeded,seedsBuilt,publicCompiled⟩ := bind_success _ _ compiled publicCompiled
  obtain ⟨commitmentNode,commitmentResolved,publicCompiled⟩ := bind_success _ _ compiled publicCompiled
  obtain ⟨withCommitment,commitmentBuilt,publicCompiled⟩ := bind_success _ _ compiled publicCompiled
  obtain ⟨withBits,bitsBuilt,publicCompiled⟩ := bind_success _ _ compiled publicCompiled
  obtain ⟨withBases,basesBuilt,publicCompiled⟩ := bind_success _ _ compiled publicCompiled
  obtain ⟨withPrimitives,primitivesBuilt,publicCompiled⟩ := bind_success _ _ compiled publicCompiled
  obtain ⟨final,merkleBuilt,publicCompiled⟩ := bind_success _ _ compiled publicCompiled
  obtain ⟨publicRoot,publicRootRead,publicCompiled⟩ := bind_success _ _ compiled publicCompiled
  obtain ⟨computedRoot,computedRootRead,publicCompiled⟩ := bind_success _ _ compiled publicCompiled
  obtain ⟨publicNullifier,publicNullifierRead,publicCompiled⟩ := bind_success _ _ compiled publicCompiled
  obtain ⟨computedNullifier,computedNullifierRead,publicCompiled⟩ := bind_success _ _ compiled publicCompiled
  obtain ⟨roots,rootsBuilt,publicCompiled⟩ := bind_success _ _ compiled publicCompiled
  have equal : CompiledGraph.mk roots final.commitmentAliases (publicRoot,computedRoot)
      (publicNullifier,computedNullifier)=compiled := Except.ok.inj publicCompiled
  subst compiled
  have complete : final.slots=roots.map some := slots_complete final roots rootsBuilt
  have basesBuilt' : (forIn graph.bases withBits (fun base current => do
      let next ← basePublicAction resolver base current
      pure (ForInStep.yield next)))=.ok withBases := by
    simpa only [basePublicAction,bind_assoc] using basesBuilt
  have seedStep : (fun index state => do
      let next ← seedPublicAction resolver index state
      pure (ForInStep.yield next)) = (fun index (state : SignalState) =>
        if index==0 then do
          let node ← resolver.resolve (.constant 1)
          let next ← state.write index node
          pure (ForInStep.yield next)
        else do
          let node ← resolver.resolve (.input index)
          let next ← state.write index node
          pure (ForInStep.yield next)) := by
    funext index state
    unfold seedPublicAction
    split <;> simp only [bind_assoc]
  have seedsBuilt' : (forIn (List.range 49) (SignalState.empty graph.nSignals)
      (fun index state => do
        let next ← seedPublicAction resolver index state
        pure (ForInStep.yield next)))=.ok seeded := by
    rw [seedStep]
    exact seedsBuilt
  exact ⟨⟨seeded,withCommitment,withBits,withBases,withPrimitives,final,commitmentNode,
    layout,table,seedsBuilt',commitmentResolved,commitmentBuilt,bitsBuilt,basesBuilt',
    primitivesBuilt,merkleBuilt,publicRootRead,computedRootRead,publicNullifierRead,
    computedNullifierRead,complete,rfl⟩⟩

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.compileGraph_trace
