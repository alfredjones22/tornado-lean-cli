import TornadoProofs.Witness.FeistelObserver
import TornadoProofs.Witness.DualMuxSimulation

set_option autoImplicit false

namespace TornadoProofs.Witness.Execution

open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.Groth16R1CS

/-- The complete two-permutation sponge stage constructs VM success from
public DAG wiring and independent arithmetic values. The native MiMC hash
comparison is derived, rather than taken as a successful-check premise. -/
theorem compileMerkleLevel_construct (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (constants : Array Nat) (state output : SignalState) (level : MerkleLevel) (sponge : SpongeLevel)
    (compiled : compileMerkleLevel resolver constants state level sponge = .ok output)
    (selectorBit : SelectorBit state level values) (terminal : AliasesValid output values) :
    AliasesValid state values ∧
      executeMerkleLevel constants (realize state values) level sponge = .ok (realize output values) := by
  unfold compileMerkleLevel at compiled
  obtain ⟨dual, dualBuilt, compiled⟩ := bind_success (compileDualMux resolver state level) _ output compiled
  obtain ⟨dual, left, right⟩ := dual
  obtain ⟨zeroNode, zeroBuilt, compiled⟩ := bind_success (resolver.resolve (.constant 0)) _ output compiled
  obtain ⟨firstKey, firstKeyBuilt, compiled⟩ := bind_success (dual.write sponge.first.key zeroNode) _ output compiled
  obtain ⟨firstLeft, firstLeftBuilt, compiled⟩ := bind_success (firstKey.write sponge.first.leftInput left) _ output compiled
  obtain ⟨firstInputs, firstInputsBuilt, compiled⟩ := bind_success (firstLeft.write sponge.first.rightInput zeroNode) _ output compiled
  obtain ⟨first, firstBuilt, compiled⟩ := bind_success (compileFeistel resolver constants firstInputs sponge.first) _ output compiled
  obtain ⟨intermediateLeft, intermediateLeftRead, compiled⟩ := bind_success (first.read sponge.first.leftOutput) _ output compiled
  obtain ⟨intermediateRight, intermediateRightRead, compiled⟩ := bind_success (first.read sponge.first.rightOutput) _ output compiled
  obtain ⟨secondKey, secondKeyBuilt, compiled⟩ := bind_success (first.write sponge.second.key zeroNode) _ output compiled
  obtain ⟨absorbed, absorbedBuilt, compiled⟩ := bind_success (resolver.resolve (.add intermediateLeft right)) _ output compiled
  obtain ⟨secondLeft, secondLeftBuilt, compiled⟩ := bind_success (secondKey.write sponge.second.leftInput absorbed) _ output compiled
  obtain ⟨secondInputs, secondInputsBuilt, compiled⟩ := bind_success (secondLeft.write sponge.second.rightInput intermediateRight) _ output compiled
  obtain ⟨second, secondBuilt, compiled⟩ := bind_success (compileFeistel resolver constants secondInputs sponge.second) _ output compiled
  obtain ⟨hash, hashRead, compiled⟩ := bind_success (second.read sponge.second.leftOutput) _ output compiled
  have finalBuilt : second.write level.hashOutput hash = .ok output := compiled
  obtain ⟨secondAliases, runtimeFinal⟩ := signalWrite_construct second output values canonical level.hashOutput hash finalBuilt terminal
  obtain ⟨secondInputsAliases, runtimeSecond⟩ := compileFeistel_construct resolver inputs values denotes canonical constants
    secondInputs second sponge.second secondBuilt secondAliases
  obtain ⟨secondLeftAliases, runtimeSecondInputs⟩ := signalWrite_construct secondLeft secondInputs values canonical
    sponge.second.rightInput intermediateRight secondInputsBuilt secondInputsAliases
  obtain ⟨secondKeyAliases, runtimeSecondLeft⟩ := signalWrite_construct secondKey secondLeft values canonical
    sponge.second.leftInput absorbed secondLeftBuilt secondLeftAliases
  obtain ⟨firstAliases, runtimeSecondKey⟩ := signalWrite_construct first secondKey values canonical
    sponge.second.key zeroNode secondKeyBuilt secondKeyAliases
  obtain ⟨firstInputsAliases, runtimeFirst⟩ := compileFeistel_construct resolver inputs values denotes canonical constants
    firstInputs first sponge.first firstBuilt firstAliases
  obtain ⟨firstLeftAliases, runtimeFirstInputs⟩ := signalWrite_construct firstLeft firstInputs values canonical
    sponge.first.rightInput zeroNode firstInputsBuilt firstInputsAliases
  obtain ⟨firstKeyAliases, runtimeFirstLeft⟩ := signalWrite_construct firstKey firstLeft values canonical
    sponge.first.leftInput left firstLeftBuilt firstLeftAliases
  obtain ⟨dualAliases, runtimeFirstKey⟩ := signalWrite_construct dual firstKey values canonical
    sponge.first.key zeroNode firstKeyBuilt firstKeyAliases
  obtain ⟨initialAliases, runtimeDual⟩ := compileDualMux_construct resolver inputs values denotes canonical
    state level (dual, left, right) dualBuilt selectorBit dualAliases
  have zeroValue : values[zeroNode]! = 0 :=
    Symbolic.resolve_sound resolver inputs values denotes (.constant 0) zeroNode zeroBuilt
  have absorbedValue : values[absorbed]! = (values[intermediateLeft]! + values[right]!) % scalarPrime :=
    Symbolic.resolve_sound resolver inputs values denotes (.add intermediateLeft right) absorbed absorbedBuilt
  rw [zeroValue] at runtimeFirstKey runtimeFirstInputs runtimeSecondKey
  have firstKeyAssigned := write_success_preserves _ _ _ _ runtimeFirstKey
  have firstLeftAssigned := write_success_preserves _ _ _ _ runtimeFirstLeft
  have firstRightAssigned := write_success_preserves _ _ _ _ runtimeFirstInputs
  have firstKeyRead : (realize firstInputs values).read sponge.first.key = .ok 0 :=
    assigned_read _ _ _ (firstRightAssigned.2.2 _ _ (firstLeftAssigned.2.2 _ _ firstKeyAssigned.1))
  have firstLeftRead : (realize firstInputs values).read sponge.first.leftInput = .ok values[left]! :=
    assigned_read _ _ _ (firstRightAssigned.2.2 _ _ firstLeftAssigned.1)
  have firstRightRead : (realize firstInputs values).read sponge.first.rightInput = .ok 0 :=
    assigned_read _ _ _ firstRightAssigned.1
  obtain ⟨firstPair, firstPermutation, firstPairLeftRead, firstPairRightRead⟩ :=
    executeFeistel_observer constants (realize firstInputs values) (realize first values) sponge.first
      0 values[left]! 0 firstKeyRead firstLeftRead firstRightRead (by decide)
      (canonical_lookup values canonical left) (by decide) runtimeFirst
  have intermediateLeftValue : values[intermediateLeft]! = firstPair.1 :=
    Except.ok.inj ((signalRead_realize first values sponge.first.leftOutput intermediateLeft intermediateLeftRead).symm.trans firstPairLeftRead)
  have intermediateRightValue : values[intermediateRight]! = firstPair.2 :=
    Except.ok.inj ((signalRead_realize first values sponge.first.rightOutput intermediateRight intermediateRightRead).symm.trans firstPairRightRead)
  have secondKeyAssigned := write_success_preserves _ _ _ _ runtimeSecondKey
  have secondLeftAssigned := write_success_preserves _ _ _ _ runtimeSecondLeft
  have secondRightAssigned := write_success_preserves _ _ _ _ runtimeSecondInputs
  have secondKeyRead : (realize secondInputs values).read sponge.second.key = .ok 0 :=
    assigned_read _ _ _ (secondRightAssigned.2.2 _ _ (secondLeftAssigned.2.2 _ _ secondKeyAssigned.1))
  have secondLeftRead : (realize secondInputs values).read sponge.second.leftInput = .ok values[absorbed]! :=
    assigned_read _ _ _ (secondRightAssigned.2.2 _ _ secondLeftAssigned.1)
  have secondRightRead : (realize secondInputs values).read sponge.second.rightInput = .ok values[intermediateRight]! :=
    assigned_read _ _ _ secondRightAssigned.1
  obtain ⟨secondPair, secondPermutation, secondPairLeftRead, _⟩ :=
    executeFeistel_observer constants (realize secondInputs values) (realize second values) sponge.second
      0 values[absorbed]! values[intermediateRight]! secondKeyRead secondLeftRead secondRightRead (by decide)
      (canonical_lookup values canonical absorbed) (canonical_lookup values canonical intermediateRight) runtimeSecond
  have hashValue : values[hash]! = secondPair.1 :=
    Except.ok.inj ((signalRead_realize second values sponge.second.leftOutput hash hashRead).symm.trans secondPairLeftRead)
  have size := compileFeistel_constants_size resolver constants firstInputs first sponge.first firstBuilt
  have permutationSecond : LeanCrypto.mimcPermutationWith constants
      ((firstPair.1 + values[right]!) % scalarPrime) firstPair.2 0 = .ok secondPair := by
    simpa only [absorbedValue, intermediateLeftValue, intermediateRightValue] using secondPermutation
  have independentHash : LeanCrypto.mimcHashPairWith constants values[left]! values[right]! = .ok values[hash]! := by
    rw [hashValue]
    exact native_hashPair_construct constants size values[left]! values[right]!
      (canonical_lookup values canonical left) firstPair secondPair firstPermutation permutationSecond
  refine ⟨initialAliases, ?_⟩
  simp only [executeMerkleLevel, runtimeDual, bind, Except.bind]
  rw [runtimeFirstKey]
  simp only
  rw [runtimeFirstLeft]
  simp only
  rw [runtimeFirstInputs]
  simp only
  rw [runtimeFirst]
  simp only
  rw [signalRead_realize first values sponge.first.leftOutput intermediateLeft intermediateLeftRead]
  simp only
  rw [signalRead_realize first values sponge.first.rightOutput intermediateRight intermediateRightRead]
  simp only
  rw [runtimeSecondKey]
  simp only
  rw [← absorbedValue, runtimeSecondLeft]
  simp only
  rw [runtimeSecondInputs]
  simp only
  rw [runtimeSecond]
  simp only
  rw [signalRead_realize second values sponge.second.leftOutput hash hashRead]
  simp only
  rw [independentHash]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  exact runtimeFinal

end TornadoProofs.Witness.Execution

#print axioms TornadoProofs.Witness.Execution.compileMerkleLevel_construct
