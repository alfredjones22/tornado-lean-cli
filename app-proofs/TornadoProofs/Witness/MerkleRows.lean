import TornadoProofs.Witness.MerkleRowSupport

set_option autoImplicit false

namespace TornadoProofs.Witness.Local

open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open TornadoProofs.Witness.Execution
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr

/-- The exact public Merkle local-row generator preserves source equation
satisfaction, using the same source selector and public Feistel compilations. -/
theorem merkleLocalSystem_sound (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (compiledGraph : CompiledGraph) (constants : Array Nat) (state after : SignalState)
    (level : MerkleLevel) (sponge : SpongeLevel) (assignment : Nat → Fr) (constant : assignment 0 = 1)
    (rowValue : ∀ index, linearValue assignment (signalLinear resolver.nodes compiledGraph index) = assignment index)
    (compiled : compileMerkleLevel resolver constants state level sponge = .ok after)
    (selectorBit : SelectorBit state level values) (aliases : AliasesValid after values)
    (interpreted : SignalInterpretation after assignment values)
    (seed : LocalSystem) (valid : SystemSatisfied assignment seed) :
    SystemSatisfied assignment (merkleLocalSystem resolver.nodes compiledGraph constants seed level sponge) := by
  unfold compileMerkleLevel at compiled
  obtain ⟨dual, dualBuilt, compiled⟩ := bind_success _ _ after compiled
  obtain ⟨dual, left, right⟩ := dual
  obtain ⟨zeroNode, zeroBuilt, compiled⟩ := bind_success _ _ after compiled
  obtain ⟨firstKey, firstKeyBuilt, compiled⟩ := bind_success _ _ after compiled
  obtain ⟨firstLeft, firstLeftBuilt, compiled⟩ := bind_success _ _ after compiled
  obtain ⟨firstInputs, firstInputsBuilt, compiled⟩ := bind_success _ _ after compiled
  obtain ⟨first, firstBuilt, compiled⟩ := bind_success _ _ after compiled
  obtain ⟨intermediateLeft, intermediateLeftRead, compiled⟩ := bind_success _ _ after compiled
  obtain ⟨intermediateRight, intermediateRightRead, compiled⟩ := bind_success _ _ after compiled
  obtain ⟨secondKey, secondKeyBuilt, compiled⟩ := bind_success _ _ after compiled
  obtain ⟨absorbed, absorbedBuilt, compiled⟩ := bind_success _ _ after compiled
  obtain ⟨secondLeft, secondLeftBuilt, compiled⟩ := bind_success _ _ after compiled
  obtain ⟨secondInputs, secondInputsBuilt, compiled⟩ := bind_success _ _ after compiled
  obtain ⟨second, secondBuilt, compiled⟩ := bind_success _ _ after compiled
  obtain ⟨hash, hashRead, finalBuilt⟩ := bind_success _ _ after compiled
  have finalWrite : second.write level.hashOutput hash = .ok after := finalBuilt
  have secondAfter := signalWrite_extends second after level.hashOutput hash finalWrite
  have secondInputsAfter := signalExtends_trans (compileFeistel_signalExtends resolver constants secondInputs second sponge.second secondBuilt) secondAfter
  have secondLeftAfter := signalExtends_trans (signalWrite_extends secondLeft secondInputs sponge.second.rightInput intermediateRight secondInputsBuilt) secondInputsAfter
  have secondKeyAfter := signalExtends_trans (signalWrite_extends secondKey secondLeft sponge.second.leftInput absorbed secondLeftBuilt) secondLeftAfter
  have firstAfter := signalExtends_trans (signalWrite_extends first secondKey sponge.second.key zeroNode secondKeyBuilt) secondKeyAfter
  have firstInputsAfter := signalExtends_trans (compileFeistel_signalExtends resolver constants firstInputs first sponge.first firstBuilt) firstAfter
  have firstLeftAfter := signalExtends_trans (signalWrite_extends firstLeft firstInputs sponge.first.rightInput zeroNode firstInputsBuilt) firstInputsAfter
  have firstKeyAfter := signalExtends_trans (signalWrite_extends firstKey firstLeft sponge.first.leftInput left firstLeftBuilt) firstLeftAfter
  have dualAfter := signalExtends_trans (signalWrite_extends dual firstKey sponge.first.key zeroNode firstKeyBuilt) firstKeyAfter
  have interp {before : SignalState} (extension : SignalExtends before after) : SignalInterpretation before assignment values :=
    signalInterpretation_backwards before after assignment values extension interpreted
  have secondAliases := signalWrite_aliases_backwards second after values level.hashOutput hash finalWrite aliases
  have secondInputsAliases := (compileFeistel_construct resolver inputs values denotes canonical constants secondInputs second sponge.second secondBuilt secondAliases).1
  have secondLeftAliases := signalWrite_aliases_backwards secondLeft secondInputs values sponge.second.rightInput intermediateRight secondInputsBuilt secondInputsAliases
  have secondKeyAliases := signalWrite_aliases_backwards secondKey secondLeft values sponge.second.leftInput absorbed secondLeftBuilt secondLeftAliases
  have firstAliases := signalWrite_aliases_backwards first secondKey values sponge.second.key zeroNode secondKeyBuilt secondKeyAliases
  have firstInputsAliases := (compileFeistel_construct resolver inputs values denotes canonical constants firstInputs first sponge.first firstBuilt firstAliases).1
  have firstLeftAliases := signalWrite_aliases_backwards firstLeft firstInputs values sponge.first.rightInput zeroNode firstInputsBuilt firstInputsAliases
  have firstKeyAliases := signalWrite_aliases_backwards firstKey firstLeft values sponge.first.leftInput left firstLeftBuilt firstLeftAliases
  have dualAliases := signalWrite_aliases_backwards dual firstKey values sponge.first.key zeroNode firstKeyBuilt firstKeyAliases
  obtain ⟨inputLeft, inputRight, selector, dualMid, inputLeftRead, inputRightRead, selectorRead,
      leftResolved, rightResolved, dualLeftWritten, dualRightWritten⟩ := compileDualMux_details resolver state level (dual, left, right) dualBuilt
  have dualMidAfter := signalExtends_trans (signalWrite_extends dualMid dual level.rightOutput right dualRightWritten) dualAfter
  have stateAfter := signalExtends_trans (signalWrite_extends state dualMid level.leftOutput left dualLeftWritten) dualMidAfter
  have dualMidAliases := signalWrite_aliases_backwards dualMid dual values level.rightOutput right dualRightWritten dualAliases
  have inputLeftS := interpreted_read state assignment values (interp stateAfter) level.leftInput inputLeft inputLeftRead
  have inputRightS := interpreted_read state assignment values (interp stateAfter) level.rightInput inputRight inputRightRead
  have selectorS := interpreted_read state assignment values (interp stateAfter) level.selector selector selectorRead
  have leftS := interpreted_write state dualMid assignment values canonical level.leftOutput left dualLeftWritten dualMidAliases (interp dualMidAfter)
  have rightS := interpreted_write dualMid dual assignment values canonical level.rightOutput right dualRightWritten dualAliases (interp dualAfter)
  have leftValue : values[left]! = (dualMuxValues values[selector]! values[inputLeft]! values[inputRight]!).1 :=
    Symbolic.resolve_sound resolver inputs values denotes (.select selector inputLeft inputRight) left leftResolved
  have rightValue : values[right]! = (dualMuxValues values[selector]! values[inputLeft]! values[inputRight]!).2 := by
    have resolved := Symbolic.resolve_sound resolver inputs values denotes (.select selector inputRight inputLeft) right rightResolved
    have swap : (dualMuxValues values[selector]! values[inputRight]! values[inputLeft]!).1 =
        (dualMuxValues values[selector]! values[inputLeft]! values[inputRight]!).2 := by
      unfold dualMuxValues
      split <;> rfl
    exact resolved.trans swap
  have binary := selectorBit selector selectorRead
  have gates := dualMux_field_equations values[selector]! values[inputLeft]! values[inputRight]! binary
  rw [← leftValue, ← rightValue] at gates
  have zeroValue : values[zeroNode]! = 0 := Symbolic.resolve_sound resolver inputs values denotes (.constant 0) zeroNode zeroBuilt
  have firstKeyS := interpreted_write dual firstKey assignment values canonical sponge.first.key zeroNode firstKeyBuilt firstKeyAliases (interp firstKeyAfter)
  have firstLeftS := interpreted_write firstKey firstLeft assignment values canonical sponge.first.leftInput left firstLeftBuilt firstLeftAliases (interp firstLeftAfter)
  have firstRightS := interpreted_write firstLeft firstInputs assignment values canonical sponge.first.rightInput zeroNode firstInputsBuilt firstInputsAliases (interp firstInputsAfter)
  have intermediateLeftS := interpreted_read first assignment values (interp firstAfter) sponge.first.leftOutput intermediateLeft intermediateLeftRead
  have intermediateRightS := interpreted_read first assignment values (interp firstAfter) sponge.first.rightOutput intermediateRight intermediateRightRead
  have secondKeyS := interpreted_write first secondKey assignment values canonical sponge.second.key zeroNode secondKeyBuilt secondKeyAliases (interp secondKeyAfter)
  have secondLeftS := interpreted_write secondKey secondLeft assignment values canonical sponge.second.leftInput absorbed secondLeftBuilt secondLeftAliases (interp secondLeftAfter)
  have secondRightS := interpreted_write secondLeft secondInputs assignment values canonical sponge.second.rightInput intermediateRight secondInputsBuilt secondInputsAliases (interp secondInputsAfter)
  have hashS := interpreted_write second after assignment values canonical level.hashOutput hash finalWrite aliases interpreted
  have hashInputS := interpreted_read second assignment values (interp secondAfter) sponge.second.leftOutput hash hashRead
  have absorbedValue : values[absorbed]! = (values[intermediateLeft]! + values[right]!) % Tornado.Protocol.Groth16R1CS.scalarPrime :=
    Symbolic.resolve_sound resolver inputs values denotes (.add intermediateLeft right) absorbed absorbedBuilt
  have absorbedModel : model values[absorbed]! = model values[intermediateLeft]! + model values[right]! := by
    rw [absorbedValue]
    change model ((_ + _) % Q) = _
    rw [model_mod]
    simp only [model, Nat.cast_add]
  let row := signalLinear resolver.nodes compiledGraph
  have rowV : ∀ index, linearValue assignment (row index) = assignment index := rowValue
  let s1 := seed.constraint (minusLinear (row level.rightInput) (row level.leftInput))
    (row level.selector) (minusLinear (row level.leftOutput) (row level.leftInput))
  have v1 : SystemSatisfied assignment s1 := by
    apply constraint_emit assignment constant seed _ _ _ valid
    simpa only [minusLinear_value, rowV, inputLeftS, inputRightS, selectorS, leftS] using gates.1
  let s2 := s1.constraint (minusLinear (row level.leftInput) (row level.rightInput))
    (row level.selector) (minusLinear (row level.rightOutput) (row level.rightInput))
  have v2 : SystemSatisfied assignment s2 := by
    apply constraint_emit assignment constant s1 _ _ _ v1
    simpa only [minusLinear_value, rowV, inputLeftS, inputRightS, selectorS, rightS] using gates.2.1
  let s3 := s2.constraint (row level.selector) (minusLinear (row level.selector) (constantLinear 1)) []
  have v3 : SystemSatisfied assignment s3 := by
    apply constraint_emit assignment constant s2 _ _ _ v2
    simpa only [minusLinear_value, rowV, selectorS, constantLinear_value assignment constant,
      show model 1 = (1 : Fr) from by simp [model], show linearValue assignment ([] : Linear) = 0 from rfl] using gates.2.2
  let s4 := s3.equality sponge.first.key (constantLinear 0)
  have v4 : SystemSatisfied assignment s4 := by
    apply equality_emit assignment s3 _ _ v3
    rw [constantLinear_value assignment constant]
    simpa only [zeroValue] using firstKeyS
  let s5 := s4.equality sponge.first.leftInput (row level.leftOutput)
  have v5 : SystemSatisfied assignment s5 := by
    apply equality_emit assignment s4 _ _ v4
    rw [rowV, leftS]
    exact firstLeftS
  let s6 := s5.equality sponge.first.rightInput (constantLinear 0)
  have v6 : SystemSatisfied assignment s6 := by
    apply equality_emit assignment s5 _ _ v5
    rw [constantLinear_value assignment constant]
    simpa only [zeroValue] using firstRightS
  let s7 := feistelLocalSystem resolver.nodes compiledGraph constants s6 sponge.first
  have v7 : SystemSatisfied assignment s7 := feistelLocalSystem_sound resolver inputs values denotes canonical compiledGraph constants
    firstInputs first sponge.first assignment constant rowValue firstBuilt firstAliases (interp firstAfter) s6 v6
  let s8 := s7.equality sponge.second.key (constantLinear 0)
  have v8 : SystemSatisfied assignment s8 := by
    apply equality_emit assignment s7 _ _ v7
    rw [constantLinear_value assignment constant]
    simpa only [zeroValue] using secondKeyS
  let s9 := s8.equality sponge.second.leftInput (addLinear (row sponge.first.leftOutput) (row level.rightOutput))
  have v9 : SystemSatisfied assignment s9 := by
    apply equality_emit assignment s8 _ _ v8
    rw [linear_add, rowV, rowV, intermediateLeftS, rightS]
    exact secondLeftS.trans absorbedModel
  let s10 := s9.equality sponge.second.rightInput (row sponge.first.rightOutput)
  have v10 : SystemSatisfied assignment s10 := by
    apply equality_emit assignment s9 _ _ v9
    rw [rowV, intermediateRightS]
    exact secondRightS
  let s11 := feistelLocalSystem resolver.nodes compiledGraph constants s10 sponge.second
  have v11 : SystemSatisfied assignment s11 := feistelLocalSystem_sound resolver inputs values denotes canonical compiledGraph constants
    secondInputs second sponge.second assignment constant rowValue secondBuilt secondAliases (interp secondAfter) s10 v10
  have v12 : SystemSatisfied assignment (s11.equality level.hashOutput (row sponge.second.leftOutput)) := by
    apply equality_emit assignment s11 _ _ v11
    rw [rowV, hashInputS]
    exact hashS
  simpa only [merkleLocalSystem] using v12

end TornadoProofs.Witness.Local

#print axioms TornadoProofs.Witness.Local.merkleLocalSystem_sound
