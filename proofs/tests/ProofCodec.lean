import LeanCryptoProofs.ProofCodec

open Lean LeanCrypto.BN254 LeanCrypto.Groth16 LeanCrypto.Proofs.Groth16Codec

private def requireCodec (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrapCodec (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def natFieldCodec (json : Json) (field : String) : IO Nat := do
  let text ← unwrapCodec (json.getObjVal? field >>= Json.getStr?)
  match text.toNat? with
  | some value => pure value
  | none => throw (IO.userError "Malformed public codec fixture")

private def rescaleCodec (point : G1.Affine) (scale : Nat) : G1.Jacobian :=
  let z := G1.Fp.ofNat scale
  ⟨point.x.mul (z.pow 2), point.y.mul (z.pow 3), z⟩

def main : IO Unit := do
  let fixture ← unwrapCodec (Json.parse (← IO.FS.readFile "../packages/lean-crypto/fixtures/groth16-msm-vectors.json"))
  let result ← unwrapCodec (fixture.getObjVal? "assembly" >>= (·.getObjVal? "result"))
  let aJson ← unwrapCodec (result.getObjVal? "piA")
  let bJson ← unwrapCodec (result.getObjVal? "piB")
  let cJson ← unwrapCodec (result.getObjVal? "piC")
  let a ← unwrapCodec (G1.Affine.checked (← natFieldCodec aJson "x") (← natFieldCodec aJson "y"))
  let b ← unwrapCodec (G2.Affine.checked (← natFieldCodec bJson "x0") (← natFieldCodec bJson "x1")
    (← natFieldCodec bJson "y0") (← natFieldCodec bJson "y1"))
  let c ← unwrapCodec (G1.Affine.checked (← natFieldCodec cJson "x") (← natFieldCodec cJson "y"))
  let expectedHex ← unwrapCodec (result.getObjVal? "solidityHex" >>= Json.getStr?)
  let limbs := affineLimbs a b c
  requireCodec (limbs.length == 8 && b.x.c0.val != b.x.c1.val && b.y.c0.val != b.y.c1.val)
    "Fixture no longer distinguishes G2 Solidity limb order"
  let mut reference := ByteArray.empty
  for aScale in #[1, 2, 17, G1.basePrime - 1] do
    for cScale in #[1, 2, 17, G1.basePrime - 1] do
      let proof : Types.ProofPoints := ⟨rescaleCodec a aScale, G2.Jacobian.ofAffine b,
        rescaleCodec c cScale, #[2]⟩
      let bytes ← unwrapCodec (MSM.solidityProofBytes proof)
      requireCodec (bytes.size == 256 && "0x" ++ LeanCrypto.Hex.encode bytes == expectedHex)
        "Actual serializer differs from pinned independent Solidity word fixture"
      requireCodec (decodeWords 8 bytes.data.toList == limbs)
        "Actual serialized bytes do not recover all eight original limbs"
      for i in [0:8] do
        requireCodec (LeanCrypto.FixedBytes.decode (bytes.extract (32 * i) (32 * (i + 1))) == limbs[i]!)
          "One actual independent 32-byte slice decodes to the wrong limb"
      let changedMetadata ← unwrapCodec (MSM.solidityProofBytes {proof with publicSignals := #[7, 8, 9]})
      requireCodec (changedMetadata == bytes) "Serializer unexpectedly depends on public-signal metadata"
      requireCodec (!(MSM.solidityProofBytes {proof with piA := G1.Jacobian.infinity}).isOk)
        "Serializer accepted A at infinity"
      requireCodec (!(MSM.solidityProofBytes {proof with piB := G2.Jacobian.infinity}).isOk)
        "Serializer accepted B at infinity"
      requireCodec (!(MSM.solidityProofBytes {proof with piC := G1.Jacobian.infinity}).isOk)
        "Serializer accepted C at infinity"
      reference := bytes
  for i in [0:8] do
    let index := 32 * i + 31
    let mutated := reference.set! index (reference[index]! + 1)
    let decoded := decodeWords 8 mutated.data.toList
    requireCodec (decoded[i]! != limbs[i]!) "A changed encoded limb did not change its decoded value"
    for other in [0:8] do
      if other != i then requireCodec (decoded[other]! == limbs[other]!) "A limb mutation changed another decoded limb"
  for value in #[0, 1, 255, 256, 2 ^ 248, 2 ^ 256 - 1] do
    let word ← unwrapCodec (wordProgram value)
    requireCodec (word.size == 32 && LeanCrypto.FixedBytes.decode word == value)
      "Actual-helper reference lost fixed width or uint256 roundtrip"
  requireCodec (!(wordProgram (2 ^ 256)).isOk) "Word helper admitted uint256 overflow"
  let zero ← unwrapCodec (wordProgram 0)
  requireCodec (zero.data.all (· == 0)) "Zero word did not retain all leading zero bytes"
  IO.println "PASS: actual 256-byte Solidity proof codec, pinned limb order, 16 projective representations, 8 independent limb mutations, metadata independence and uint256 boundaries"
