import LeanCrypto

/-! A neutral consumer: no Tornado import, CLI/RPC/native helper, proving
asset, catalog, or application namespace occurs in this module. -/

open LeanCrypto

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw <| IO.userError error

example (value : Fin (256 ^ 32)) :
    FixedBytes.toNat (FixedBytes.ofNat value) = value := FixedBytes.toNat_ofNat value

example (bytes : FixedBytes.Bytes 32) :
    FixedBytes.ofNat (FixedBytes.toNat bytes) = bytes := FixedBytes.ofNat_toNat bytes

example (q budget value : Nat) (positive : 0 < q) (fits : q ≤ 2 ^ 256)
    (allowed : Sampling.admissible q value = true) :
    Probability.ByteEntropy.byteMass 32 q budget (Probability.Rejection.valueEvent value) * (q - 1) =
      Probability.ByteEntropy.byteMass 32 q budget Probability.Rejection.successEvent :=
  Probability.ByteEntropy.bytes32_conditional_uniform q budget value positive fits allowed

example (D q budget value : Nat) (positive : 0 < q) (fits : q ≤ D)
    (allowed : Sampling.admissible q value = true) :
    Probability.Rejection.mass D q budget (Probability.Rejection.valueEvent value) * (q - 1) =
      Probability.Rejection.mass D q budget Probability.Rejection.successEvent :=
  Probability.Rejection.conditional_uniform D q budget value positive fits allowed

def main : IO Unit := do
  require (keccak256Hex "abc".toUTF8 ==
    "0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45") "Keccak consumer vector failed."
  require (sha256Hex "abc".toUTF8 ==
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad") "SHA256 consumer vector failed."
  require ((sha512 "abc".toUTF8).size == 64) "SHA512 consumer width failed."
  require (blake256Hex ByteArray.empty ==
    "716f6e863f744b9ac22c97ec7b76ea5f5908bc5b2f67c61510bfc4751384ea7a") "BLAKE256 consumer vector failed."
  let encoded := FixedBytes.encode 32 42
  require (encoded.size == 32 && FixedBytes.decode encoded == 42) "Fixed-width consumer roundtrip failed."
  let seed := ByteArray.mk ((List.range 16).map Nat.toUInt8).toArray
  let master ← checked <| bip32MasterFromSeed seed
  let node ← checked <| bip32HardenedPath master [0, 1]
  require (node.privateKey.size == 32 && node.chainCode.size == 32) "Hardened-only BIP32 consumer derivation failed."
  let signature ← checked <| secp256k1SignDigest (FixedBytes.encode 32 1) (sha256 "consumer".toUTF8)
  require (signature.r > 0 && signature.r < secp256k1Order &&
    signature.s > 0 && signature.s ≤ secp256k1Order / 2 && signature.bytes65.size == 65)
    "Secp256k1 consumer signature shape failed."
  require (!(Sampling.admitCandidate (FixedBytes.encode 31 1)).isOk) "Malformed sampling width accepted."
  require ((Sampling.admitValue 0).isNone && (Sampling.admitValue bn254ScalarPrime).isNone &&
    (Sampling.admitValue 1).isSome) "Rejection sampling consumer bounds failed."
  let drawn ← IO.mkRef (0 : Nat)
  let sample : IO (Option Nat) := do
    drawn.modify (· + 1)
    if (← drawn.get) < 3 then return none else return some 7
  let sampled ← Sampling.sampleLoop sample (throw <| IO.userError "Exhausted consumer sample.") 5
  require (sampled == 7 && (← drawn.get) == 3) "Shared bounded sampler read beyond success."
  IO.println "PASS: neutral standalone consumer, fixed-byte proof aliases, hash/key/signature vectors and shared sampler bounds"
