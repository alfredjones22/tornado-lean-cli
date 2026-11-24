import Tornado.Crypto.BIP32
import Tornado.Crypto.Secp256k1
import Tornado.Crypto.Pedersen

/-!
Native implementation of the SDK's Tornado signature-v1 seeded-note
derivation: EIP-712 envelope, deterministic low-S secp256k1 signature,
pool-bound Keccak secrets, and BabyJubJub Pedersen public identifiers.
-/

namespace Tornado.Crypto

private def natToBytesBE (n count : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:count] do
    bytes := bytes.push ((n / 2 ^ (8 * (count - 1 - i)) % 256).toUInt8)
  return bytes

private def bytesToNatLE (bytes : ByteArray) : Nat := Id.run do
  let mut n := 0
  for i in [0:bytes.size] do
    n := n + (bytes.get! i).toNat * 2 ^ (8 * i)
  return n

private def tornadoDomainHash (chainId : Nat) : ByteArray :=
  keccak256 (
    keccak256 "EIP712Domain(string name,string version,uint256 chainId,bytes32 salt)".toUTF8 ++
    keccak256 "TornadoCash Keychain".toUTF8 ++
    keccak256 "1".toUTF8 ++
    natToBytesBE chainId 32 ++
    keccak256 "tornado".toUTF8)

private def tornadoNoteStructHash (nonce : Nat) : ByteArray :=
  keccak256 (
    keccak256 "TornadoCashNote(uint64 nonce)".toUTF8 ++
    natToBytesBE nonce 32)

/-- Digest signed by the SDK's `TornadoCashNote(uint64 nonce)` EIP-712
    envelope, including its chain-bound domain and fixed `tornado` salt. -/
def tornadoNoteTypedDataHash (chainId nonce : Nat) : Except String ByteArray := do
  if chainId == 0 || chainId >= 2 ^ 256 then
    throw "Tornado EIP-712 chain ID is outside uint256"
  if nonce >= 2 ^ 64 then throw "Tornado note nonce is outside uint64"
  return keccak256 ((ByteArray.empty.push 0x19 |>.push 0x01) ++
    tornadoDomainHash chainId ++ tornadoNoteStructHash nonce)

/-- Signed note envelope, matching viem deterministic low-S signing. -/
def tornadoNoteSignature (privateKey : ByteArray) (chainId nonce : Nat) : Except String SecpSignature := do
  let digest ← tornadoNoteTypedDataHash chainId nonce
  secp256k1SignDigest privateKey digest

private def trunc31 (tag : String) (poolAddress : Nat) (signature : SecpSignature) : ByteArray :=
  (keccak256 (tag.toUTF8 ++ natToBytesBE poolAddress 20 ++ signature.canonicalRS)).extract 0 31

structure TornadoSignatureNote where
  nullifierBytes : ByteArray
  secretBytes : ByteArray
  commitment : Nat
  nullifierHash : Nat
  deriving Inhabited

def TornadoSignatureNote.preimage (note : TornadoSignatureNote) : ByteArray :=
  note.nullifierBytes ++ note.secretBytes

def TornadoSignatureNote.nullifier (note : TornadoSignatureNote) : Nat :=
  bytesToNatLE note.nullifierBytes

def TornadoSignatureNote.secret (note : TornadoSignatureNote) : Nat :=
  bytesToNatLE note.secretBytes

/-- Derive both secret preimages and the two public Pedersen identifiers. -/
def tornadoSignatureNote (privateKey : ByteArray) (chainId nonce poolAddress : Nat) : Except String TornadoSignatureNote := do
  if poolAddress >= 2 ^ 160 then throw "Tornado pool address is outside 20 bytes"
  let signature ← tornadoNoteSignature privateKey chainId nonce
  let nullifierBytes := trunc31 "nullifier" poolAddress signature
  let secretBytes := trunc31 "secret" poolAddress signature
  let commitment ← pedersenX (nullifierBytes ++ secretBytes)
  let nullifierHash ← pedersenX nullifierBytes
  return { nullifierBytes, secretBytes, commitment, nullifierHash }

/-- Full mnemonic-to-note path, useful for recovery and independent parity
    checks. Reuse a derived BIP32 private key across sequential nonces. -/
def tornadoSignatureNoteFromMnemonic (mnemonic : String) (chainId nonce poolAddress : Nat) : Except String TornadoSignatureNote := do
  let signer ← tornadoNoteSigningKeyFromMnemonic mnemonic
  tornadoSignatureNote signer.privateKey chainId nonce poolAddress

end Tornado.Crypto
