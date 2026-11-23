import Tornado.Crypto.BIP39

/-!
Pure hardened BIP32 private-key derivation for the Tornado note-signing path
`m/29795'/1'/0'`. This module derives keys without public-key operations;
secp256k1 and EIP-712 signing are separate protocol operations.
-/

namespace Tornado.Crypto

def secp256k1Order : Nat :=
  0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

structure BIP32PrivateNode where
  privateKey : ByteArray
  chainCode : ByteArray

private def bytesToNatBE (bytes : ByteArray) : Nat := Id.run do
  let mut result := 0
  for byte in bytes.data do result := result * 256 + byte.toNat
  return result

private def natToBytesBE (value length : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for i in [0:length] do
    result := result.push ((value / 2 ^ (8 * (length - 1 - i)) % 256).toUInt8)
  return result

/-- BIP32 master node from a 128..512-bit seed. -/
def bip32MasterFromSeed (seed : ByteArray) : Except String BIP32PrivateNode := do
  if seed.size < 16 || seed.size > 64 then
    throw "BIP32 master seed must be 16..64 bytes"
  let i := hmacSHA512 "Bitcoin seed".toUTF8 seed
  let key := i.extract 0 32
  let scalar := bytesToNatBE key
  if scalar == 0 || scalar >= secp256k1Order then
    throw "BIP32 master secret is outside the secp256k1 scalar range"
  return { privateKey := key, chainCode := i.extract 32 64 }

/-- Derive a hardened child from the unhardened index, retrying consecutive
    child indexes if the BIP32 scalar is invalid, as `@scure/bip32` does. -/
def bip32HardenedChild (parent : BIP32PrivateNode) (index : Nat) : Except String BIP32PrivateNode := do
  if parent.privateKey.size != 32 || parent.chainCode.size != 32 then
    throw "BIP32 parent key and chain code must each be 32 bytes"
  if index >= 0x80000000 then
    throw "BIP32 hardened child index must be below 2^31"
  let parentScalar := bytesToNatBE parent.privateKey
  if parentScalar == 0 || parentScalar >= secp256k1Order then
    throw "BIP32 parent private key is invalid"
  for attempt in [0:100] do
    let candidate := index + attempt
    if candidate >= 0x80000000 then
      throw "BIP32 hardened child index exhausted"
    let data := (ByteArray.empty.push 0) ++ parent.privateKey ++
      natToBytesBE (candidate + 0x80000000) 4
    let i := hmacSHA512 parent.chainCode data
    let tweak := bytesToNatBE (i.extract 0 32)
    if tweak < secp256k1Order then
      let childScalar := (parentScalar + tweak) % secp256k1Order
      if childScalar != 0 then
        return {
          privateKey := natToBytesBE childScalar 32,
          chainCode := i.extract 32 64
        }
  throw "BIP32 hardened child derivation exhausted 100 retries"

def bip32HardenedPath (master : BIP32PrivateNode) (path : List Nat) : Except String BIP32PrivateNode := do
  let mut node := master
  for index in path do
    node ← bip32HardenedChild node index
  return node

/-- The exact Tornado signature-v1 note key path for account index 0. -/
def tornadoNoteSigningKeyFromMnemonic (mnemonic : String) : Except String BIP32PrivateNode := do
  let seed ← mnemonicToSeedEnglish mnemonic
  let master ← bip32MasterFromSeed seed
  bip32HardenedPath master [29795, 1, 0]

end Tornado.Crypto
