import Tornado.Domain.Invoice
import Tornado.Crypto.TornadoSignature

/-!
Pure note creation and backup formatting for the pinned CLI. Randomness and
private file I/O are supplied by the effectful caller.
No function here samples entropy or writes a secret.
-/

namespace Tornado.Domain

open Tornado.Crypto

structure CreatedNote where
  raw : String
  preimage : String
  pool : Pool
  commitment : String
  nullifierHash : String
  id : String
  nonce : Option Nat := none
  call : DepositCall
  -- raw and preimage are spendable secrets, so generic Repr is unsafe.
  deriving BEq, Inhabited

private def bytesLE (value length : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for index in [0:length] do
    result := result.push ((value / 2 ^ (8 * index) % 256).toUInt8)
  return result

private def reversed (bytes : ByteArray) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for index in [0:bytes.size] do
    result := result.push bytes[bytes.size - index - 1]!
  return result

private def byteHex (byte : UInt8) : String :=
  let alphabet := "0123456789abcdef".toList.toArray
  String.ofList [alphabet[byte.toNat / 16]!, alphabet[byte.toNat % 16]!]

/-- Deterministic RFC 4122 version-four UUID from 16 separately supplied
    random bytes. The entropy source is not implemented by this pure module. -/
def uuidV4FromEntropy (entropy : ByteArray) : Except String String := do
  if entropy.size != 16 then throw "UUID entropy must contain exactly 16 bytes."
  let mut bytes := entropy
  bytes := bytes.set! 6 ((bytes[6]!.toNat % 16 + 64).toUInt8)
  bytes := bytes.set! 8 ((bytes[8]!.toNat % 64 + 128).toUInt8)
  let hex := String.join (bytes.data.toList.map byteHex)
  return String.intercalate "-" [
    String.ofList (hex.toList.take 8),
    String.ofList ((hex.toList.drop 8).take 4),
    String.ofList ((hex.toList.drop 12).take 4),
    String.ofList ((hex.toList.drop 16).take 4),
    String.ofList (hex.toList.drop 20)]

private def checkPool (pool : Pool) : Except String Nat := do
  let some known := poolFor pool.chainId pool.denomination pool.asset.symbol
    | throw "This Tornado pool is unavailable."
  if known.address.toLower != pool.address.toLower then
    throw "This Tornado pool is unavailable."
  let address ← parseHexBytes pool.address
  if address.size != 20 then throw "This Tornado pool is unavailable."
  return address.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def fromPreimage (pool : Pool) (nullifier secret : ByteArray)
    (id : String) (nonce : Option Nat) : Except String CreatedNote := do
  if nullifier.size != 31 || secret.size != 31 then
    throw "Each Classic note secret must contain 31 bytes."
  let preimageBytes := nullifier ++ secret
  let preimage := bytesToHex preimageBytes
  let raw := s!"tornado-{pool.asset.symbol.toLower}-{pool.denomination}-{chainNumber pool.chainId}-0x{preimage}"
  let commitment ← toHex32 (← pedersenX preimageBytes)
  let nullifierHash ← toHex32 (← pedersenX nullifier)
  let deposit ← depositCall pool commitment
  return { raw := raw, preimage := preimage, pool := pool, commitment := commitment,
           nullifierHash := nullifierHash, id := id, nonce := nonce, call := deposit }

/-- Exact SDK `coalesceSecret`: interpret the 32-byte keystore value as a
    big-endian integer, serialize it little-endian, append chain and pool in
    little-endian, Keccak-256, then mask to 248 bits. The mask keeps the first
    31 digest bytes. -/
def legacyCoalescedSecret (key : ByteArray) (chainId poolAddress : Nat) : Except String ByteArray := do
  if key.size != 32 then throw "Legacy keystore key must contain 32 bytes."
  if chainId >= 2 ^ 64 || poolAddress >= 2 ^ 160 then
    throw "Legacy note chain or pool address is out of range."
  return (keccak256 (reversed key ++ bytesLE chainId 8 ++ bytesLE poolAddress 20)).extract 0 31

/-- Pure independent-note derivation from the two *separately sampled* keys
    used by the pinned SDK's keystore paths at deposit index zero. The UUID
    has its own entropy input and does not influence the note secrets. -/
def independentNoteFromEntropy (pool : Pool) (nullifierKey saltKey uuidEntropy : ByteArray) :
    Except String CreatedNote := do
  let address ← checkPool pool
  let nullifier ← legacyCoalescedSecret nullifierKey (chainNumber pool.chainId) address
  let secret ← legacyCoalescedSecret saltKey (chainNumber pool.chainId) address
  let id ← uuidV4FromEntropy uuidEntropy
  fromPreimage pool nullifier secret id none

/-- Seeded session recovery derives one note per selected pool with a
    contiguous nonce sequence, sharing the native BIP32 signing key. The
    supplied UUID inputs are independent of the mnemonic and note secrets. -/
def seededNotesFromMnemonic (pools : List Pool) (mnemonic : String)
    (uuidEntropy : List ByteArray) : Except String (List CreatedNote) := do
  let some first := pools.head? | throw "Choose at least one note."
  if pools.length != uuidEntropy.length then
    throw "Each note needs its own UUID entropy."
  if uuidEntropy.eraseDups.length != uuidEntropy.length then
    throw "Each note needs distinct UUID entropy."
  let _ ← checkPool first
  for pool in pools do
    let _ ← checkPool pool
    if pool.chainId != first.chainId || pool.asset.symbol != first.asset.symbol then
      throw "Use supported pools of one asset on one network per deposit session."
  let signingKey ← tornadoNoteSigningKeyFromMnemonic mnemonic
  let mut result := []
  for (pool, nonce) in pools.zipIdx do
    let address ← checkPool pool
    let derived ← tornadoSignatureNote signingKey.privateKey (chainNumber pool.chainId) nonce address
    let id ← uuidV4FromEntropy uuidEntropy[nonce]!
    result := result ++ [← fromPreimage pool derived.nullifierBytes derived.secretBytes id (some nonce)]
  return result

private def rawBackup (notes : List CreatedNote) : String :=
  String.intercalate "\n" (notes.map (·.raw)) ++ "\n"

private def derivationReference : String :=
  "https://github.com/ethereum/kohaku/blob/886f72ddd6e36d43e53675fc359fd4a315590ee8/packages/tornado-cash/src/account/signature-keys.ts"

private def seedKeyReference : String :=
  "https://github.com/ethereum/kohaku/blob/886f72ddd6e36d43e53675fc359fd4a315590ee8/packages/plugins/src/host/mnemonic-keystore.ts"

/-- Exact user-facing backup text produced by the pinned CLI. The caller
    must durably create a protected file before using it for real deposits. -/
def formatDepositBackup (notes : List CreatedNote) (seedPhrase : Option String := none) :
    Except String String := do
  let raw := rawBackup notes
  match seedPhrase with
  | none => return raw
  | some phrase =>
    if phrase.isEmpty then return raw
    if notes.isEmpty then throw "There are no notes to back up."
    let nonceList := String.intercalate ", " (notes.map fun note =>
      match note.nonce with | none => "" | some nonce => toString nonce)
    return "------- SEED PHRASE (SECRET) --------\n" ++ phrase ++
      "\n-------------------------------------\n\n" ++
      "-------- NOTES (SECRET) --------\n" ++ raw ++
      "--------------------------------\n\n" ++
      "-------- METADATA --------\n" ++
      "Anyone with the seed phrase above can find and control ALL of these Tornado notes.\n" ++
      "Each individual note string is also secret material: anyone with access to it can spend that note.\n\n" ++
      s!"Note nonces: {nonceList} (in the same order as the notes above).\n\n" ++
      "Exact note derivation reference (Kohaku SDK, fixed commit):\n" ++
      derivationReference ++ "\n\n" ++
      "Seed-to-key implementation (same commit):\n" ++ seedKeyReference ++ "\n" ++
      "--------------------------\n"

end Tornado.Domain
