import LeanCrypto.Groth16.Types
import Lean
import Tornado.Crypto.SHA256
import Tornado.Protocol.BN254G2
import Tornado.Protocol.Groth16Key
import Tornado.Protocol.Groth16R1CS

/-!
Native decoding of the pinned Tornado Groth16 proving key: affine G1/G2 query
points and sparse A/B polynomials.
The legacy key stores each field element as a 32-byte little-endian Montgomery
residue. This module converts those encodings into canonical Fp/Fr values and
rejects truncated, noncanonical, duplicate, or out-of-range records.

The complete-key entry point SHA-256-authenticates the entire decompressed
asset once. It still does not implement G2 subgroup checks, FFT, MSM, pairing,
or Groth16 proof generation.
-/

namespace Tornado.Protocol.ProvingKey

open Tornado.Protocol.Groth16R1CS
open Tornado.Crypto

/-- BN254 base-field modulus, distinct from the scalar modulus in R1CS. -/
def fpPrime : Nat :=
  0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

/-- Inverses of R = 2^256 in the two key encoding fields. -/
def fpRInverse : Nat :=
  20988524275117001072002809824448087578619730785600314334253784976379291040311

def frRInverse : Nat :=
  9915499612839321149637521777990102151350674507940716049588462388200839649614

theorem fpRInverse_correct : (2 ^ 256 * fpRInverse) % fpPrime = 1 := by decide
theorem frRInverse_correct : (2 ^ 256 * frRInverse) % scalarPrime = 1 := by decide

def readU256LE (bytes : ByteArray) (offset : Nat) : Except String Nat := do
  if offset + 32 > bytes.size then throw "Truncated proving-key field element."
  let mut value := 0
  for i in [0:32] do
    value := value * 256 + bytes[offset + 31 - i]!.toNat
  return value

private def readMontgomery (bytes : ByteArray) (offset prime inverse : Nat) :
    Except String Nat := do
  let encoded ← readU256LE bytes offset
  if encoded >= prime then throw "Noncanonical proving-key Montgomery residue."
  return encoded * inverse % prime

def readMontgomeryFp (bytes : ByteArray) (offset : Nat) : Except String Nat :=
  readMontgomery bytes offset fpPrime fpRInverse

def readMontgomeryFr (bytes : ByteArray) (offset : Nat) : Except String Nat :=
  readMontgomery bytes offset scalarPrime frRInverse

export LeanCrypto.Groth16.Types
  (AffineG1 AffineG1.mk AffineG1.x AffineG1.y AffineG1.onCurve
   DecodedG1 DecodedG1.identity DecodedG1.point DecodedG1.valid)

/-- Decode the SDK's affine G1 format. The old `(0,1)` sentinel means the
    group identity; every other decoded point must satisfy y² = x³ + 3. -/
def readG1 (bytes : ByteArray) (offset : Nat) : Except String DecodedG1 := do
  if offset + 64 > bytes.size then throw "Truncated proving-key G1 point."
  let x ← readMontgomeryFp bytes offset
  let y ← readMontgomeryFp bytes (offset + 32)
  if x == 0 && y == 1 then return .identity
  let point : AffineG1 := ⟨x, y⟩
  if !point.onCurve then throw "Proving-key G1 point is not on BN254."
  return .point point

export LeanCrypto.Groth16.Types (DecodedG2 DecodedG2.identity DecodedG2.point)

/-- Decode the SDK's four Fp limbs in `(c0,c1)` order for each Fp2
    coordinate. The old `((0,0),(1,0))` sentinel means the group identity.
    Nonidentity points are checked on the BN254 twist, but this is not a
    subgroup check. -/
def readG2 (bytes : ByteArray) (offset : Nat) : Except String DecodedG2 := do
  if offset + 128 > bytes.size then throw "Truncated proving-key G2 point."
  let x0 ← readMontgomeryFp bytes offset
  let x1 ← readMontgomeryFp bytes (offset + 32)
  let y0 ← readMontgomeryFp bytes (offset + 64)
  let y1 ← readMontgomeryFp bytes (offset + 96)
  if x0 == 0 && x1 == 0 && y0 == 1 && y1 == 0 then return .identity
  return .point (← Tornado.Protocol.BN254G2.Affine.checked x0 x1 y0 y1)

def readG1Section (bytes : ByteArray) (start stop count : Nat) :
    Except String (Array DecodedG1) := do
  if stop > bytes.size || start + count * 64 != stop then
    throw "G1 query section has the wrong length."
  let mut points := #[]
  for i in [0:count] do
    points := points.push (← readG1 bytes (start + i * 64))
  return points

def readG2Section (bytes : ByteArray) (start stop count : Nat) :
    Except String (Array DecodedG2) := do
  if stop > bytes.size || start + count * 128 != stop then
    throw "G2 query section has the wrong length."
  let mut points := #[]
  for i in [0:count] do
    points := points.push (← readG2 bytes (start + i * 128))
  return points

export LeanCrypto.Groth16.Types
  (PolynomialEntry PolynomialEntry.mk PolynomialEntry.constraint PolynomialEntry.coefficient
   Polynomial Polynomial.mk Polynomial.entries)

/-- Decode one SDK sparse-polynomial record. Each signal starts with a u32
    count, followed by (u32 constraint index, Montgomery Fr coefficient)
    entries. `stop` must be the trusted end of its A or B key section. -/
def readPolynomialAt (bytes : ByteArray) (offset stop domainSize : Nat) :
    Except String (Polynomial × Nat) := do
  if stop > bytes.size || offset + 4 > stop then
    throw "Truncated proving-key polynomial count."
  let count ← Groth16Key.readU32LE bytes offset
  if count > domainSize || offset + 4 + count * 36 > stop then
    throw "Proving-key polynomial exceeds its section."
  let mut entries := #[]
  let mut seen : Std.HashSet Nat := {}
  let mut cursor := offset + 4
  for _ in [0:count] do
    let constraint ← Groth16Key.readU32LE bytes cursor
    if constraint >= domainSize || seen.contains constraint then
      throw "Duplicate or out-of-range proving-key polynomial row."
    seen := seen.insert constraint
    let coefficient ← readMontgomeryFr bytes (cursor + 4)
    entries := entries.push ⟨constraint, coefficient⟩
    cursor := cursor + 36
  return (⟨entries⟩, cursor)

/-- Decode exactly `nVars` records and reject unused or truncated bytes. -/
def readPolynomialSection (bytes : ByteArray) (start stop nVars domainSize : Nat) :
    Except String (Array Polynomial) := do
  if start > stop || stop > bytes.size then
    throw "Invalid proving-key polynomial section bounds."
  let mut cursor := start
  let mut polynomials := #[]
  for _ in [0:nVars] do
    let (polynomial, next) ← readPolynomialAt bytes cursor stop domainSize
    polynomials := polynomials.push polynomial
    cursor := next
  if cursor != stop then throw "Proving-key polynomial section has trailing bytes."
  return polynomials

def pinnedKeySHA256 : String :=
  "8e2d2f22beafb5a9666daebca57b13f8029c3656c65fcfbcc86e2418fa16a3af"

/-- Exact authenticated key bytes and a header whose fixed section layout was
    checked. Both facts are represented as kernel-visible propositions. -/
structure PinnedKey where
  private mk ::
  bytes : ByteArray
  header : Tornado.Protocol.Groth16Key.Header
  digest : sha256Hex bytes = pinnedKeySHA256
  layout : Tornado.Protocol.Groth16Key.decodeHeader bytes bytes.size = .ok header

def authenticatePinnedKey (bytes : ByteArray) : Except String PinnedKey :=
  if bytes.size != 14522256 then
    .error "The pinned proving key has the wrong byte length."
  else if digest : sha256Hex bytes = pinnedKeySHA256 then
    match layout : Tornado.Protocol.Groth16Key.decodeHeader bytes bytes.size with
    | .error error => .error error
    | .ok header => .ok ⟨bytes, header, digest, layout⟩
  else .error "The proving key differs from its pinned SHA-256."

structure ParsedKey where
  header : Tornado.Protocol.Groth16Key.Header
  vkAlpha1 : DecodedG1
  vkBeta1 : DecodedG1
  vkDelta1 : DecodedG1
  vkBeta2 : DecodedG2
  vkDelta2 : DecodedG2
  polsA : Array Polynomial
  polsB : Array Polynomial
  queryA : Array DecodedG1
  queryB1 : Array DecodedG1
  queryB2 : Array DecodedG2
  queryC : Array DecodedG1
  hExps : Array DecodedG1

/-- Parse every key section after authenticating the complete raw binary.
    `queryC` contains the 28,293 stored private-signal points; the SDK later
    prefixes seven identity placeholders for the public signals. -/
def decodeFullKey (pinned : PinnedKey) : Except String ParsedKey := do
  let bytes := pinned.bytes
  let h := pinned.header
  let vkAlpha1 ← readG1 bytes 40
  let vkBeta1 ← readG1 bytes 104
  let vkDelta1 ← readG1 bytes 168
  let vkBeta2 ← readG2 bytes 232
  let vkDelta2 ← readG2 bytes 360
  let polsA ← readPolynomialSection bytes h.polsA h.polsB h.nVars h.domainSize
  let polsB ← readPolynomialSection bytes h.polsB h.pointsA h.nVars h.domainSize
  let queryA ← readG1Section bytes h.pointsA h.pointsB1 h.nVars
  let queryB1 ← readG1Section bytes h.pointsB1 h.pointsB2 h.nVars
  let queryB2 ← readG2Section bytes h.pointsB2 h.pointsC h.nVars
  let queryC ← readG1Section bytes h.pointsC h.hExps (h.nVars - h.nPublic - 1)
  let hExps ← readG1Section bytes h.hExps bytes.size (h.domainSize - 1)
  return ⟨h, vkAlpha1, vkBeta1, vkDelta1, vkBeta2, vkDelta2,
    polsA, polsB, queryA, queryB1, queryB2, queryC, hExps⟩

theorem authenticated_key_has_pinned_digest (pinned : PinnedKey) :
    sha256Hex pinned.bytes = pinnedKeySHA256 := pinned.digest

theorem authenticated_key_has_valid_header (pinned : PinnedKey) :
    Tornado.Protocol.Groth16Key.decodeHeader pinned.bytes pinned.bytes.size =
      .ok pinned.header := pinned.layout

end Tornado.Protocol.ProvingKey

#print axioms Tornado.Protocol.ProvingKey.fpRInverse_correct
#print axioms Tornado.Protocol.ProvingKey.frRInverse_correct
#print axioms Tornado.Protocol.ProvingKey.authenticated_key_has_pinned_digest
#print axioms Tornado.Protocol.ProvingKey.authenticated_key_has_valid_header
