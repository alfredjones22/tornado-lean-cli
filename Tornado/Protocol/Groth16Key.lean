import Lean

/-!
Checked header and section layout for the exact pinned SDK Tornado proving key.
This does not decode or validate points, polynomials, or Groth16 proofs.
-/

namespace Tornado.Protocol.Groth16Key

structure Header where
  nVars : Nat
  nPublic : Nat
  domainSize : Nat
  polsA : Nat
  polsB : Nat
  pointsA : Nat
  pointsB1 : Nat
  pointsB2 : Nat
  pointsC : Nat
  hExps : Nat
  deriving Inhabited, Repr

def readU32LE (bytes : ByteArray) (start : Nat) : Except String Nat := do
  if start + 4 > bytes.size then throw "Truncated Groth16 key header."
  return bytes[start]!.toNat + bytes[start + 1]!.toNat * 2 ^ 8 +
    bytes[start + 2]!.toNat * 2 ^ 16 + bytes[start + 3]!.toNat * 2 ^ 24

def readHeader (bytes : ByteArray) : Except String Header := do
  if bytes.size < 40 then throw "Truncated Groth16 key header."
  return {
    nVars := (← readU32LE bytes 0),
    nPublic := (← readU32LE bytes 4),
    domainSize := (← readU32LE bytes 8),
    polsA := (← readU32LE bytes 12),
    polsB := (← readU32LE bytes 16),
    pointsA := (← readU32LE bytes 20),
    pointsB1 := (← readU32LE bytes 24),
    pointsB2 := (← readU32LE bytes 28),
    pointsC := (← readU32LE bytes 32),
    hExps := (← readU32LE bytes 36)
  }

/-- The exact offsets of the pinned key, plus the point-section lengths implied
    by its dimensions. Sparse polynomial section sizes cannot be inferred just
    from `nVars`, so accepting arbitrary monotone offsets would be unsafe. -/
def sectionLayoutValid (h : Header) (totalBytes : Nat) : Bool :=
  h.nVars == 28300 && h.nPublic == 6 && h.domainSize == 32768 &&
  h.polsA == 488 && h.polsB == 1506204 && h.pointsA == 3369616 &&
  h.pointsB1 == 5180816 && h.pointsB2 == 6992016 &&
  h.pointsC == 10614416 && h.hExps == 12425168 &&
  h.pointsA + h.nVars * 64 == h.pointsB1 &&
  h.pointsB1 + h.nVars * 64 == h.pointsB2 &&
  h.pointsB2 + h.nVars * 128 == h.pointsC &&
  h.pointsC + (h.nVars - h.nPublic - 1) * 64 == h.hExps &&
  h.hExps + (h.domainSize - 1) * 64 == totalBytes

/-- Header validation is a necessary condition before a native key
    parser trusts the pinned offsets, but does not establish that section
    contents are valid. The full asset hash must also be checked by its caller. -/
def decodeHeader (headerBytes : ByteArray) (totalBytes : Nat) : Except String Header :=
  match readHeader headerBytes with
  | .error error => .error error
  | .ok h =>
      if sectionLayoutValid h totalBytes then .ok h
      else .error "Groth16 key section layout is invalid."

theorem decoded_header_has_valid_layout (bytes : ByteArray) (totalBytes : Nat)
    (h : Header) (decoded : decodeHeader bytes totalBytes = .ok h) :
    sectionLayoutValid h totalBytes = true := by
  cases read : readHeader bytes with
  | error error => simp [decodeHeader, read] at decoded
  | ok candidate =>
    cases valid : sectionLayoutValid candidate totalBytes with
    | false => simp [decodeHeader, read, valid] at decoded
    | true =>
      simp [decodeHeader, read, valid] at decoded
      cases decoded
      exact valid

end Tornado.Protocol.Groth16Key

#print axioms Tornado.Protocol.Groth16Key.decoded_header_has_valid_layout
