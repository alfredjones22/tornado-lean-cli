import Lean
import Tornado.Protocol.Groth16Key
import Tornado.Domain.NoteIdentity

open Lean Tornado.Protocol.Groth16Key Tornado.Domain

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def check (json : Json) : Except String Unit := do
  let compressedHash ← (← json.getObjVal? "compressedSourceSha256").getStr?
  let plainHash ← (← json.getObjVal? "uncompressedSha256").getStr?
  require (compressedHash == "806676308b1fc825a97aad47eaec0499f665a1da3f3d0a0e35f7bbf6796bcd32")
    "Pinned compressed key hash changed."
  require (plainHash == "8e2d2f22beafb5a9666daebca57b13f8029c3656c65fcfbcc86e2418fa16a3af")
    "Pinned uncompressed key hash changed."
  let totalBytes ← (← json.getObjVal? "uncompressedBytes").getNat?
  let header ← parseHexBytes (← (← json.getObjVal? "header").getStr?)
  require (header.size == 40) "Pinned key header is not 40 bytes."
  let decoded ← decodeHeader header totalBytes
  require (decoded.nVars == 28300 && decoded.nPublic == 6 && decoded.domainSize == 32768)
    "Pinned key dimensions changed."
  require (decoded.polsA == 488 && decoded.polsB == 1506204 && decoded.pointsA == 3369616 &&
    decoded.pointsB1 == 5180816 && decoded.pointsB2 == 6992016 &&
    decoded.pointsC == 10614416 && decoded.hExps == 12425168)
    "Pinned key section offsets changed."
  require ((decodeHeader header (totalBytes - 1)).isOk == false)
    "Wrong key length was accepted."
  require ((decodeHeader (header.extract 0 39) totalBytes).isOk == false)
    "Truncated header was accepted."
  let altered := header.set! 24 0
  require ((decodeHeader altered totalBytes).isOk == false)
    "Corrupted point offset was accepted."
  let shiftedPolynomial := header.set! 16 ((header[16]!.toNat + 1).toUInt8)
  require ((decodeHeader shiftedPolynomial totalBytes).isOk == false)
    "Corrupted sparse-polynomial offset was accepted."

def main : IO UInt32 := do
  let raw ← IO.FS.readFile "fixtures/groth16-key-header.json"
  match Json.parse raw >>= check with
  | .error error =>
      IO.eprintln error
      return 1
  | .ok _ =>
      IO.println "PASS: pinned Groth16 key header layout and 4 corruption checks"
      return 0
