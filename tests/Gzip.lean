import Lean
import Tornado.Compression.Gzip
import Tornado.Domain.NoteIdentity
import Tornado.Crypto.SHA256

open Lean Tornado.Compression.Gzip Tornado.Domain Tornado.Crypto

private def unwrap (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError s!"{label}: {message}"

private def ensure (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw <| IO.userError label

private def textField (json : Json) (name : String) : Except String String := do
  (← json.getObjVal? name).getStr?

private def byteChanged (bytes : ByteArray) (index : Nat) (value : UInt8) : ByteArray :=
  ⟨bytes.data.set! index value⟩

private def smallVectors : IO Unit := do
  let fixture ← unwrap "parse gzip fixture" <|
    Json.parse (← IO.FS.readFile "fixtures/gzip-vectors.json")
  let cases ← unwrap "gzip cases" <| fixture.getObjVal? "cases" >>= Json.getArr?
  ensure (cases.size == 6) "Expected six gzip vectors."
  let mut seenKinds := #[]
  for item in cases do
    let name ← unwrap "case name" <| textField item "name"
    let compressedHex ← unwrap s!"{name} gzip hex" <| textField item "gzipHex"
    let compressed ← unwrap s!"{name} gzip bytes" <| parseHexBytes compressedHex
    let rawHex ← unwrap s!"{name} raw hex" <| textField item "rawHex"
    let raw ← unwrap s!"{name} raw bytes" <| parseHexBytes rawHex
    let kind ← unwrap "first block type" <|
      item.getObjVal? "firstBlockType" >>= Json.getNat?
    seenKinds := seenKinds.push kind
    let decoded ← unwrap s!"decode {name}" <| decompress compressed raw.size
    ensure (decoded == raw) s!"{name} DEFLATE bytes differ from zlib."
    let expectedHash ← unwrap "expected SHA-256" <| textField item "sha256"
    ensure (sha256Hex decoded == expectedHash)
      s!"{name} SHA-256 differs from zlib output."
    let expectedCrc ← unwrap "expected CRC32" <|
      item.getObjVal? "crc32" >>= Json.getNat?
    ensure ((crc32 decoded).toNat == expectedCrc)
      s!"{name} CRC32 differs from gzip."
    if name == "stored" then
      ensure (!(decompress (byteChanged compressed 13 (compressed[13]! + 1)) raw.size).isOk)
        "Invalid stored-block LEN/NLEN was accepted."
    if name == "optional" then
      ensure (!(decompress (byteChanged compressed 14 (compressed[14]! + 1)) raw.size).isOk)
        "Optional header CRC mismatch was accepted."
    if !raw.isEmpty then
      ensure (!(decompress compressed (raw.size - 1)).isOk)
        s!"{name} exceeded an undersized output bound."
    ensure (!(decompress (byteChanged compressed 0 0) raw.size).isOk)
      s!"{name} invalid gzip magic was accepted."
    ensure (!(decompress (byteChanged compressed 3 0xe0) raw.size).isOk)
      s!"{name} reserved gzip flags were accepted."
    ensure (!(decompress (byteChanged compressed (compressed.size - 8)
      (compressed[compressed.size - 8]! + 1)) raw.size).isOk)
      s!"{name} corrupt data CRC was accepted."
    ensure (!(decompress (byteChanged compressed (compressed.size - 4)
      (compressed[compressed.size - 4]! + 1)) raw.size).isOk)
      s!"{name} corrupt ISIZE was accepted."
    ensure (!(decompress (compressed.extract 0 (compressed.size - 1)) raw.size).isOk)
      s!"{name} truncated stream was accepted."
    ensure (!(decompress (compressed ++ compressed) (2 * raw.size)).isOk)
      s!"{name} concatenated members were accepted."
  ensure (seenKinds.contains 0 && seenKinds.contains 1 && seenKinds.contains 2)
    "Stored, fixed, and dynamic DEFLATE blocks were not all covered."
  let first ← unwrap "first case" <| cases[0]!.getObjVal? "gzipHex" >>= Json.getStr?
  let firstBytes ← unwrap "first gzip hex" <| parseHexBytes first
  ensure (!(decompress (byteChanged firstBytes 10 0x07) 0).isOk)
    "Reserved DEFLATE block type was accepted."
  ensure (!(decompress firstBytes (hardLimit + 1)).isOk)
    "Output bound above the hard limit was accepted."
  let manyHex ← unwrap "block-amplification fixture" <|
    textField fixture "tooManyFixedBlocksHex"
  let many ← unwrap "block-amplification bytes" <| parseHexBytes manyHex
  ensure (!(decompress many 0).isOk)
    "More than 4096 fixed DEFLATE blocks were accepted."

private def pinnedAssets (circuitPath keyPath : String) : IO Unit := do
  let compressedCircuit ← IO.FS.readBinFile circuitPath
  let circuit ← unwrap "native pinned circuit decompression" <|
    pinnedCircuit compressedCircuit
  ensure (circuit.size == 19474889) "Pinned circuit has the wrong size."
  let compressedKey ← IO.FS.readBinFile keyPath
  let key ← unwrap "native pinned proving-key decompression" <|
    pinnedProvingKey compressedKey
  ensure (key.size == 14522256) "Pinned proving key has the wrong size."
  IO.println "PASS: native Lean decompressed and authenticated both pinned proving assets"

def main (args : List String) : IO UInt32 := do
  try
    smallVectors
    match args with
    | [] => pure ()
    | [circuitPath, keyPath] => pinnedAssets circuitPath keyPath
    | _ => throw <| IO.userError "Usage: Gzip.lean [circuit.gz key.gz]"
    IO.println "PASS: 6 native gzip/DEFLATE vectors and malformed-stream guards"
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1
