import Lean
import Tornado.Crypto.SHA256

/-!
Bounded, single-member gzip and RFC 1951 DEFLATE decoder written in Lean.
It supports stored, fixed-Huffman, and dynamic-Huffman blocks. It never uses
zlib or a native decompression FFI. The decoder rejects malformed headers,
tables, backreferences, checksums, sizes, and trailing bytes.
-/

namespace Tornado.Compression.Gzip

def hardLimit : Nat := 32 * 1024 * 1024
def maxBlocks : Nat := 4096

private def invalid : String := "Invalid or unsupported gzip/DEFLATE stream."

private def little16 (bytes : ByteArray) (pos : Nat) : Nat :=
  bytes[pos]!.toNat + 256 * bytes[pos + 1]!.toNat

private def little32 (bytes : ByteArray) (pos : Nat) : Nat :=
  bytes[pos]!.toNat + 256 * bytes[pos + 1]!.toNat +
    65536 * bytes[pos + 2]!.toNat + 16777216 * bytes[pos + 3]!.toNat

private def crcTable : Array UInt32 := Id.run do
  let mut table := #[]
  for i in [0:256] do
    let mut value := UInt32.ofNat i
    for _ in [0:8] do
      value := if value &&& 1 == 1 then
        (value >>> 1) ^^^ (0xedb88320 : UInt32)
      else value >>> 1
    table := table.push value
  return table

/-- IEEE CRC-32 used by gzip's member trailer and optional header CRC. -/
def crc32 (bytes : ByteArray) : UInt32 := Id.run do
  let table := crcTable
  let mut state : UInt32 := 0xffffffff
  for byte in bytes.data do
    let index := ((state ^^^ byte.toUInt32) &&& 0xff).toNat
    state := (state >>> 8) ^^^ table[index]!
  return state ^^^ 0xffffffff

private def boundedZeroTerminated (bytes : ByteArray) (start stop : Nat) :
    Except String Nat := do
  let mut pos := start
  while pos < stop && bytes[pos]! != 0 do
    pos := pos + 1
  if pos >= stop then throw invalid
  return pos + 1

/-- Return the first DEFLATE byte after a strictly parsed gzip header. -/
def headerEnd (bytes : ByteArray) : Except String Nat := do
  if bytes.size < 18 || bytes.size > hardLimit then throw invalid
  if bytes[0]! != 0x1f || bytes[1]! != 0x8b || bytes[2]! != 8 then
    throw invalid
  let flags := bytes[3]!.toNat
  if flags % 256 >= 32 then throw invalid
  let trailer := bytes.size - 8
  let mut pos := 10
  if flags % 8 >= 4 then
    if pos + 2 > trailer then throw invalid
    let extraLength := little16 bytes pos
    pos := pos + 2 + extraLength
    if pos > trailer then throw invalid
  if flags % 16 >= 8 then
    pos ← boundedZeroTerminated bytes pos trailer
  if flags % 32 >= 16 then
    pos ← boundedZeroTerminated bytes pos trailer
  if flags % 4 >= 2 then
    if pos + 2 > trailer then throw invalid
    if (crc32 (bytes.extract 0 pos)).toNat % 65536 != little16 bytes pos then
      throw "Gzip header CRC mismatch."
    pos := pos + 2
  if pos >= trailer then throw invalid
  return pos

private structure Decoder where
  input : ByteArray
  bitPos : Nat
  trailer : Nat
  output : ByteArray := ByteArray.empty
  outputLimit : Nat

private abbrev DecodeM := StateT Decoder (Except String)

private def readBits (count : Nat) : DecodeM Nat := do
  let state ← get
  if count > 16 || state.bitPos + count > state.trailer * 8 then
    throw "Truncated DEFLATE bitstream."
  let mut value := 0
  for i in [0:count] do
    let pos := state.bitPos + i
    let byte := state.input[pos / 8]!.toNat
    value := value + (byte / 2 ^ (pos % 8) % 2) * 2 ^ i
  set { state with bitPos := state.bitPos + count }
  return value

private def alignByte : DecodeM Unit := do
  let state ← get
  let aligned := (state.bitPos + 7) / 8 * 8
  if aligned > state.trailer * 8 then throw invalid
  set { state with bitPos := aligned }

private def appendLiteral (byte : Nat) : DecodeM Unit := do
  let state ← get
  if byte > 255 || state.output.size >= state.outputLimit then
    throw "DEFLATE output exceeds its configured bound."
  set { state with output := state.output.push byte.toUInt8 }

private def appendMatch (length distance : Nat) : DecodeM Unit := do
  let state ← get
  if distance == 0 || distance > state.output.size ||
      length > state.outputLimit - state.output.size then
    throw "Invalid or oversized DEFLATE backreference."
  let mut output := state.output
  for _ in [0:length] do
    output := output.push output[output.size - distance]!
  set { state with output := output }

private def reverseBits (value length : Nat) : Nat := Id.run do
  let mut bits := value
  let mut result := 0
  for _ in [0:length] do
    result := result * 2 + bits % 2
    bits := bits / 2
  return result

private structure Huffman where
  rows : Array (Array (Option Nat))
  maxBits : Nat

private def makeHuffman (lengths : Array Nat) (allowEmpty : Bool := false) :
    Except String (Option Huffman) := do
  let mut counts := Array.replicate 16 0
  for length in lengths do
    if length > 15 then throw "DEFLATE code length exceeds 15 bits."
    if length > 0 then counts := counts.set! length (counts[length]! + 1)
  if (counts.toList.drop 1).all (· == 0) then
    if allowEmpty then return none else throw "Empty DEFLATE Huffman alphabet."
  let mut available := 1
  for bits in [1:16] do
    available := available * 2
    if counts[bits]! > available then
      throw "Oversubscribed DEFLATE Huffman alphabet."
    available := available - counts[bits]!
  let mut nextCode := Array.replicate 16 0
  let mut code := 0
  for bits in [1:16] do
    code := (code + counts[bits - 1]!) * 2
    nextCode := nextCode.set! bits code
  let mut rows : Array (Array (Option Nat)) := Array.replicate 16 #[]
  for bits in [1:16] do
    rows := rows.set! bits (Array.replicate (2 ^ bits) none)
  for symbol in [0:lengths.size] do
    let length := lengths[symbol]!
    if length > 0 then
      let value := nextCode[length]!
      if value >= 2 ^ length then throw invalid
      nextCode := nextCode.set! length (value + 1)
      let reversed := reverseBits value length
      let row := rows[length]!
      if row[reversed]!.isSome then throw invalid
      rows := rows.set! length (row.set! reversed (some symbol))
  let maxBits := (List.range 16).foldl (fun result n =>
    if counts[n]! > 0 then n else result) 0
  return some ⟨rows, maxBits⟩

private def expectHuffman (result : Except String (Option Huffman)) :
    DecodeM Huffman := do
  match result with
  | .ok (some table) => return table
  | .ok none => throw "Empty DEFLATE Huffman alphabet."
  | .error message => throw message

private def readSymbol (table : Huffman) : DecodeM Nat := do
  let state ← get
  let mut code := 0
  let mut weight := 1
  let mut pos := state.bitPos
  for length in [1:table.maxBits + 1] do
    if pos >= state.trailer * 8 then throw "Truncated DEFLATE bitstream."
    let byte := state.input[pos / 8]!.toNat
    code := code + (byte / 2 ^ (pos % 8) % 2) * weight
    pos := pos + 1
    weight := weight * 2
    if let some symbol := table.rows[length]![code]! then
      set { state with bitPos := pos }
      return symbol
  throw "Invalid DEFLATE Huffman code."

private def fixedLiteralLengths : Array Nat := Id.run do
  let mut lengths := #[]
  for symbol in [0:288] do
    lengths := lengths.push
      (if symbol <= 143 then 8 else if symbol <= 255 then 9
       else if symbol <= 279 then 7 else 8)
  return lengths

private def codeLengthOrder : Array Nat := #[
  16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

private def dynamicTables : DecodeM (Huffman × Option Huffman) := do
  let nLiteral := (← readBits 5) + 257
  let nDistance := (← readBits 5) + 1
  let nCodeLength := (← readBits 4) + 4
  if nLiteral > 286 || nDistance > 32 then throw invalid
  let mut codeLengths := Array.replicate 19 0
  for i in [0:nCodeLength] do
    codeLengths := codeLengths.set! codeLengthOrder[i]! (← readBits 3)
  let codeTable ← expectHuffman (makeHuffman codeLengths)
  let total := nLiteral + nDistance
  let mut lengths := #[]
  while lengths.size < total do
    let symbol ← readSymbol codeTable
    if symbol <= 15 then lengths := lengths.push symbol
    else
      let (value, repetitions) ← if symbol == 16 then do
        if lengths.isEmpty then throw invalid
        pure (lengths[lengths.size - 1]!, (← readBits 2) + 3)
      else if symbol == 17 then
        pure (0, (← readBits 3) + 3)
      else if symbol == 18 then
        pure (0, (← readBits 7) + 11)
      else throw invalid
      if lengths.size + repetitions > total then throw invalid
      for _ in [0:repetitions] do lengths := lengths.push value
  let literalLengths := lengths.extract 0 nLiteral
  if literalLengths[256]! == 0 then throw "DEFLATE end-of-block code is missing."
  let distanceLengths := lengths.extract nLiteral total
  let literal ← expectHuffman (makeHuffman literalLengths)
  let distance ← match makeHuffman distanceLengths true with
    | .ok table => pure table
    | .error message => throw message
  return (literal, distance)

private def lengthBases : Array Nat := #[
  3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27,
  31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]

private def lengthExtra : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2,
  2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]

private def distanceBases : Array Nat := #[
  1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129,
  193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097,
  6145, 8193, 12289, 16385, 24577]

private def distanceExtra : Array Nat := #[
  0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6,
  6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

private def decodeCodes (literal : Huffman) (distance : Option Huffman) :
    DecodeM Unit := do
  let mut finished := false
  while !finished do
    let symbol ← readSymbol literal
    if symbol < 256 then appendLiteral symbol
    else if symbol == 256 then finished := true
    else if symbol <= 285 then
      let index := symbol - 257
      let length := lengthBases[index]! + (← readBits lengthExtra[index]!)
      let some distanceTable := distance
        | throw "DEFLATE length code has no distance alphabet."
      let distanceSymbol ← readSymbol distanceTable
      if distanceSymbol >= 30 then throw "Reserved DEFLATE distance code."
      let offset := distanceBases[distanceSymbol]! +
        (← readBits distanceExtra[distanceSymbol]!)
      appendMatch length offset
    else throw "Reserved DEFLATE literal/length code."

private def decodeStored : DecodeM Unit := do
  alignByte
  let length := (← readBits 16)
  let complement := (← readBits 16)
  if length + complement != 65535 then throw "Invalid DEFLATE stored-block length."
  let state ← get
  if length > state.outputLimit - state.output.size then
    throw "DEFLATE output exceeds its configured bound."
  if state.bitPos / 8 + length > state.trailer then
    throw "Truncated DEFLATE stored block."
  let mut output := state.output
  for i in [0:length] do
    output := output.push state.input[state.bitPos / 8 + i]!
  set { state with bitPos := state.bitPos + 8 * length, output := output }

private def decodeDeflate : DecodeM Unit := do
  let mut finalBlock := false
  let mut blocks := 0
  let mut fixedTables : Option (Huffman × Huffman) := none
  while !finalBlock do
    if blocks >= maxBlocks then
      throw "DEFLATE block count exceeds its configured bound."
    blocks := blocks + 1
    finalBlock := (← readBits 1) == 1
    let kind ← readBits 2
    if kind == 0 then decodeStored
    else if kind == 1 then
      let (literal, distance) ← match fixedTables with
        | some tables => pure tables
        | none => do
          let literal ← expectHuffman (makeHuffman fixedLiteralLengths)
          let distance ← expectHuffman (makeHuffman (Array.replicate 32 5))
          fixedTables := some (literal, distance)
          pure (literal, distance)
      decodeCodes literal (some distance)
    else if kind == 2 then
      let (literal, distance) ← dynamicTables
      decodeCodes literal distance
    else throw "Reserved DEFLATE block type."

def trailerValid (bytes output : ByteArray) (maxOutput : Nat) : Prop :=
  output.size ≤ maxOutput ∧
  output.size % (2 ^ 32) = little32 bytes (bytes.size - 8 + 4) ∧
  crc32 output = UInt32.ofNat (little32 bytes (bytes.size - 8))

private def verifyTrailer (bytes output : ByteArray) (maxOutput : Nat) :
    Except String ByteArray := by
  letI : Decidable (trailerValid bytes output maxOutput) := by
    unfold trailerValid
    infer_instance
  exact
  if trailerValid bytes output maxOutput then .ok output
  else .error "Gzip output failed size or CRC validation."

theorem verifyTrailer_sound (bytes output result : ByteArray) (maxOutput : Nat)
    (h : verifyTrailer bytes output maxOutput = .ok result) :
    result = output ∧ output.size ≤ maxOutput ∧
    output.size % (2 ^ 32) = little32 bytes (bytes.size - 8 + 4) ∧
    crc32 output = UInt32.ofNat (little32 bytes (bytes.size - 8)) := by
  unfold verifyTrailer at h
  split at h
  · rename_i valid
    cases h
    exact ⟨rfl, valid.1, valid.2.1, valid.2.2⟩
  · contradiction

private def inflate (bytes : ByteArray) (maxOutput : Nat) : Except String ByteArray := do
  if maxOutput > hardLimit then throw "Gzip output bound exceeds 32 MiB."
  let start ← headerEnd bytes
  let trailer := bytes.size - 8
  let initial : Decoder := {
    input := bytes, bitPos := 8 * start, trailer := trailer,
    outputLimit := maxOutput }
  let (_, finalState) ← decodeDeflate.run initial
  if (finalState.bitPos + 7) / 8 != trailer then
    throw "Trailing or incomplete DEFLATE data."
  return finalState.output

/-- Decode one bounded gzip member with header/trailer integrity checks. -/
def decompress (bytes : ByteArray) (maxOutput : Nat) : Except String ByteArray := do
  let output ← inflate bytes maxOutput
  verifyTrailer bytes output maxOutput

theorem decompress_success_integrity (bytes output : ByteArray) (maxOutput : Nat)
    (h : decompress bytes maxOutput = .ok output) :
    output.size ≤ maxOutput ∧
    output.size % (2 ^ 32) = little32 bytes (bytes.size - 8 + 4) ∧
    crc32 output = UInt32.ofNat (little32 bytes (bytes.size - 8)) := by
  unfold decompress at h
  cases hInflate : inflate bytes maxOutput with
  | error message => simp [hInflate, bind, Except.bind] at h
  | ok raw =>
      have checked : verifyTrailer bytes raw maxOutput = .ok output := by
        simpa [hInflate] using h
      obtain ⟨same, bound, size, crc⟩ :=
        verifyTrailer_sound bytes raw output maxOutput checked
      subst output
      exact ⟨bound, size, crc⟩

private def authenticateAsset (compressed : ByteArray) (compressedHash : String)
    (rawHash : String) (rawLength : Nat) : Except String ByteArray := do
  if Tornado.Crypto.sha256Hex compressed != compressedHash then
    throw "Compressed proving asset differs from the pinned SHA-256."
  let raw ← decompress compressed rawLength
  if raw.size != rawLength || Tornado.Crypto.sha256Hex raw != rawHash then
    throw "Decompressed proving asset differs from the pinned SHA-256."
  return raw

/-- Authenticate and decode the exact pinned Tornado Circom JSON asset. -/
def pinnedCircuit (compressed : ByteArray) : Except String ByteArray :=
  authenticateAsset compressed
    "22b240a07985e1f7f5e4520029b65cce0276eafd35d67080c70a3990aa892ed6"
    "3ddd61dbff09caeec82d8edde95c674a3c34f9e66b1fe9f2c8783e72fe536f98"
    19474889

/-- Authenticate and decode the exact pinned binary Tornado proving key. -/
def pinnedProvingKey (compressed : ByteArray) : Except String ByteArray :=
  authenticateAsset compressed
    "806676308b1fc825a97aad47eaec0499f665a1da3f3d0a0e35f7bbf6796bcd32"
    "8e2d2f22beafb5a9666daebca57b13f8029c3656c65fcfbcc86e2418fa16a3af"
    14522256

end Tornado.Compression.Gzip

#print axioms Tornado.Compression.Gzip.verifyTrailer_sound
#print axioms Tornado.Compression.Gzip.decompress_success_integrity
