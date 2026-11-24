import LeanCrypto.SHA256

/-! SHA-256 and HMAC-SHA256 vectors. Empty/abc and RFC 4231 test 1 are
    published standard vectors; boundary cases were cross-checked against
    Node's `crypto` implementation used by the TypeScript CLI. -/

namespace LeanCrypto.SHA256Tests

private def rangeBytes (count : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:count] do
    bytes := bytes.push (UInt8.ofNat (i % 256))
  return bytes

private def repeatedByte (count : Nat) (byte : UInt8) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for _ in [0:count] do
    bytes := bytes.push byte
  return bytes

private def check (label actual expected : String) : IO Unit :=
  if actual == expected then pure ()
  else throw <| IO.userError s!"{label}: got {actual}, expected {expected}"

def main : IO Unit := do
  check "sha256 empty" (sha256Hex (rangeBytes 0))
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  check "sha256 abc" (sha256Hex "abc".toUTF8)
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  check "sha256 55" (sha256Hex (rangeBytes 55))
    "463eb28e72f82e0a96c0a4cc53690c571281131f672aa229e0d45ae59b598b59"
  check "sha256 56" (sha256Hex (rangeBytes 56))
    "da2ae4d6b36748f2a318f23e7ab1dfdf45acdc9d049bd80e59de82a60895f562"
  check "sha256 63" (sha256Hex (rangeBytes 63))
    "29af2686fd53374a36b0846694cc342177e428d1647515f078784d69cdb9e488"
  check "sha256 64" (sha256Hex (rangeBytes 64))
    "fdeab9acf3710362bd2658cdc9a29e8f9c757fcf9811603a8c447cd1d9151108"
  check "sha256 65" (sha256Hex (rangeBytes 65))
    "4bfd2c8b6f1eec7a2afeb48b934ee4b2694182027e6d0fc075074f2fabb31781"
  check "sha256 128" (sha256Hex (rangeBytes 128))
    "471fb943aa23c511f6f72f8d1652d9c880cfa392ad80503120547703e56a2be5"
  check "sha256 4096" (sha256Hex (rangeBytes 4096))
    "c8f5d0341d54d951a71b136e6e2afcb14d11ed8489a7ae126a8fee0df6ecf193"
  check "hmac RFC 4231 #1"
    (hmacSHA256Hex (repeatedByte 20 0x0b) "Hi There".toUTF8)
    "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
  check "hmac empty key" (hmacSHA256Hex (repeatedByte 0 0xaa) "message".toUTF8)
    "eb08c1f56d5ddee07f7bdf80468083da06b64cf4fac64fe3a90883df5feacae4"
  check "hmac 64-byte key" (hmacSHA256Hex (repeatedByte 64 0xaa) "message".toUTF8)
    "1f0f5ab0e94dd93e8396341927e03bd9767e94f58ef0417e892619074d058eba"
  check "hmac 65-byte key" (hmacSHA256Hex (repeatedByte 65 0xaa) "message".toUTF8)
    "5e7054f27681c4344b10e3359059fff5f97544686c3d64e0dc0283d0f4524ade"
  check "hmac 131-byte key" (hmacSHA256Hex (repeatedByte 131 0xaa) "message".toUTF8)
    "4d23fbaefa37dfdeae330fa18600c33d324708a258b32623108f0da230039554"
  IO.println "SHA-256/HMAC-SHA256: 14 compatibility vectors passed"

end LeanCrypto.SHA256Tests

def main : IO Unit := LeanCrypto.SHA256Tests.main
