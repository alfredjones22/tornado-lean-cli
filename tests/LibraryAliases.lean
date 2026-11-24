import Tornado

example : Tornado.Crypto.SecpAffine = LeanCrypto.SecpAffine := rfl
example : Tornado.Crypto.SecpSignature = LeanCrypto.SecpSignature := rfl
example : Tornado.Crypto.BIP32PrivateNode = LeanCrypto.BIP32PrivateNode := rfl
example : Tornado.Crypto.MimcTree = LeanCrypto.MimcTree := rfl
example : Tornado.Crypto.MimcProof = LeanCrypto.MimcProof := rfl
example (x y recovery : Nat) : Tornado.Crypto.SecpSignature.mk x y recovery = LeanCrypto.SecpSignature.mk x y recovery := rfl
example (sig : Tornado.Crypto.SecpSignature) : Tornado.Crypto.SecpSignature.canonicalRS sig = LeanCrypto.SecpSignature.canonicalRS sig := rfl
example (width : Nat) : Tornado.Encoding.FixedBytes.Bytes width = LeanCrypto.FixedBytes.Bytes width := rfl
example (width value : Nat) : Tornado.Encoding.FixedBytes.encode width value = LeanCrypto.FixedBytes.encode width value := rfl
example (bytes : Tornado.Encoding.FixedBytes.Bytes 32) :
    Tornado.Encoding.FixedBytes.ofNat (Tornado.Encoding.FixedBytes.toNat bytes) = bytes :=
  Tornado.Encoding.FixedBytes.ofNat_toNat bytes

def main : IO Unit := do
  unless Tornado.Crypto.keccak256Hex "abc".toUTF8 = LeanCrypto.keccak256Hex "abc".toUTF8 do
    throw <| IO.userError "Legacy alias changed Keccak output."
  IO.println "PASS: legacy aliases preserve canonical structures, constructors, projections, proof terms and hash output"
