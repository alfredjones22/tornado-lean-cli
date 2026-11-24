import Std

/-! Numeric curve orders shared by pure primitives. No key derivation or
application module is imported to obtain a constant. -/
namespace LeanCrypto

def secp256k1Order : Nat :=
  0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

def bn254BasePrime : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

def bn254ScalarPrime : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

end LeanCrypto
