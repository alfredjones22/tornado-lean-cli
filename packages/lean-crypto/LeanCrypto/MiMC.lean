import LeanCrypto.Keccak

/-!
Circomlib-compatible MiMC sponge over the BN254 scalar field, matching the
pinned `micro-zk-proofs/mimcsponge.js` and Kohaku MiMC Merkle tree. Round
constants are derived in Lean from Ethereum Keccak-256; no external table or
crypto FFI is needed.

Callers building many Merkle nodes should compute `mimcConstants` once and
reuse it with `mimcHashPairWith`, instead of re-deriving 218 constants for
every node.
-/

namespace LeanCrypto

def mimcFieldPrime : Nat :=
  0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001

private def fromBE (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

/-- `getIV("mimcsponge")` from micro-zk-proofs. The standard sponge starts
    at zero and does not use this IV, but it is exposed for parity checks. -/
def mimcIV : Nat :=
  fromBE (keccak256 "mimcsponge_iv".toUTF8) % mimcFieldPrime

/-- The 220 MiMC constants, including zero first and last endpoints. -/
def mimcConstants : Array Nat := Id.run do
  let mut table : Array Nat := #[0]
  let mut current := keccak256 "mimcsponge".toUTF8
  for _ in [0:218] do
    current := keccak256 current
    table := table.push (fromBE current % mimcFieldPrime)
  return table.push 0

private def fifthPower (value : Nat) : Nat :=
  let squared := value * value % mimcFieldPrime
  squared * squared % mimcFieldPrime * value % mimcFieldPrime

/-- One 220-round MiMC sponge permutation. The constants argument must be
    `mimcConstants` (220 values); other lengths are rejected. -/
def mimcPermutationWith (constants : Array Nat) (left right key : Nat) : Except String (Nat × Nat) := do
  if constants.size != 220 then throw "MiMC requires exactly 220 round constants"
  let mut l := left % mimcFieldPrime
  let mut r := right % mimcFieldPrime
  let k := key % mimcFieldPrime
  for i in [0:220] do
    let t := (l + k + constants[i]!) % mimcFieldPrime
    let next := (r + fifthPower t) % mimcFieldPrime
    if i < 219 then
      r := l
      l := next
    else
      r := next
  return (l, r)

/-- Hash a list of field elements, returning the first sponge output. -/
def mimcMultiHashWith (constants : Array Nat) (inputs : Array Nat)
    (key : Nat := 0) : Except String Nat := do
  if constants.size != 220 then throw "MiMC requires exactly 220 round constants"
  let mut left := 0
  let mut right := 0
  for value in inputs do
    let (l, r) ← mimcPermutationWith constants ((left + value) % mimcFieldPrime) right key
    left := l
    right := r
  return left

/-- MiMC parent hash used by the 20-level Classic Tornado tree. -/
def mimcHashPairWith (constants : Array Nat) (left right : Nat) : Except String Nat :=
  mimcMultiHashWith constants #[left, right]

def mimcHashPair (left right : Nat) : Except String Nat :=
  mimcHashPairWith mimcConstants left right

end LeanCrypto
