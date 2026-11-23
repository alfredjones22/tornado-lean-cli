import Tornado.Crypto.MiMC

/-!
Twenty-level Classic Tornado MiMC Merkle tree, including zero nodes and
membership paths. The layer layout matches the pinned Kohaku
`@kohaku-eth/mimc-tree` / `fixed-merkle-tree` implementation. Hashing uses
the pure Lean MiMC sponge in `MiMC.lean`.

The full tree builder is O(number of leaves) in MiMC hashes and stores all
layers, so large mainnet pools incur work proportional to their complete
deposit history.
-/

namespace Tornado.Crypto

def mimcZeroLeaf : Nat :=
  21663839004416932945382355908790599225266501822907911457504978515578255421292

structure MimcTree where
  levels : Nat
  zeros : Array Nat
  layers : Array (Array Nat)
  root : Nat
  deriving Repr

structure MimcProof where
  index : Nat
  root : Nat
  siblings : Array Nat
  pathIndices : Array Nat
  deriving Repr

/-- Build a tree with levels 0..20. Leaves preserve their input values in
    layer zero; MiMC normalizes them into the BN254 scalar field when hashed. -/
def buildMimcTreeWith (constants : Array Nat) (leaves : Array Nat)
    (levels : Nat := 20) : Except String MimcTree := do
  if constants.size != 220 then throw "MiMC requires exactly 220 round constants"
  if levels > 20 then throw "Tornado MiMC tree supports at most 20 levels"
  if leaves.size > 2 ^ levels then throw "Tornado MiMC tree is full"
  let mut zeros : Array Nat := #[mimcZeroLeaf]
  for level in [0:levels] do
    let previous := zeros[level]!
    zeros := zeros.push (← mimcHashPairWith constants previous previous)
  let mut layers : Array (Array Nat) := #[leaves]
  let mut current := leaves
  for level in [0:levels] do
    let mut next : Array Nat := #[]
    for i in [0:(current.size + 1) / 2] do
      let left := current[2 * i]!
      let right := if 2 * i + 1 < current.size then current[2 * i + 1]!
        else zeros[level]!
      next := next.push (← mimcHashPairWith constants left right)
    layers := layers.push next
    current := next
  let root := if current.isEmpty then zeros[levels]! else current[0]!
  return ⟨levels, zeros, layers, root⟩

def buildMimcTree (leaves : Array Nat) (levels : Nat := 20) : Except String MimcTree :=
  buildMimcTreeWith mimcConstants leaves levels

/-- Membership path for an exact leaf index, including zero siblings. -/
def mimcProofAt (tree : MimcTree) (index : Nat) : Except String MimcProof := do
  let leaves := tree.layers[0]!
  if index >= leaves.size then throw "MiMC leaf index is out of bounds"
  let mut position := index
  let mut siblings : Array Nat := #[]
  let mut pathIndices : Array Nat := #[]
  for level in [0:tree.levels] do
    let layer := tree.layers[level]!
    let siblingIndex := if position % 2 == 0 then position + 1 else position - 1
    let sibling := if siblingIndex < layer.size then layer[siblingIndex]!
      else tree.zeros[level]!
    siblings := siblings.push sibling
    pathIndices := pathIndices.push (position % 2)
    position := position / 2
  return ⟨index, tree.root, siblings, pathIndices⟩

/-- Match SDK `tree.indexOf(leaf)` by taking the first exact occurrence. -/
def mimcProofForLeaf (tree : MimcTree) (leaf : Nat) : Except String MimcProof := do
  let leaves := tree.layers[0]!
  for i in [0:leaves.size] do
    if leaves[i]! == leaf then return (← mimcProofAt tree i)
  throw "MiMC leaf was not found"

/-- Recompute a 0..20-level path using the same MiMC parent hash. -/
def verifyMimcProofWith (constants : Array Nat) (leaf : Nat)
    (proof : MimcProof) : Except String Bool := do
  if proof.siblings.size != proof.pathIndices.size || proof.siblings.size > 20 then
    throw "Invalid MiMC proof depth"
  if proof.index >= 2 ^ proof.siblings.size then
    throw "MiMC proof index exceeds its depth"
  let mut current := leaf
  for level in [0:proof.siblings.size] do
    let side := proof.pathIndices[level]!
    let sibling := proof.siblings[level]!
    if side != (proof.index / 2 ^ level) % 2 then
      throw "MiMC proof direction differs from its index"
    if side == 0 then current ← mimcHashPairWith constants current sibling
    else if side == 1 then current ← mimcHashPairWith constants sibling current
    else throw "Invalid MiMC path direction"
  return current == proof.root

def verifyMimcProof (leaf : Nat) (proof : MimcProof) : Except String Bool :=
  verifyMimcProofWith mimcConstants leaf proof

end Tornado.Crypto
