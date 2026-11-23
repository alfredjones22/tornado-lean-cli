import Tornado.Domain.Catalog
import Tornado.Domain.NoteIdentity
import Tornado.Protocol.HistoryReducer

/-!
Native selected-pool bootstrap captured from the clean TypeScript CLI at
daaa0c18de91ecc2effbdaea8d0bea7c856ff7f7. The 29 rows below are the
intersection of its supported catalog, `history-bootstrap.json`, and
`history-manifest.json`; scripts/check_selected_pool_bootstrap.py rechecks
the exact source SHA-256 digests and every field. This is public data only.
No runtime Node, JSON, snapshot, or network dependency is involved.
-/

namespace Tornado.Protocol.SelectedPoolBootstrap

open Tornado.Domain

def bootstrapSourceSHA256 : String :=
  "d294f0d137f9e168fd9508ab217a848340084e8e505fca0b7dd0b7473d30fa7a"
def manifestSourceSHA256 : String :=
  "2b3e848d8db92ed48d270083dec8800928a26ef684b5309345e273b2d4d6e8f1"
def catalogSourceSHA256 : String :=
  "5f51168fef9e4b575fd5cd1a61bec3644433f01868226327ce8de408f4a4e718"

structure Row where
  chain : ChainId
  address : Nat
  registeredBlock : Nat
  manifestFromBlock : Nat
  amount : Nat
  asset : Nat
  deriving Repr, BEq, Inhabited

def rows : List Row := [
  ⟨.mainnet, 0x178169b423a011fff22b9e3f3abea13414ddd0f1, 12067529, 12067529, 10000000, 0x2260fac5e5542a773aa44fbcfedf7c193bc2c599⟩,
  ⟨.mainnet, 0xd96f2b1c14db8458374d9aca76e26c3d18364307, 9161958, 9161958, 100000000, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48⟩,
  ⟨.mainnet, 0x169ad27a470d064dede56a2d3ff727986b15d52b, 9162005, 9162005, 100000000, 0xdac17f958d2ee523a2206206994597c13d831ec7⟩,
  ⟨.mainnet, 0x610b717796ad172b316836ac95a2ffad065ceab4, 12066652, 12066652, 100000000, 0x2260fac5e5542a773aa44fbcfedf7c193bc2c599⟩,
  ⟨.mainnet, 0x4736dcf1b7a3d580672cce6e7c65cd5cc9cfba9d, 9161965, 9161965, 1000000000, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48⟩,
  ⟨.mainnet, 0x836222f2b2b24a3f36f98668ed8f0b38d1a872f, 9162012, 9162012, 1000000000, 0xdac17f958d2ee523a2206206994597c13d831ec7⟩,
  ⟨.mainnet, 0xbb93e510bbcd0b7beb5a853875f9ec60275cf498, 12067591, 12067591, 1000000000, 0x2260fac5e5542a773aa44fbcfedf7c193bc2c599⟩,
  ⟨.mainnet, 0x199112eb461ea7eec1d75b33343542e1d069b41c, 26198980, 26198980, 10000000000000000, 0x0⟩,
  ⟨.mainnet, 0x398971a7ae0fed4ae435f353ef00d3d4e4c18fd4, 26198980, 26198980, 30000000000000000, 0x0⟩,
  ⟨.mainnet, 0x12d66f87a04a9e220743712ce6d9bb1b5616b8fc, 9116966, 9116966, 100000000000000000, 0x0⟩,
  ⟨.mainnet, 0xf22487b84a618192aa68c0e1da24e9bbd892f774, 26198980, 26198980, 300000000000000000, 0x0⟩,
  ⟨.mainnet, 0x47ce0c6ed5b0ce3d3a51fdb1c52dc66a7c3c2936, 9117609, 9117609, 1000000000000000000, 0x0⟩,
  ⟨.mainnet, 0x74185a3f30b873c0ce1f4257298d1cda61be2f9f, 26198980, 26198980, 3000000000000000000, 0x0⟩,
  ⟨.mainnet, 0x910cbd523d972eb0a6f4cae4618ad62622b39dbf, 9117720, 9117720, 10000000000000000000, 0x0⟩,
  ⟨.mainnet, 0xc11197f71c7730c8b5db7c84191e07575f1db896, 26198983, 26198983, 30000000000000000000, 0x0⟩,
  ⟨.mainnet, 0xa160cdab225685da1d56aa342ad8841c3b53f291, 9161895, 9161895, 100000000000000000000, 0x0⟩,
  ⟨.mainnet, 0xd4b88df4d29f5cedd6857912842cff3b20c8cfa3, 9117612, 9117612, 100000000000000000000, 0x6b175474e89094c44da98b954eedeac495271d0f⟩,
  ⟨.mainnet, 0xfd8610d20aa15b7b2e3be39b396a1bc3516c7144, 9161917, 9161917, 1000000000000000000000, 0x6b175474e89094c44da98b954eedeac495271d0f⟩,
  ⟨.mainnet, 0x7687e702b410fa43f4cb4af7fa097918ffd2730, 12066007, 12066007, 10000000000000000000000, 0x6b175474e89094c44da98b954eedeac495271d0f⟩,
  ⟨.mainnet, 0x23773e65ed146a459791799d01336db287f25334, 12066048, 12066048, 100000000000000000000000, 0x6b175474e89094c44da98b954eedeac495271d0f⟩,
  ⟨.sepolia, 0xe999c5285141ccb6dfae68a0921f37abd3e6a87, 11949077, 11949077, 10000000000000000, 0x0⟩,
  ⟨.sepolia, 0x9480be3964642efcd6cebdb3570db8dc0f788908, 11949078, 11949078, 30000000000000000, 0x0⟩,
  ⟨.sepolia, 0x8c4a04d872a6c1be37964a21ba3a138525dff50b, 5594400, 5594400, 100000000000000000, 0x0⟩,
  ⟨.sepolia, 0x83091415b54d764e215153ff54b36ccd44122e6e, 11949080, 11949080, 300000000000000000, 0x0⟩,
  ⟨.sepolia, 0x8cc930096b4df705a007c4a039bdfa1320ed2508, 5594401, 5594401, 1000000000000000000, 0x0⟩,
  ⟨.sepolia, 0x7ee90edc51c3739af3ee277e09ade3f3d6bad4af, 11949081, 11949081, 3000000000000000000, 0x0⟩,
  ⟨.sepolia, 0x8d10d506d29fc62abb8a290b99f66db27fc43585, 5594402, 5594402, 10000000000000000000, 0x0⟩,
  ⟨.sepolia, 0x3d1c943dfb2c8d9905b0da0afd18615915ff343a, 11949082, 11949082, 30000000000000000000, 0x0⟩,
  ⟨.sepolia, 0x6921fd1a97441dd603a997ed6ddf388658daf754, 5594406, 5594406, 100000000000000000000, 0xff34b3d4aee8ddcd6f9afffb6fe49bd371b8a357⟩
]

private def addressNat (raw : String) : Except String Nat := do
  let bytes ← parseHexBytes raw
  if bytes.size != 20 then throw "Invalid catalog pool or token address."
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def tokenNat (pool : Pool) : Except String Nat :=
  match pool.asset.token with
  | none => .ok 0
  | some token => addressNat token

/-- Resolve only a byte-for-byte supported catalog pool on the supplied
    network, and cross-check the bootstrap and history manifest identities. -/
def selected (chainId : Nat) (pool : Pool) : Except String Row := do
  if chainId != chainNumber pool.chainId ||
      !(allPools.any (fun known => known == pool)) then
    throw "Selected pool is not in the pinned network catalog."
  let address ← addressNat pool.address
  let asset ← tokenNat pool
  let some row := rows.find? (fun row => row.chain == pool.chainId &&
      row.address == address)
    | throw "Selected pool has no pinned history bootstrap."
  if row.amount != pool.amount || row.asset != asset ||
      row.registeredBlock == 0 ||
      row.registeredBlock != row.manifestFromBlock then
    throw "Selected pool bootstrap disagrees with catalog or history manifest."
  return row

/-- RPC/Saga callers may identify a pool numerically; this still resolves
    through the pinned catalog, then performs the same bootstrap checks. -/
def byIdentity (chainId poolAddress : Nat) : Except String Row := do
  let some chain := chainFromNat chainId
    | throw "Unsupported pool network."
  if poolAddress == 0 || poolAddress >= 2 ^ 160 then
    throw "Invalid pool address."
  let some pool := allPools.find? (fun candidate =>
      candidate.chainId == chain &&
      (addressNat candidate.address).toOption == some poolAddress)
    | throw "Selected pool is not in the pinned network catalog."
  selected chainId pool

/-- Seed the selected-pool reducer at exactly one block before the first
    possible event. A missing or chain-mismatched pool fails closed. -/
def freshState (chainId poolAddress : Nat) : Except String HistoryReducer.State := do
  let row ← byIdentity chainId poolAddress
  HistoryReducer.emptyState chainId row.address row.registeredBlock

theorem rows_match_manifest :
    rows.all (fun row => row.registeredBlock == row.manifestFromBlock) = true := by
  decide

theorem rows_have_positive_start :
    rows.all (fun row => row.registeredBlock > 0) = true := by
  decide

theorem rows_count_matches_catalog : rows.length = allPools.length := by decide

theorem row_identities_unique :
    (rows.map fun row => (chainNumber row.chain, row.address)).Nodup := by decide

end Tornado.Protocol.SelectedPoolBootstrap

#print axioms Tornado.Protocol.SelectedPoolBootstrap.rows_match_manifest
#print axioms Tornado.Protocol.SelectedPoolBootstrap.rows_have_positive_start
#print axioms Tornado.Protocol.SelectedPoolBootstrap.rows_count_matches_catalog
#print axioms Tornado.Protocol.SelectedPoolBootstrap.row_identities_unique
