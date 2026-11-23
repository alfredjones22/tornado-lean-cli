import Tornado.Domain.Amount

/-!
Captured catalog from tornado-cli-new-era at
daaa0c18de91ecc2effbdaea8d0bea7c856ff7f7, using
@kohaku-eth/tornado-cash@0.1.0-alpha.38. These public constants are
native Lean data at runtime. Regeneration requires reviewing SDK catalog drift.
-/

namespace Tornado.Domain

inductive ChainId where
  | mainnet
  | sepolia
  deriving Repr, BEq, DecidableEq, Inhabited

def chainNumber : ChainId → Nat
  | .mainnet => 1
  | .sepolia => 11155111

def chainFromNat : Nat → Option ChainId
  | 1 => some .mainnet
  | 11155111 => some .sepolia
  | _ => none

def chainName : ChainId → String
  | .mainnet => "Ethereum"
  | .sepolia => "Sepolia"

def defaultRpc : ChainId → String
  | .mainnet => "https://ethereum.publicnode.com"
  | .sepolia => "https://0xrpc.io/sep"

def explorer : ChainId → String
  | .mainnet => "https://etherscan.io"
  | .sepolia => "https://sepolia.etherscan.io"

structure Asset where
  symbol : String
  decimals : Nat
  token : Option String
  deriving Repr, BEq, Inhabited

structure Pool where
  chainId : ChainId
  denomination : String
  amount : Nat
  address : String
  asset : Asset
  classicRelayer : Bool
  deriving Repr, BEq, Inhabited

structure DepositSelection where
  denomination : String
  count : Nat
  deriving Repr, BEq, Inhabited

structure DepositCartRow where
  pool : Pool
  count : Nat
  total : Nat
  deriving Repr, BEq, Inhabited

/-! The 29 supported pools are in the TypeScript poolsFor order. -/
def allPools : List Pool := [
  { chainId := .mainnet, denomination := "0.1", amount := 10000000,
    address := "0x178169B423a011fff22B9e3F3abeA13414dDD0F1", asset := ⟨"WBTC", 8, some "0x2260FAC5E5542a773Aa44fBCfeDf7C193bc2C599"⟩, classicRelayer := true },
  { chainId := .mainnet, denomination := "100", amount := 100000000,
    address := "0xd96f2B1c14Db8458374d9Aca76E26c3D18364307", asset := ⟨"USDC", 6, some "0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48"⟩, classicRelayer := true },
  { chainId := .mainnet, denomination := "100", amount := 100000000,
    address := "0x169AD27A470D064DEDE56a2D3ff727986b15D52B", asset := ⟨"USDT", 6, some "0xdAC17F958D2ee523a2206206994597C13D831ec7"⟩, classicRelayer := true },
  { chainId := .mainnet, denomination := "1", amount := 100000000,
    address := "0x610B717796ad172B316836AC95a2ffad065CeaB4", asset := ⟨"WBTC", 8, some "0x2260FAC5E5542a773Aa44fBCfeDf7C193bc2C599"⟩, classicRelayer := true },
  { chainId := .mainnet, denomination := "1000", amount := 1000000000,
    address := "0x4736dCf1b7A3d580672CcE6E7c65cd5cc9cFBa9D", asset := ⟨"USDC", 6, some "0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48"⟩, classicRelayer := true },
  { chainId := .mainnet, denomination := "1000", amount := 1000000000,
    address := "0x0836222F2B2B24A3F36f98668Ed8F0B38D1a872f", asset := ⟨"USDT", 6, some "0xdAC17F958D2ee523a2206206994597C13D831ec7"⟩, classicRelayer := true },
  { chainId := .mainnet, denomination := "10", amount := 1000000000,
    address := "0xbB93e510BbCD0B7beb5A853875f9eC60275CF498", asset := ⟨"WBTC", 8, some "0x2260FAC5E5542a773Aa44fBCfeDf7C193bc2C599"⟩, classicRelayer := true },
  { chainId := .mainnet, denomination := "0.01", amount := 10000000000000000,
    address := "0x199112Eb461ea7eeC1D75B33343542e1d069B41c", asset := ⟨"ETH", 18, none⟩, classicRelayer := false },
  { chainId := .mainnet, denomination := "0.03", amount := 30000000000000000,
    address := "0x398971a7Ae0FeD4ae435F353eF00D3d4e4c18fD4", asset := ⟨"ETH", 18, none⟩, classicRelayer := false },
  { chainId := .mainnet, denomination := "0.1", amount := 100000000000000000,
    address := "0x12D66f87A04A9E220743712cE6d9bB1B5616B8Fc", asset := ⟨"ETH", 18, none⟩, classicRelayer := true },
  { chainId := .mainnet, denomination := "0.3", amount := 300000000000000000,
    address := "0xf22487b84A618192aa68C0E1da24e9Bbd892f774", asset := ⟨"ETH", 18, none⟩, classicRelayer := false },
  { chainId := .mainnet, denomination := "1", amount := 1000000000000000000,
    address := "0x47CE0C6eD5B0Ce3d3A51fdb1C52DC66a7c3c2936", asset := ⟨"ETH", 18, none⟩, classicRelayer := true },
  { chainId := .mainnet, denomination := "3", amount := 3000000000000000000,
    address := "0x74185A3f30b873c0ce1F4257298D1CdA61be2f9f", asset := ⟨"ETH", 18, none⟩, classicRelayer := false },
  { chainId := .mainnet, denomination := "10", amount := 10000000000000000000,
    address := "0x910Cbd523D972eb0a6f4cAe4618aD62622b39DbF", asset := ⟨"ETH", 18, none⟩, classicRelayer := true },
  { chainId := .mainnet, denomination := "30", amount := 30000000000000000000,
    address := "0xC11197f71C7730C8B5dB7C84191E07575F1DB896", asset := ⟨"ETH", 18, none⟩, classicRelayer := false },
  { chainId := .mainnet, denomination := "100", amount := 100000000000000000000,
    address := "0xA160cdAB225685dA1d56aa342Ad8841c3b53f291", asset := ⟨"ETH", 18, none⟩, classicRelayer := true },
  { chainId := .mainnet, denomination := "100", amount := 100000000000000000000,
    address := "0xD4B88Df4D29F5CedD6857912842cff3b20C8Cfa3", asset := ⟨"DAI", 18, some "0x6B175474E89094C44Da98b954EedeAC495271d0F"⟩, classicRelayer := true },
  { chainId := .mainnet, denomination := "1000", amount := 1000000000000000000000,
    address := "0xFD8610d20aA15b7B2E3Be39B396a1bC3516c7144", asset := ⟨"DAI", 18, some "0x6B175474E89094C44Da98b954EedeAC495271d0F"⟩, classicRelayer := true },
  { chainId := .mainnet, denomination := "10000", amount := 10000000000000000000000,
    address := "0x07687e702b410Fa43f4cB4Af7FA097918ffD2730", asset := ⟨"DAI", 18, some "0x6B175474E89094C44Da98b954EedeAC495271d0F"⟩, classicRelayer := true },
  { chainId := .mainnet, denomination := "100000", amount := 100000000000000000000000,
    address := "0x23773E65ed146A459791799d01336DB287f25334", asset := ⟨"DAI", 18, some "0x6B175474E89094C44Da98b954EedeAC495271d0F"⟩, classicRelayer := true },
  { chainId := .sepolia, denomination := "0.01", amount := 10000000000000000,
    address := "0x0E999C5285141ccB6dFaE68A0921F37ABd3e6A87", asset := ⟨"ETH", 18, none⟩, classicRelayer := false },
  { chainId := .sepolia, denomination := "0.03", amount := 30000000000000000,
    address := "0x9480Be3964642efcD6CeBdb3570db8dC0f788908", asset := ⟨"ETH", 18, none⟩, classicRelayer := false },
  { chainId := .sepolia, denomination := "0.1", amount := 100000000000000000,
    address := "0x8C4A04d872a6C1BE37964A21ba3a138525dFF50b", asset := ⟨"ETH", 18, none⟩, classicRelayer := true },
  { chainId := .sepolia, denomination := "0.3", amount := 300000000000000000,
    address := "0x83091415b54d764E215153Ff54B36cCd44122e6e", asset := ⟨"ETH", 18, none⟩, classicRelayer := false },
  { chainId := .sepolia, denomination := "1", amount := 1000000000000000000,
    address := "0x8cc930096B4Df705A007c4A039BDFA1320Ed2508", asset := ⟨"ETH", 18, none⟩, classicRelayer := true },
  { chainId := .sepolia, denomination := "3", amount := 3000000000000000000,
    address := "0x7eE90edc51c3739Af3ee277e09ADE3F3d6bad4AF", asset := ⟨"ETH", 18, none⟩, classicRelayer := false },
  { chainId := .sepolia, denomination := "10", amount := 10000000000000000000,
    address := "0x8D10d506D29Fc62ABb8A290B99F66dB27Fc43585", asset := ⟨"ETH", 18, none⟩, classicRelayer := false },
  { chainId := .sepolia, denomination := "30", amount := 30000000000000000000,
    address := "0x3d1C943dfb2C8d9905B0Da0AFD18615915fF343A", asset := ⟨"ETH", 18, none⟩, classicRelayer := false },
  { chainId := .sepolia, denomination := "100", amount := 100000000000000000000,
    address := "0x6921fd1a97441dd603a997ED6DDF388658daf754", asset := ⟨"DAI", 18, some "0xFF34B3d4Aee8ddCd6F9AFFFB6Fe49bD371b8a357"⟩, classicRelayer := true }
]

def poolsFor (chainId : ChainId) (symbol : Option String := none) : List Pool :=
  allPools.filter fun pool =>
    pool.chainId == chainId && (symbol.map (fun s => s.isEmpty || s.toLower == pool.asset.symbol.toLower)).getD true

def poolFor (chainId : ChainId) (denomination : String) (symbol : String := "ETH") : Option Pool :=
  (poolsFor chainId (some symbol)).find? (fun pool => pool.denomination == denomination)

def assetsFor (chainId : ChainId) : List Asset :=
  ["ETH", "DAI", "USDC", "USDT", "WBTC"].filterMap fun symbol =>
    ((poolsFor chainId).find? (fun pool => pool.asset.symbol == symbol)).map (·.asset)

def supportsClassicRelayer (pool : Pool) : Bool :=
  match poolFor pool.chainId pool.denomination pool.asset.symbol with
  | none => false
  | some known => known.address.toLower == pool.address.toLower && known.classicRelayer

def depositBatchLimit (asset : Asset) : Nat :=
  if asset.token.isSome then 5 else 12

def totalValue (pools : List Pool) : Nat :=
  pools.foldl (fun sum pool => sum + pool.amount) 0

private def jsMaxSafe : Nat := 9007199254740991

def depositCart (chainId : ChainId) (selections : List DepositSelection)
    (symbol : String := "ETH") : Except String (List DepositCartRow) := do
  let mut rows : List DepositCartRow := []
  let mut quantity : Nat := 0
  for selection in selections do
    if selection.count > jsMaxSafe || quantity + selection.count > jsMaxSafe then
      throw "Invalid note quantity."
    if selection.count > 0 then
      let some pool := poolFor chainId selection.denomination symbol
        | throw s!"{selection.denomination} {symbol} is unavailable on {chainName chainId}."
      quantity := quantity + selection.count
      rows := rows ++ [{ pool, count := selection.count, total := pool.amount * selection.count }]
  if rows.isEmpty then throw "Select at least one note."
  return rows

def expandSelection (chainId : ChainId) (selections : List DepositSelection)
    (symbol : String := "ETH") : Except String (List Pool) := do
  let rows ← depositCart chainId selections symbol
  return rows.flatMap (fun row => List.replicate row.count row.pool)

end Tornado.Domain

