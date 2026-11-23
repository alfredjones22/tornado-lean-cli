import Tornado.Cli.History
import Tornado.Protocol.ClassicProofPipeline
import Tornado.Protocol.SelectedPoolBootstrap
import Tornado.Runtime.HistorySync
import Tornado.Runtime.ProofBlinding

/-!
One-note proof-to-call composition. The native prover has variable-time
big-integer arithmetic and does not zeroize note secrets. Secret lifetime and
process isolation are obligations of the caller.
-/

namespace Tornado.Cli.WithdrawProof

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime

inductive Route where
  | direct
  | paymaster
  | classicRelayer (rewardAccount : Nat)
  deriving Repr, Inhabited, BEq

/-- Only public withdrawal data leave the builder. The proof bytes and
    calldata are inherently public once submitted; the note is not retained. -/
structure Call where
  chainId : Nat
  pool : Nat
  recipient : Nat
  relayer : Nat
  fee : Nat
  root : Nat
  nullifierHash : ByteArray
  proof : ByteArray
  data : ByteArray
  historyHead : Nat
  deriving Inhabited

private def wordNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def exactAddress (raw : String) : Except String Nat := do
  if !raw.startsWith "0x" then throw "Pool or paymaster address lacks 0x prefix."
  let bytes ← parseHexBytes raw
  if bytes.size != 20 then throw "Pool or paymaster address is not 20 bytes."
  return wordNat bytes

private def exactWord (raw : String) : Except String ByteArray := do
  if !raw.startsWith "0x" then throw "Note identity lacks 0x prefix."
  let bytes ← parseHexBytes raw
  if bytes.size != 32 then throw "Note identity is not bytes32."
  return bytes

private def paymasterAddress : ChainId → Nat
  | .mainnet => 0xb0ffcdc890e969579d348f519a9c3920c2dd04a5
  | .sepolia => 0x835ce2da8ad0d1f5d5a8462a58594006514c39b0

private def routeFields (pool : Pool) (route : Route) (fee : Nat) :
    Except String Nat := do
  match route with
  | .direct =>
    if fee != 0 then throw "A direct pool call has no relayer fee."
    return 0
  | .paymaster =>
    if fee >= pool.amount then throw "Paymaster fee consumes the selected note."
    return paymasterAddress pool.chainId
  | .classicRelayer rewardAccount =>
    if !supportsClassicRelayer pool then
      throw "Classic relayers only support original Tornado pools."
    if rewardAccount == 0 || rewardAccount >= 2 ^ 160 ||
        fee == 0 || fee >= pool.amount || fee * 5 > pool.amount then
      throw "Classic relayer account or fee is outside the reviewed limit."
    return rewardAccount

private def selectedSignatureNote (selected : BackupIdentity) :
    Except String TornadoSignatureNote := do
  let bytes ← parseHexBytes selected.note.preimage
  if bytes.size != 62 then throw "Selected Classic note is not 62 bytes."
  let commitmentBytes ← exactWord selected.publicIdentity.commitment
  let nullifierHashBytes ← exactWord selected.publicIdentity.nullifierHash
  return { nullifierBytes := bytes.extract 0 31,
           secretBytes := bytes.extract 31 62,
           commitment := wordNat commitmentBytes,
           nullifierHash := wordNat nullifierHashBytes }

/-- Strictly bind a complete selected-pool history result to the note before
    using its Merkle root. The same-block `isSpent` claim is an independent
    input: callers must read it from the selected RPC at `capturedHead`. -/
private def selectedPath (selected : BackupIdentity)
    (history : HistorySync.Result) (spentAtHead : Bool) :
    Except String (TornadoSignatureNote × MimcProof × Nat × Nat) := do
  let state := history.state
  HistoryReducer.validateState state
  let pool ← exactAddress selected.note.pool.address
  if !(allPools.any (fun known => known == selected.note.pool)) ||
      state.chainId != chainNumber selected.note.pool.chainId ||
      state.pool != pool || state.lastSyncedBlock != history.capturedHead ||
      state.lastSyncedBlock < state.registeredBlock || spentAtHead then
    throw "Selected note, pool history, or same-block spent status disagrees."
  let some verifiedRoot := state.verifiedRoot
    | throw "Selected pool history has no same-block verified root."
  let note ← selectedSignatureNote selected
  let commitment ← exactWord selected.publicIdentity.commitment
  let nullifierHash ← exactWord selected.publicIdentity.nullifierHash
  if state.withdrawals.any (fun item => item.nullifierHash == nullifierHash) then
    throw "Selected note has a withdrawal in complete pool history."
  let found := state.deposits.filter (fun item => item.commitment == commitment)
  if found.size != 1 then
    throw "Selected note has no unique deposit in complete pool history."
  let record := found[0]!
  let tree ← buildMimcTree (state.deposits.map (fun item => wordNat item.commitment))
  if tree.root != verifiedRoot || record.leafIndex >= state.deposits.size ||
      (state.deposits[record.leafIndex]!).commitment != commitment then
    throw "Selected note Merkle tree differs from the same-block pool root."
  let proof ← mimcProofAt tree record.leafIndex
  if proof.root != verifiedRoot then
    throw "Selected note Merkle path differs from the same-block pool root."
  return (note, proof, verifiedRoot, pool)

/-- Public-fixture entry with explicit canonical blinding scalars. This is
    deterministic only for tests; callers must not use fixed scalars for
    funded notes. -/
def buildWith (assets : ClassicProofPipeline.PinnedAssets)
    (selected : BackupIdentity) (history : HistorySync.Result)
    (spentAtHead : Bool) (route : Route) (recipient fee r s : Nat) :
    Except String Call := do
  if recipient == 0 || recipient >= 2 ^ 160 then
    throw "Withdrawal recipient is not a nonzero Ethereum address."
  let relayer ← routeFields selected.note.pool route fee
  let (note, path, root, pool) ← selectedPath selected history spentAtHead
  let withdrawal : TornadoWitness.WithdrawalInput := {
    note, proof := path, expectedRoot := root,
    recipient, relayer, fee, refund := 0 }
  let _ ← TornadoWitness.prepareInputPrefix withdrawal
  let proof ← ClassicProofPipeline.prove assets withdrawal r s
  let rootBytes ← Abi.uintWord root
  let nullifierBytes ← Abi.uintWord note.nullifierHash
  if proof.bytes.size != 256 || proof.signals !=
      #[root, note.nullifierHash, recipient, relayer, fee, 0] then
    throw "Native proof differs from reviewed Classic withdrawal inputs."
  let data ← Abi.poolWithdraw proof.bytes rootBytes nullifierBytes
    recipient relayer fee 0
  return ⟨chainNumber selected.note.pool.chainId, pool, recipient, relayer,
    fee, root, nullifierBytes, proof.bytes, data, history.capturedHead⟩

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

/-- Fresh unbiased Fr blinding from separate kernel CSPRNG reads. This does
    not make the variable-time prover safe for live secret notes. -/
def buildFresh (assets : ClassicProofPipeline.PinnedAssets)
    (selected : BackupIdentity) (history : HistorySync.Result)
    (spentAtHead : Bool) (route : Route) (recipient fee : Nat) : IO Call := do
  let (r, s) ← ProofBlinding.samplePair
  checked <| buildWith assets selected history spentAtHead route recipient fee
    r.value s.value

private def absolutePath (path : String) : IO String := do
  let current ← IO.currentDir
  return if (System.FilePath.mk path).isAbsolute then path
    else (current / path).toString

/-- Protected selection from a private note backup; no note text is included
    in error messages or returned public Call data. -/
def readSelected (noteFile : String) (chain : ChainId)
    (noteIndex : Option String) : IO BackupIdentity := do
  let bytes ← ProtectedIO.readPrivate (← absolutePath noteFile)
  let some raw := String.fromUTF8? bytes
    | throw <| IO.userError "Private note backup is not UTF-8."
  checked <| Tornado.Cli.History.selectNote raw chain noteIndex

/-- Authenticate only the exact bundled Classic proving artifacts. -/
def loadAssets (root : String) : IO ClassicProofPipeline.PinnedAssets := do
  let base ← absolutePath root
  let circuit ← IO.FS.readBinFile
    (base ++ "/assets/proving/tornado-3ddd61dbff09caee.json.gz")
  let key ← IO.FS.readBinFile
    (base ++ "/assets/proving/tornadoProvingKey-8e2d2f22beafb5a9.bin.gz")
  let graph ← IO.FS.readFile (base ++ "/fixtures/witness-vm-selected-components.json")
  checked <| ClassicProofPipeline.loadBundled circuit key graph

private def quantityHex (value : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 value)

private def addressHex (address : Nat) : String := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:20] do
    bytes := bytes.push ((address / 256 ^ (19 - i) % 256).toUInt8)
  return "0x" ++ bytesToHex bytes

private def rpcWord (value : Json) : Except String Nat := do
  let raw ← value.getStr?
  if !raw.startsWith "0x" then throw "Selected-pool RPC word lacks 0x prefix."
  let bytes ← parseHexBytes raw
  if bytes.size != 32 then throw "Selected-pool RPC word is not uint256."
  return wordNat bytes

/-- Recheck the selected chain, root, leaf count, and `isSpent(bytes32)` at
    the captured head after history sync. RPC failures are sanitized so an
    endpoint echo cannot leak the nullifier in an error message. -/
def liveSpentClaim (rpcUrl : String) (history : HistorySync.Result)
    (nullifierHash : ByteArray) : IO Bool := do
  let state := history.state
  if nullifierHash.size != 32 || state.lastSyncedBlock != history.capturedHead then
    throw <| IO.userError "Invalid selected history or nullifier hash."
  let chain ← try
    checked <| JsonRpc.parseHexQuantity (← checked <|
      (← HttpTransport.call rpcUrl 9001 .chainId #[]).getStr?)
    catch _ => throw <| IO.userError "Selected-pool chain recheck failed."
  if chain != state.chainId then
    throw <| IO.userError "Selected-pool RPC changed networks."
  let target := addressHex state.pool
  let block := quantityHex history.capturedHead
  let callWord (signature : String) (tail : ByteArray) (id : Nat) : IO Nat := do
    let data := "0x" ++ bytesToHex (Abi.selector signature ++ tail)
    let result ← try
      HttpTransport.call rpcUrl id .call
        #[Json.mkObj [("to", toJson target), ("data", toJson data)], toJson block]
      catch _ => throw <| IO.userError "Selected-pool exact-block claim failed."
    checked <| rpcWord result
  let root ← callWord "getLastRoot()" ByteArray.empty 9002
  let count ← callWord "nextIndex()" ByteArray.empty 9003
  if state.verifiedRoot != some root || state.deposits.size != count then
    throw <| IO.userError "Selected-pool root or leaf count changed after sync."
  let spent ← callWord "isSpent(bytes32)" nullifierHash 9004
  if spent > 1 then throw <| IO.userError "Selected-pool spent claim is not boolean."
  return spent == 1

/-- Protected-note helper using fresh history and authenticated proving assets
    to construct public ABI calldata. It does not sign, journal or submit. -/
def buildLiveInternal (noteFile : String) (noteIndex : Option String)
    (chain : ChainId) (rpcUrl assetRoot : String) (route : Route)
    (recipient fee : Nat) : IO Call := do
  let selected ← readSelected noteFile chain noteIndex
  let pool ← checked <| exactAddress selected.note.pool.address
  let prior ← checked <| SelectedPoolBootstrap.freshState (chainNumber chain) pool
  let history ← HistorySync.syncSelectedPoolLive prior rpcUrl
  let nullifierHash ← checked <| exactWord selected.publicIdentity.nullifierHash
  let spent ← liveSpentClaim rpcUrl history nullifierHash
  let assets ← loadAssets assetRoot
  buildFresh assets selected history spent route recipient fee

end Tornado.Cli.WithdrawProof
