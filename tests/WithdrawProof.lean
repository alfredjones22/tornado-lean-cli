import Tornado.Cli.WithdrawProof

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime
open Tornado.Cli.WithdrawProof

private def unwrap (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError s!"{label}: {message}"

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def word (value : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:32] do
    bytes := bytes.push ((value / 256 ^ (31 - i) % 256).toUInt8)
  return bytes

private def keyBytes : ByteArray := word
  0xa0030e1f064deb82242c2915d0ec910c23656641e72904c10055c5e395bad5bb

def main : IO UInt32 := do
  let started ← IO.monoMsNow
  let some pool := poolFor .mainnet "0.01" "ETH"
    | throw <| IO.userError "Missing public extended ETH fixture pool."
  let poolBytes ← unwrap "pool address" <| parseHexBytes pool.address
  let poolNat := poolBytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  let note ← unwrap "public unfunded note" <|
    tornadoSignatureNote keyBytes 1 0 poolNat
  let raw := s!"tornado-eth-0.01-1-0x{bytesToHex note.preimage}"
  let selected ← unwrap "select fixture note" <| Tornado.Cli.History.selectNote raw .mainnet none
  require (selected.publicIdentity.commitment == (← unwrap "commitment hex" <|
    toHex32 note.commitment) &&
    selected.publicIdentity.nullifierHash == (← unwrap "nullifier hex" <|
      toHex32 note.nullifierHash))
    "Protected-note public identity differs from the native signature fixture."
  let tree ← unwrap "one-leaf public tree" <| buildMimcTree #[note.commitment]
  let registered := 26198980
  let prior ← unwrap "fresh pool state" <|
    HistoryReducer.emptyState 1 poolNat registered
  let state : HistoryReducer.State := { prior with
    lastSyncedBlock := registered, finalizedBlock := some registered,
    verifiedRoot := some tree.root,
    deposits := #[⟨word note.commitment, 0, 0, registered, 0, true⟩] }
  let history : HistorySync.Result := ⟨state, registered, none, 0⟩
  let assets ← loadAssets "."
  require (!(buildWith assets selected history true .direct 1 0 1 2).isOk &&
    !(buildWith assets selected history false .direct 1 1 1 2).isOk &&
    !(buildWith assets selected history false (.classicRelayer 7) 1 1 1 2).isOk &&
    !(buildWith assets selected
      { history with state := { state with verifiedRoot := some (tree.root + 1) } }
      false .direct 1 0 1 2).isOk)
    "Spent, wrong-fee, unsupported-relayer, or wrong-root request was accepted."
  let result ← unwrap "native public proof-to-call" <|
    buildWith assets selected history false .direct 1 0 1 2
  let fixture ← unwrap "public SDK proof fixture" <|
    Json.parse (← IO.FS.readFile "fixtures/groth16-full-public-proof.json")
  let expectedProof ← unwrap "public SDK proof bytes" <|
    (← unwrap "fixture proof field" <| fixture.getObjVal? "solidityProofHex").getStr?
  let selector := Abi.selector
    "withdraw(bytes,bytes32,bytes32,address,address,uint256,uint256)"
  require (result.chainId == 1 && result.pool == poolNat &&
    result.recipient == 1 && result.relayer == 0 && result.fee == 0 &&
    result.root == tree.root && result.historyHead == registered &&
    result.nullifierHash == word note.nullifierHash &&
    result.proof.size == 256 &&
    "0x" ++ bytesToHex result.proof == expectedProof &&
    result.data.size == 516 && result.data.extract 0 4 == selector &&
    result.data.extract 4 36 == word 224 &&
    result.data.extract 36 68 == word tree.root &&
    result.data.extract 68 100 == word note.nullifierHash &&
    result.data.extract 100 132 == word 1 &&
    result.data.extract 228 260 == word 256 &&
    result.data.extract 260 516 == result.proof)
    "Public proof bytes or Classic withdrawal ABI binding differ from SDK fixture."
  let finished ← IO.monoMsNow
  IO.println s!"PASS: selected public note, checked history, exact SDK proof, and direct Classic calldata ({finished - started} ms)"
  return 0
