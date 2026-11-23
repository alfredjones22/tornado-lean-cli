import Tornado.Protocol.SelectedPoolBootstrap

open Tornado.Domain Tornado.Protocol.SelectedPoolBootstrap

private def unwrap (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError s!"{label}: {message}"

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def expectError (label : String) (value : Except String α) : IO Unit :=
  match value with
  | .ok _ => throw <| IO.userError s!"{label}: unexpectedly accepted"
  | .error _ => pure ()

/-- Finite integration check for every source-pinned catalog pool. -/
def main : IO UInt32 := do
  require (rows.length == 29 && allPools.length == 29)
    "Selected-pool bootstrap/catalog row count drifted."
  let mut identities : Array (Nat × Nat) := #[]
  for pool in allPools do
    let chainId := chainNumber pool.chainId
    let row ← unwrap "supported catalog pool" <| selected chainId pool
    let identity := (chainId, row.address)
    require (!identities.contains identity)
      "Selected-pool bootstrap repeats a chain/address identity."
    identities := identities.push identity
    let numeric ← unwrap "numeric selected-pool lookup" <|
      byIdentity chainId row.address
    require (numeric == row && row.registeredBlock == row.manifestFromBlock &&
      row.amount == pool.amount && row.registeredBlock > 0)
      "Selected-pool bootstrap differs from catalog or manifest."
    let state ← unwrap "fresh selected-pool state" <|
      freshState chainId row.address
    require (state.chainId == chainId && state.pool == row.address &&
      state.registeredBlock == row.registeredBlock &&
      state.lastSyncedBlock + 1 == row.registeredBlock &&
      state.deposits.isEmpty && state.withdrawals.isEmpty)
      "Fresh selected-pool cursor or identity is wrong."
  let pool := allPools.head!
  let row ← unwrap "first known pool" <| selected (chainNumber pool.chainId) pool
  expectError "wrong selected chain" <| selected 11155111 pool
  expectError "spoofed catalog amount" <| selected 1 { pool with amount := pool.amount + 1 }
  expectError "unsupported pool address" <| byIdentity 1 0x1234
  expectError "unsupported chain" <| byIdentity 10 row.address
  expectError "wrong-chain numeric lookup" <| byIdentity 11155111 row.address
  expectError "zero address" <| freshState 1 0
  expectError "oversized address" <| freshState 1 (2 ^ 160)
  IO.println "PASS: all 29 selected-pool bootstrap identities, deployment cursors, and mismatch rejections"
  return 0
