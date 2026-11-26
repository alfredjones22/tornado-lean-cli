# Native domain regression checks

Run from this repository root after `lake build`:

```sh
lake env lean --run tests/PlanGrid.lean
lake env lean --run tests/PlanChoices.lean
lake env lean --run tests/NotesParsing.lean
lake env lean --run tests/StatusRules.lean
lake env lean --run tests/StatusParity.lean
```

`PlanGrid.lean` checks all 1,860 cells in [`fixtures/plan-grid.csv`](../fixtures/plan-grid.csv): 31 restricted mainnet ETH catalogs multiplied by amounts 0.01–0.60 ETH. It compares the exact ordered denomination/count result or rejection. Every accepted plan must pass the independent native accounting validator, and a changed note count must fail it. The fixture header records its independent reference source identity; the recorded planner source SHA-256 is `7b5c7757984915b08933bbb4478ed508fe5b64d60153ff1026180efd05ef25b7`. The test requires every mask/amount pair exactly once. These finite cases do not prove optimality or correctness for every CLI input.

`PlanChoices.lean` compares the exact ordered lists of alternate plans for 900 pinned inputs across seven chain/asset catalogs (`ETH` on both chains, mainnet `DAI`, `USDC`, `USDT`, `WBTC`, and Sepolia `DAI`). Its independent fixture is [`fixtures/plan-choices.csv`](../fixtures/plan-choices.csv), whose header retains the exact reference source identity. These cases cover plan ordering and alternative exclusions that the restricted minimum-count grid does not.

`NotesParsing.lean` checks 11 public zero-entropy raw note vectors plus malformed note, wrong-chain, duplicate-nullifier, and backup-extraction cases. The pinned [`fixtures/seeded-note-vectors.json`](../fixtures/seeded-note-vectors.json) records the public fixture's source and has SHA-256 `815bd5608744846f0723cf35872ae28badc16a9971f3828dfc681f30526f1135`. It also recomputes each commitment and nullifier hash through the native Lean Pedersen implementation. It does **not** verify seed derivation or proof material, and the vectors do not constitute a cryptographic-security proof.

`StatusRules.lean` exercises pure one-note status JSON decoding, signed-candidate no-replacement, the legacy rejected exception, malformed hash/candidate rejection, and candidate aggregation priority. `Tornado/Domain/Status.lean` contains a theorem that signed candidates block replacement and a theorem that a confirmed candidate wins aggregation. These rules operate on parsed values; they do not establish file permission, lock, rename, power-loss durability, bundler behavior, or chain confirmation.

`StatusParity.lean` checks expected acceptance or rejection of 38 synthetic status JSON records. The pinned [`fixtures/status-parity.json`](../fixtures/status-parity.json) retains its independent source identity and covers valid pending, failed, unknown and confirmed candidates plus malformed status versions, chains, operation hashes, sender/nonce/block fields, candidate types, and candidate cross-field mismatches. It checks schema acceptance only, not the saved-file lifecycle, exact error messages, or on-chain state.
