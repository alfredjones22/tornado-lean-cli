# Native domain parity checks

Run from this repository root after `lake build`:

```sh
lake env lean --run tests/PlanGrid.lean
lake env lean --run tests/PlanChoices.lean
lake env lean --run tests/NotesParsing.lean
lake env lean --run tests/StatusRules.lean
lake env lean --run tests/StatusParity.lean
```

`PlanGrid.lean` checks all 1,860 cells in `fixtures/plan-grid.csv`: 31 restricted mainnet ETH catalogs multiplied by amounts 0.01–0.60 ETH. It compares the exact ordered denomination/count result or rejection. Every accepted plan must pass the independent native accounting validator, and a changed note count must fail it. The fixture was generated from clean `tornado-cli-new-era` commit `daaa0c18de91ecc2effbdaea8d0bea7c856ff7f7`, `src/domain/denomination-plan.ts` SHA-256 `7b5c7757984915b08933bbb4478ed508fe5b64d60153ff1026180efd05ef25b7`, with SDK `0.1.0-alpha.38`. The test requires every mask/amount pair exactly once. This is a differential test of finite inputs, not an all-input equivalence proof or an independent proof that TypeScript chooses the optimal plan.

`PlanChoices.lean` compares the exact ordered lists of alternate plans for 900 pinned inputs across seven chain/asset catalogs (`ETH` on both chains, mainnet `DAI`, `USDC`, `USDT`, `WBTC`, and Sepolia `DAI`). Its oracle is `fixtures/plan-choices.csv`, generated from the same clean source commit and SDK pin. These cases cover plan ordering and alternative exclusions that the restricted minimum-count grid does not.

`NotesParsing.lean` checks 11 public zero-entropy raw note vectors plus malformed note, wrong-chain, duplicate-nullifier, and backup-extraction cases. `fixtures/seeded-note-vectors.json` is byte-identical to the TypeScript CLI's `tests/domain/fixtures/seeded-deposits.json` (SHA-256 `815bd5608744846f0723cf35872ae28badc16a9971f3828dfc681f30526f1135`). It also recomputes each commitment and nullifier hash through the native Lean Pedersen implementation. It does **not** verify seed derivation or proof material, and the vectors do not constitute a cryptographic-security proof.

`StatusRules.lean` exercises pure one-note status JSON decoding, signed-candidate no-replacement, the legacy rejected exception, malformed hash/candidate rejection, and candidate aggregation priority. `Tornado/Domain/Status.lean` contains a theorem that signed candidates block replacement and a theorem that a confirmed candidate wins aggregation. These rules operate on parsed values; they do not establish file permission, lock, rename, power-loss durability, bundler behavior, or chain confirmation.

`StatusParity.lean` checks acceptance or rejection of 38 synthetic status JSON records against the TypeScript CLI's `readWithdrawalStatus` at source commit `daaa0c18de91ecc2effbdaea8d0bea7c856ff7f7`. The pinned fixture `fixtures/status-parity.json` covers valid pending, failed, unknown and confirmed candidates plus malformed status versions, chains, operation hashes, sender/nonce/block fields, candidate types, and candidate cross-field mismatches. It compares schema acceptance only, not the saved-file lifecycle, exact error messages, or on-chain state.
