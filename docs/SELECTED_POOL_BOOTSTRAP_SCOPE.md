# Native selected-pool history bootstrap

[`SelectedPoolBootstrap.lean`](../Tornado/Protocol/SelectedPoolBootstrap.lean)
contains the 29 pools supported by the frozen CLI catalog. Each row captures
the chain, numeric pool address, denomination, token address, and the pool's
`registeredBlock` from `history-bootstrap.json` and `fromBlock` from
`history-manifest.json`. The two blocks agree for every supported pool. Four
additional pools in the mainnet bootstrap are outside the supported catalog
and are deliberately unavailable through this API.

`byIdentity` accepts a numeric chain and address, resolves them through the
pinned catalog, then checks the table's amount, token, and registration block.
`selected` also rejects a caller-supplied pool whose fields differ from the
catalog. `freshState` passes the checked registration block to
`HistoryReducer.emptyState`, which starts the cursor one block earlier. Missing
pools, wrong chains, zero and oversized addresses, and altered catalog fields
fail closed. Runtime lookup uses only native Lean constants and parsing.

## Source provenance

The source is clean `tornado-cli-new-era` commit
`daaa0c18de91ecc2effbdaea8d0bea7c856ff7f7`. The module pins SHA-256 of
the TypeScript catalog and both JSON sources. Run the development-only checker
from this repo:

```sh
python3 scripts/check_selected_pool_bootstrap.py
```

It authenticates those source bytes and compares every Lean table row to the
catalog, bootstrap, and manifest. It normalizes addresses numerically because
some source JSON keys omit a leading zero. The checker passed for all 29 rows.
The compiled Lean test `selected_pool_bootstrap_test` passed for all 29 fresh
cursors and tested wrong-chain, unknown-pool, spoofed-amount, zero, and
oversized-address rejection. Four finite theorems establish row count,
positive registration blocks, equality with manifest starts, and unique
chain/address identities with **no axioms**. Exhaustive coverage through the
runtime `selected` parser is tested, rather than proved as a Lean theorem.

The pinned source files and translation remain trust assumptions. This module
does not authenticate chain data, the endpoint, event coverage, finality,
root/leaf claims, or current pool registration on chain. Those belong to the
history validators and on-chain checks. Experimental withdrawal sessions use
this catalog-bound bootstrap; it does not itself authorize or submit a spend.
