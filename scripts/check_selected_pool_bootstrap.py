#!/usr/bin/env python3
"""Development-only provenance check for native Lean pool bootstrap constants.

Reads the pinned TypeScript CLI's public JSON sources. The runnable Lean CLI
never loads these JSON files or invokes Python/Node for pool bootstrap.
"""

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CLI = Path(sys.argv[1]).resolve() if len(sys.argv) == 2 else ROOT.parent / "tornado-cli-new-era"
SOURCE_COMMIT = "a24d5f5e89d1f2486a031b1e5e8b1a92e81e1326"
LEAN = (ROOT / "Tornado/Protocol/SelectedPoolBootstrap.lean").read_text()


def pinned_source(relative: str, constant: str) -> bytes:
    source = CLI / relative
    data = source.read_bytes()
    expected = re.search(rf'def {constant} : String :=\s*"([0-9a-f]{{64}})"', LEAN)
    assert expected, f"Missing Lean source pin: {constant}"
    assert hashlib.sha256(data).hexdigest() == expected.group(1), f"Source digest changed: {source}"
    return data


assert subprocess.check_output(["git", "-C", str(CLI), "rev-parse", "HEAD"], text=True).strip() == SOURCE_COMMIT
bootstrap = json.loads(pinned_source("src/services/history-bootstrap.json", "bootstrapSourceSHA256"))
manifest = json.loads(pinned_source("src/services/history-manifest.json", "manifestSourceSHA256"))
pinned_source("src/domain/catalog.ts", "catalogSourceSHA256")

catalog_text = (ROOT / "Tornado/Domain/Catalog.lean").read_text()
catalog_pattern = re.compile(
    r'\{ chainId := \.(mainnet|sepolia), denomination := "[^"]+", amount := (\d+),'
    r'\s+address := "(0x[0-9a-fA-F]+)", asset := ⟨"[^"]+", \d+, '
    r'(none|some "0x[0-9a-fA-F]+")⟩'
)
catalog = catalog_pattern.findall(catalog_text)
assert len(catalog) == 29, "Lean catalog no longer has exactly 29 supported pools"

section = LEAN.split("def rows : List Row := [", 1)[1].split("\n]\n", 1)[0]
row_pattern = re.compile(
    r'⟨\.(mainnet|sepolia), (0x[0-9a-f]+), (\d+), (\d+), (\d+), (0x[0-9a-f]+)⟩'
)
actual = [
    (chain, int(address, 16), int(registered), int(start), int(amount), int(asset, 16))
    for chain, address, registered, start, amount, asset in row_pattern.findall(section)
]
assert len(actual) == 29, "Lean bootstrap no longer has exactly 29 pinned rows"

expected = []
for chain_name, amount, address, token in catalog:
    chain_id = "1" if chain_name == "mainnet" else "11155111"
    pool_address = int(address, 16)
    bootstrap_matches = [
        row for raw_address, row in bootstrap["chains"][chain_id]["pools"]["poolsTuples"]
        if int(raw_address, 16) == pool_address
    ]
    manifest_matches = [
        descriptor for raw_address, descriptor in manifest["chains"][chain_id]["pools"].items()
        if int(raw_address, 16) == pool_address
    ]
    assert len(bootstrap_matches) == len(manifest_matches) == 1, f"Missing or duplicated {address}"
    saved = bootstrap_matches[0]
    descriptor = manifest_matches[0]
    token_address = 0 if token == "none" else int(token.split('"')[1], 16)
    assert int(saved["denomination"], 16) == int(amount), f"Wrong catalog amount: {address}"
    assert int(saved["asset"], 16) == token_address, f"Wrong catalog token: {address}"
    assert saved["isERC20"] == (token_address != 0), f"Wrong asset type: {address}"
    registered = int(saved["registeredBlock"], 16)
    start = int(descriptor["fromBlock"], 16)
    assert registered > 0 and registered == start, f"History starts before/after registration: {address}"
    expected.append((chain_name, pool_address, registered, start, int(amount), token_address))

assert actual == expected, "Native Lean bootstrap differs from source-pinned CLI rows"
assert len({(row[0], row[1]) for row in actual}) == 29, "Duplicate chain/pool address"
print("PASS: clean CLI source hashes and all 29 Lean pool bootstrap rows match catalog, bootstrap, and manifest")
