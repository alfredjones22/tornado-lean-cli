#!/usr/bin/env python3
"""Check compiled history descriptors against the pinned CLI manifest."""

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CLI = Path(sys.argv[1]).resolve() if len(sys.argv) == 2 else ROOT.parent / "tornado-cli-new-era"
lean = (ROOT / "Tornado/Runtime/HistorySnapshotManifest.lean").read_text()
source = (CLI / "src/services/history-manifest.json").read_bytes()
pin = re.search(r'def sourceSHA256 : String := "([0-9a-f]{64})"', lean)
assert pin and hashlib.sha256(source).hexdigest() == pin.group(1), "History manifest source digest differs"
manifest = json.loads(source)
pattern = re.compile(
    r'⟨(\d+), (0x[0-9a-f]+), "([^"]+)", "([^"]+)", "([0-9a-f]{64})", '
    r'(\d+), (\d+), (\d+), (\d+), (\d+), (\d+)⟩'
)
actual = pattern.findall(lean)
assert len(actual) == 29, "History descriptors do not cover exactly 29 supported pools"
seen = set()
for chain, pool, state_key, file, digest, json_bytes, gzip_bytes, start, end, deposits, withdrawals in actual:
    identity = (int(chain), int(pool, 16))
    assert identity not in seen, "Duplicate history descriptor"
    seen.add(identity)
    entry = manifest["chains"][chain]
    matches = [value for address, value in entry["pools"].items() if int(address, 16) == identity[1]]
    assert len(matches) == 1, "Missing source pool descriptor"
    descriptor = matches[0]
    assert state_key == entry["stateKey"]
    assert (file, digest, int(json_bytes), int(gzip_bytes), int(start), int(end), int(deposits), int(withdrawals)) == (
        descriptor["file"], descriptor["sha256"], descriptor["jsonBytes"], descriptor["gzipBytes"],
        int(descriptor["fromBlock"], 16), int(descriptor["toBlock"], 16), descriptor["deposits"], descriptor["withdrawals"]
    ), f"Native history descriptor differs for {pool}"
bootstrap = (ROOT / "Tornado/Protocol/SelectedPoolBootstrap.lean").read_text()
supported = {(1 if chain == "mainnet" else 11155111, int(address, 16))
             for chain, address in re.findall(r'⟨\.(mainnet|sepolia), (0x[0-9a-f]+),', bootstrap)}
assert seen == supported, "History descriptor identities differ from the pinned supported catalog"
print("PASS: all 29 compiled history snapshot descriptors match the pinned CLI manifest")
