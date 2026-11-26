#!/usr/bin/env python3
"""Check compiled history descriptors against the pinned CLI manifest."""

import hashlib
import gzip
import io
import json
import re
import sys
from pathlib import Path

# Explicit public release assets only. Never enumerate a live session/cache,
# note backup, or arbitrary asset directory as verification evidence.
BUNDLED_SEPOLIA_FILES = {
    "11155111/0x0e999c5285141ccb6dfae68a0921f37abd3e6a87-6ac12c3cdf215493.json.gz",
    "11155111/0x9480be3964642efcd6cebdb3570db8dc0f788908-976c3b43d178bae6.json.gz",
    "11155111/0x8c4a04d872a6c1be37964a21ba3a138525dff50b-ceb6fa3aadea3bf4.json.gz",
    "11155111/0x83091415b54d764e215153ff54b36ccd44122e6e-9d67d34e77947ebc.json.gz",
    "11155111/0x8cc930096b4df705a007c4a039bdfa1320ed2508-d8b706c462583256.json.gz",
    "11155111/0x7ee90edc51c3739af3ee277e09ade3f3d6bad4af-16c70734c312c18a.json.gz",
    "11155111/0x8d10d506d29fc62abb8a290b99f66db27fc43585-4c2d8491cca8b9f4.json.gz",
    "11155111/0x3d1c943dfb2c8d9905b0da0afd18615915ff343a-9d8b31c456aa03bd.json.gz",
    "11155111/0x6921fd1a97441dd603a997ed6ddf388658daf754-364c228163859be7.json.gz",
}

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
metadata = {
    (1 if chain == "mainnet" else 11155111, int(address, 16)):
        (int(registered), int(amount), int(asset, 16))
    for chain, address, registered, _, amount, asset in re.findall(
        r'⟨\.(mainnet|sepolia), (0x[0-9a-f]+), (\d+), (\d+), (\d+), (0x[0-9a-f]+)⟩', bootstrap)
}


def hex_number(value):
    assert isinstance(value, str) and re.fullmatch(r"0x[0-9a-f]{1,64}", value), "Invalid snapshot identifier"
    return int(value, 16)


bundled = set()
for chain, pool, state_key, file, digest, json_bytes, gzip_bytes, start, end, deposits, withdrawals in actual:
    if chain != "11155111":
        continue
    assert file in BUNDLED_SEPOLIA_FILES, "Unexpected bundled snapshot path"
    bundled.add(file)
    asset_path = ROOT / "assets/history" / file
    assert asset_path.is_file() and not asset_path.is_symlink(), "Missing or symlinked bundled public snapshot"
    expected_size, expected_gzip = int(json_bytes), int(gzip_bytes)
    assert 0 < expected_size <= 128 * 1024 * 1024 and 0 < expected_gzip <= 128 * 1024 * 1024
    assert asset_path.stat().st_size == expected_gzip, "Bundled snapshot compressed size differs"
    compressed = asset_path.read_bytes()
    assert len(compressed) == expected_gzip, "Bundled snapshot changed during read"
    with gzip.GzipFile(fileobj=io.BytesIO(compressed)) as stream:
        raw = stream.read(expected_size + 1)
    assert len(raw) == expected_size, "Bundled snapshot decoded size differs"
    assert hashlib.sha256(raw).hexdigest() == digest, "Bundled snapshot SHA-256 differs"
    parsed = json.loads(raw)
    assert isinstance(parsed, dict) and set(parsed) == {state_key}, "Bundled snapshot state key differs"
    state = parsed[state_key]
    identity = (int(chain), int(pool, 16))
    registered, amount, asset = metadata[identity]
    assert hex_number(state["instanceRegistryInfo"]["chainId"]) == identity[0]
    pools = state["pools"]["poolsTuples"]
    assert len(pools) == 1 and len(pools[0]) == 2 and hex_number(pools[0][0]) == identity[1]
    row = pools[0][1]
    assert isinstance(row["isERC20"], bool), "Bundled snapshot asset flag is not boolean"
    assert (hex_number(row["address"]), hex_number(row["registeredBlock"]),
            hex_number(row["lastSyncedBlock"]), hex_number(row["denomination"]),
            hex_number(row["asset"]), row["isERC20"]) == (
                identity[1], registered, int(end), amount, asset, asset != 0)
    groups = state["deposits"]["depositsTuples"]
    assert len(groups) <= 1, "Bundled snapshot has extra deposit pools"
    records = []
    if groups:
        assert len(groups[0]) == 2 and hex_number(groups[0][0]) == identity[1]
        records = groups[0][1]
    assert len(records) == int(deposits), "Bundled snapshot deposit count differs"
    assert all(hex_number(record[1]["pool"]) == identity[1] for record in records)
    records = state["withdrawals"]["withdrawalsTuples"]
    assert len(records) == int(withdrawals), "Bundled snapshot withdrawal count differs"
    assert all(hex_number(record[1]["pool"]) == identity[1] for record in records)
assert bundled == BUNDLED_SEPOLIA_FILES, "Bundled snapshot inventory differs"
print("PASS: all 29 compiled history snapshot descriptors match the pinned CLI manifest")
