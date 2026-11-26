#!/usr/bin/env python3
"""Deposit resume, route and conflict checks against a local RPC fixture."""
import hashlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import tempfile
import threading

ROOT = Path(__file__).resolve().parent.parent
CLI = ROOT / '.lake/build/bin/tornado'
POOL = '0x199112Eb461ea7eeC1D75B33343542e1d069B41c'
SENDER = '0x7e5f4552091a69125d5dfcb7b8c2659029395bdf'
TOPIC = '0xa945e51eec50ab98c161376f0db4cf2aeba3ec92755fe2fcd388bdbbb80ff196'
BLOCK = '0x' + (17).to_bytes(32, 'big').hex()


def encode(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def main():
    directory = Path(tempfile.mkdtemp(prefix='.resume-cli-', dir=ROOT / 'tests'))
    server = None
    try:
        os.chmod(directory, 0o700)
        notes = directory / 'notes.txt'
        notes.write_text(''.join('tornado-eth-0.01-1-0x' +
                         (index.to_bytes(31, 'little') + (index + 100).to_bytes(31, 'little')).hex() + '\n'
                         for index in range(1, 7)))
        notes.chmod(0o600)
        output = subprocess.check_output([str(CLI), 'notes', 'invoice', '--file', str(notes)], text=True)
        commitments = [line.split('-')[-1] for line in output.strip().splitlines()]
        assert len(commitments) == 6 and len(set(commitments)) == 6
        key = directory / 'fixture-key'
        key.write_text('0x' + '0' * 63 + '1\n')
        key.chmod(0o600)
        journal = directory / 'journal.json'
        steps = []
        transactions = {}
        receipts = {}
        for index, commitment in enumerate(commitments):
            step = dict(kind='deposit', label='Deposit 0.01 ETH', to=POOL.lower(),
                        status='confirmed' if index < 5 else 'planned',
                        pool=POOL, commitment=commitment, denomination='0.01', asset='ETH')
            if index < 5:
                txhash = '0x' + (index + 1).to_bytes(32, 'big').hex()
                step['hash'] = txhash
                coordinates = dict(transactionHash=txhash, blockHash=BLOCK,
                                   blockNumber='0x1', transactionIndex=hex(index))
                log = dict(coordinates, address=POOL, topics=[TOPIC, commitment],
                           data='0x' + index.to_bytes(32, 'big').hex() + (1700000000).to_bytes(32, 'big').hex(),
                           logIndex=hex(index), removed=False)
                receipts[txhash] = dict(coordinates, **{'from': SENDER, 'to': POOL, 'status': '0x1'}, logs=[log])
                transactions[txhash] = dict(hash=txhash, **{'from': SENDER, 'to': POOL}, chainId='0x1',
                    type='0x2', nonce=hex(index), value=hex(10**16), input='0xb214faa5' + commitment[2:],
                    gas=hex(1387939), maxFeePerGas='0x3', maxPriorityFeePerGas='0x1',
                    blockHash=BLOCK, blockNumber='0x1', transactionIndex=hex(index))
            steps.append(step)
        original = encode(dict(version=1, kind='deposit', chainId=1,
                               account=SENDER, createdAt='native-lean', steps=steps))
        journal.write_bytes(original)
        journal.chmod(0o600)
        funded_claims = []
        for commitment in commitments[:5]:
            # Only the opaque filename hash is needed; ask the native Keccak
            # compatibility fixture through its standard public invoice identities.
            identity = f'tornado-lean-cli/invoice/v1/1/{POOL.lower()}/{commitment.lower()}'
            # Python's SHA3 is not Ethereum Keccak. The checked-in CLI source
            # fixture helper below exports the native public identity digest.
            helper = directory / 'Claim.lean'
            helper.write_text('import Tornado.Crypto.Keccak\n'
                              'def main : IO Unit := IO.println (Tornado.Crypto.bytesToHex '
                              f'(Tornado.Crypto.keccak256 "{identity}".toUTF8))\n')
            digest = subprocess.check_output(['lake', 'env', 'lean', '--run', str(helper)], cwd=ROOT, text=True).strip()
            path = directory / f'.tornado-invoice-{digest}.claim'
            path.write_bytes(encode(dict(version=1, kind='invoice-claim', chainId=1,
                pool=POOL, commitment=commitment, sender=SENDER, journal=str(journal))))
            path.chmod(0o600)
            funded_claims.append(path)
        (directory / 'Claim.lean').unlink()
        calls = []

        class RPC(BaseHTTPRequestHandler):
            def log_message(self, *_):
                pass

            def do_POST(self):
                request = json.loads(self.rfile.read(int(self.headers['Content-Length'])))
                method, params = request['method'], request['params']
                calls.append(method)
                if method == 'eth_chainId': result = '0x1'
                elif method == 'eth_getTransactionReceipt': result = receipts.get(params[0])
                elif method == 'eth_getTransactionByHash': result = transactions.get(params[0])
                elif method == 'eth_getBlockByNumber': result = dict(number='0x1', hash=BLOCK)
                elif method == 'eth_blockNumber': result = '0x1'
                elif method == 'eth_getTransactionCount': result = '0x5'
                elif method == 'eth_getBalance': result = hex(2 * 10**16)
                elif method == 'eth_getCode': result = '0xef0100e6cae83bde06e4c305530e199d7217f42808555b'
                elif method == 'eth_estimateGas': result = hex(1156615)
                elif method == 'eth_feeHistory': result = dict(baseFeePerGas=['0x1', '0x1'], reward=[['0x1']])
                elif method == 'eth_call':
                    data = params[0]['data']
                    if data.startswith('0x839df945'):
                        value = int(('0x' + data[-64:]).lower() in [c.lower() for c in commitments[:5]])
                    else: value = 10**16
                    result = '0x' + value.to_bytes(32, 'big').hex()
                else:
                    result = None
                response = json.dumps(dict(jsonrpc='2.0', id=request['id'], result=result)).encode()
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                self.send_header('Content-Length', str(len(response)))
                self.end_headers()
                self.wfile.write(response)

        server = ThreadingHTTPServer(('127.0.0.1', 0), RPC)
        threading.Thread(target=server.serve_forever, daemon=True).start()
        base = [str(CLI), 'deposit', 'send', '--notes-file', str(notes), '--key-file', str(key),
                '--journal', str(journal), '--rpc', f'http://127.0.0.1:{server.server_port}']
        snapshot = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in directory.iterdir()}
        preview = subprocess.run([*base, '--resume', '--dry-run'], capture_output=True, text=True, timeout=60)
        assert preview.returncode == 0 and '5/6 deposits confirmed; 1 unexposed deposits remain' in preview.stdout, preview.stderr
        assert snapshot == {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in directory.iterdir()}
        duplicate = subprocess.run([*base, '--broadcast'], capture_output=True, text=True, timeout=10)
        assert duplicate.returncode != 0 and 'with --resume' in duplicate.stderr
        for _ in range(2):
            cancelled = subprocess.run([*base, '--resume', '--broadcast'], input='CANCEL\n',
                                       capture_output=True, text=True, timeout=60)
            assert cancelled.returncode != 0 and 'Step 6/6' in cancelled.stdout
            assert 'cancelled before signing' in cancelled.stderr
        single_notes = directory / 'one-note.txt'
        single_notes.write_text(notes.read_text().splitlines()[0] + '\n')
        single_notes.chmod(0o600)
        one = [str(CLI), 'deposit', 'send', '--notes-file', str(single_notes),
               '--key-file', str(key), '--rpc', f'http://127.0.0.1:{server.server_port}']
        for flags, route in [([], 'Route: sequential EIP-1559 transactions.'),
                             (['--delegated'], 'Route: 1 Simple7702 UserOperation batch(es).')]:
            review = subprocess.run([*one, *flags, '--dry-run'],
                                    capture_output=True, text=True, timeout=60)
            assert review.returncode == 0 and route in review.stdout, review.stderr
        lock, = directory.glob('.tornado-sender-*.lock')
        lock_bytes = lock.read_bytes()
        new_journal = directory / 'new-attempt.json'
        for flags in [[], ['--delegated']]:
            blocked = subprocess.run([*one, *flags, '--journal', str(new_journal), '--broadcast'],
                                     capture_output=True, text=True, timeout=60)
            assert blocked.returncode != 0 and 'A deposit sender lock already exists:' in blocked.stderr, blocked.stderr
            assert str(lock) in blocked.stderr and 'deposit send --resume' in blocked.stderr
            assert 'errno 17' not in blocked.stderr
            assert lock.read_bytes() == lock_bytes and not new_journal.exists()
        # Move only this synthetic fixture lock, to exercise the independent
        # permanent commitment claim. Never inspect or modify user files.
        lock.rename(directory / 'saved-fixture-lock')
        invoice = directory / 'public-invoice.txt'
        invoice.write_text(output.splitlines()[0] + '\n')
        invoice.chmod(0o600)
        payer = [str(CLI), 'deposit', 'pay-invoice', '--invoice-file', str(invoice),
                 '--key-file', str(key), '--rpc', f'http://127.0.0.1:{server.server_port}']
        for command in [one, [*one, '--delegated'], payer]:
            blocked = subprocess.run([*command, '--journal', str(new_journal), '--broadcast'],
                                     capture_output=True, text=True, timeout=60)
            assert blocked.returncode != 0 and 'A deposit reservation already exists' in blocked.stderr, blocked.stderr
            assert str(funded_claims[0]) in blocked.stderr and 'remain after a successful deposit' in blocked.stderr
            assert 'errno 17' not in blocked.stderr and not lock.exists() and not new_journal.exists()

        # New deposits may choose a journal, but resuming must still identify
        # the original one. Use one shared working directory and separate
        # synthetic key directories so cancellation locks cannot mask naming
        # collisions between independent attempts.
        default_cwd = directory / 'default-journals'
        default_cwd.mkdir(mode=0o700)
        prior_journal = default_cwd / 'preserved-journal.json'
        prior_journal.write_bytes(original)
        prior_journal.chmod(0o600)
        default_notes = directory / 'default-note.txt'
        default_notes.write_text(notes.read_text().splitlines()[-1] + '\n')
        default_notes.chmod(0o600)
        default_invoice = directory / 'default-invoice.txt'
        default_invoice.write_text(output.splitlines()[-1] + '\n')
        default_invoice.chmod(0o600)
        key_paths = []
        for index in range(4):
            key_directory = directory / f'default-key-{index}'
            key_directory.mkdir(mode=0o700)
            fixture_key = key_directory / 'key.txt'
            fixture_key.write_bytes(key.read_bytes())
            fixture_key.chmod(0o600)
            key_paths.append(fixture_key)

        endpoint = f'http://127.0.0.1:{server.server_port}'
        default_send = [str(CLI), 'deposit', 'send', '--notes-file', str(default_notes),
                        '--chain', '1', '--rpc', endpoint]
        default_pay = [str(CLI), 'deposit', 'pay-invoice', '--invoice-file', str(default_invoice),
                       '--chain', '1', '--rpc', endpoint]
        before_dry = {p.name: p.read_bytes() for p in default_cwd.iterdir()}
        for command in [default_send, default_pay]:
            review = subprocess.run([*command, '--key-file', str(key_paths[0]), '--dry-run'],
                                    cwd=default_cwd, capture_output=True, text=True, timeout=60)
            assert review.returncode == 0 and 'Dry run complete.' in review.stdout, review.stderr
            assert before_dry == {p.name: p.read_bytes() for p in default_cwd.iterdir()}
        missing_resume = subprocess.run([*default_send, '--key-file', str(key_paths[0]),
                                         '--resume', '--broadcast'], cwd=default_cwd,
                                        capture_output=True, text=True, timeout=30)
        assert missing_resume.returncode != 0 and '--resume requires the original --journal' in missing_resume.stderr
        assert before_dry == {p.name: p.read_bytes() for p in default_cwd.iterdir()}

        chosen = []
        for index, command in enumerate([default_send, default_send, default_pay, default_pay]):
            existing = {p.name: p.read_bytes() for p in default_cwd.iterdir()}
            cancelled = subprocess.run([*command, '--key-file', str(key_paths[index]), '--broadcast'],
                                       cwd=default_cwd, input='CANCEL\n', capture_output=True,
                                       text=True, timeout=60)
            assert cancelled.returncode != 0 and 'cancelled before signing' in cancelled.stderr, cancelled.stderr
            printed = [line.removeprefix('Journal: ') for line in cancelled.stdout.splitlines()
                       if line.startswith('Journal: ')]
            assert len(printed) == 1, cancelled.stdout
            selected = Path(printed[0])
            assert selected.parent == default_cwd and re.fullmatch(r'tornado-deposit-1-[0-9a-f]{32}\.json', selected.name)
            assert selected not in chosen and selected.is_file()
            assert stat.S_IMODE(selected.stat().st_mode) == 0o600
            assert set(p.name for p in default_cwd.iterdir()) == set(existing) | {selected.name}
            for name, contents in existing.items():
                assert (default_cwd / name).read_bytes() == contents, 'An existing journal was modified'
            planned = json.loads(selected.read_bytes())
            assert planned['kind'] == 'deposit' and planned['chainId'] == 1
            assert planned['account'].lower() == SENDER and len(planned['steps']) == 1
            assert planned['steps'][0]['status'] == 'planned' and planned['steps'][0].get('hash') is None
            chosen.append(selected)
        assert len(chosen) == 4 and prior_journal.read_bytes() == original
        assert 'eth_sendRawTransaction' not in calls and journal.read_bytes() == original
        for path in funded_claims:
            assert hashlib.sha256(path.read_bytes()).hexdigest() == snapshot[path.name]
        print('PASS: actual CLI resume, protected deposit conflicts and single-note routing without broadcast')
    finally:
        if server is not None:
            server.shutdown()
            server.server_close()
        shutil.rmtree(directory)


if __name__ == '__main__':
    main()
