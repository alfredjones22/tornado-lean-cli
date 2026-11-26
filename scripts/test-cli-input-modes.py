#!/usr/bin/env python3
"""Check CLI admission and network diagnostics using only public fixtures."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
CLI = ROOT / '.lake/build/bin/tornado'
MISSING_JOURNAL = str(ROOT / 'tests' / 'nonexistent-input-mode-journal.json')

for command in [['deposit', 'send'], ['deposit', 'pay-invoice'], ['withdraw', 'one'],
                ['withdraw', 'batch'], ['smart-account', 'recover']]:
    help_output = subprocess.check_output([str(CLI), *command, '--help'], text=True)
    assert '--broadcast' in help_output and '--experimental-send' not in help_output
    assert '--non-interactive' in help_output
    old = subprocess.run([str(CLI), *command, '--experimental-send'],
                         capture_output=True, text=True, start_new_session=True, timeout=10)
    assert old.returncode != 0

for command, expected in [
    (['deposit', 'send', '--notes-file', '/missing', '--broadcast'], '--key-file for deposits'),
    (['deposit', 'pay-invoice', '--invoice-file', '/missing', '--broadcast'], '--key-file for deposits'),
    (['withdraw', 'batch', '--notes-file', '/missing', '--broadcast'], '--owner-key-file for batch withdrawals'),
    (['withdraw', 'batch', '--notes-file', '/missing', '--dry-run'], '--owner-key-file for batch withdrawals'),
    (['smart-account', 'recover', '--broadcast', '--journal', MISSING_JOURNAL], '--owner-key-file for recovery sending'),
    (['smart-account', 'recover', '--dry-run'], '--owner or --owner-key-file for recovery review'),
]:
    result = subprocess.run([str(CLI), *command, '--non-interactive'],
                            capture_output=True, text=True, start_new_session=True, timeout=10)
    assert result.returncode != 0 and expected in result.stderr, result.stderr
    assert 'No interactive terminal' not in result.stderr

for command in [['withdraw', 'one'], ['withdraw', 'batch']]:
    result = subprocess.run([str(CLI), *command, '--broadcast', '--non-interactive', '--yes'],
                            capture_output=True, text=True, start_new_session=True, timeout=10)
    assert result.returncode != 0 and '--yes is unavailable' in result.stderr

for command in [
    ['deposit', 'send', '--notes-file', '/missing', '--journal', MISSING_JOURNAL, '--resume', '--dry-run'],
    ['deposit', 'pay-invoice', '--invoice-file', '/missing', '--dry-run'],
    ['withdraw', 'batch', '--notes-file', '/missing', '--broadcast'],
    ['withdraw', 'batch', '--notes-file', '/missing', '--dry-run'],
    ['smart-account', 'recover', '--broadcast', '--journal', MISSING_JOURNAL],
    ['smart-account', 'recover', '--dry-run'],
]:
    result = subprocess.run([str(CLI), *command], capture_output=True, text=True,
                            start_new_session=True, timeout=10)
    assert result.returncode != 0 and 'No interactive terminal is available' in result.stderr, command

for flags in [['--resume', '--delegated'], ['--delegated', '--sequential']]:
    result = subprocess.run([str(CLI), 'deposit', 'send', *flags, '--dry-run'],
                            capture_output=True, text=True, start_new_session=True, timeout=10)
    assert result.returncode != 0 and 'cannot' in result.stderr
    assert 'No interactive terminal' not in result.stderr

directory = Path(tempfile.mkdtemp(prefix='.withdraw-network-', dir=ROOT / 'tests'))
try:
    os.chmod(directory, 0o700)
    # Public, unfunded fixtures. Both remote endpoints are unreachable
    # loopback addresses; this test cannot submit to an external service.
    raw = 'tornado-eth-0.01-11155111-0x' + '11' * 62
    notes = directory / 'public-note.txt'
    notes.write_text(raw + '\n')
    notes.chmod(0o600)
    key = directory / 'public-key-one.txt'
    key.write_text('0x' + '0' * 63 + '1\n')
    key.chmod(0o600)
    common = ['--broadcast', '--rpc', 'http://127.0.0.1:1',
              '--bundler-url', 'http://127.0.0.1:1', '--status-dir', str(directory)]
    for command in [
        ['withdraw', 'one', '--note-file', str(notes),
         '--recipient', '0x1111111111111111111111111111111111111111'],
        ['withdraw', 'batch', '--notes-file', str(notes), '--owner-key-file', str(key)],
    ]:
        result = subprocess.run([str(CLI), *command, *common], capture_output=True,
                                text=True, start_new_session=True, timeout=90)
        assert result.returncode != 0 and 'Selected network: Ethereum mainnet (chain 1)' in result.stderr, result.stderr
        assert '--chain 11155111' in result.stderr and 'before proof generation' in result.stderr
        assert raw not in result.stderr and raw not in result.stdout
    for note_path in [str(directory / 'missing-note.txt'), '~/Desktop/tornado-public-missing-note.txt']:
        resolved = Path(note_path) if Path(note_path).is_absolute() else ROOT / note_path
        for command in [
            ['withdraw', 'one', '--note-file', note_path,
             '--recipient', '0x1111111111111111111111111111111111111111'],
            ['withdraw', 'batch', '--notes-file', note_path, '--owner-key-file', str(key)],
        ]:
            result = subprocess.run([str(CLI), *command, *common, '--chain', '11155111'],
                                    cwd=ROOT, capture_output=True, text=True,
                                    start_new_session=True, timeout=30)
            assert result.returncode != 0 and 'Note backup file was not found:' in result.stderr, result.stderr
            assert str(resolved) in result.stderr and 'tilde' in result.stderr
            assert 'Prover metadata inspection failed' not in result.stderr
finally:
    shutil.rmtree(directory)
print('PASS: broadcast flag admission, optional account key files, no-TTY failures and resume flag conflicts')
