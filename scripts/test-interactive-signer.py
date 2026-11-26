#!/usr/bin/env python3
"""Offline PTY checks using the universally public secp256k1 key 1."""
import errno
import fcntl
import os
from pathlib import Path
import pty
import select
import signal
import shutil
import subprocess
import tempfile
import termios
import time

ROOT = Path(__file__).resolve().parent.parent
BINARY = ROOT / '.lake/build/bin/native_signer_test'
PUBLIC_KEY = b'0x' + b'0' * 63 + b'1'


def run_terminal(directory, entered, expected_success=False, interrupt=None):
    master, slave = pty.openpty()
    before = termios.tcgetattr(slave)

    def terminal_session():
        os.setsid()
        fcntl.ioctl(0, termios.TIOCSCTTY, 0)

    process = subprocess.Popen([str(BINARY), str(directory), 'interactive'],
                               stdin=slave, stdout=slave, stderr=slave,
                               preexec_fn=terminal_session, close_fds=True)
    output = bytearray()
    sent = approved = restored = False
    deadline = time.monotonic() + 30
    try:
        while time.monotonic() < deadline:
            ready, _, _ = select.select([master], [], [], 0.05)
            if ready:
                try:
                    chunk = os.read(master, 65536)
                except OSError as error:
                    if error.errno != errno.EIO:
                        raise
                    chunk = b''
                output.extend(chunk)
            if not sent and b'Private key (hidden;' in output:
                assert not termios.tcgetattr(slave)[3] & termios.ECHO, 'Key prompt has terminal echo enabled'
                if interrupt is None:
                    os.write(master, entered)
                else:
                    process.send_signal(interrupt)
                sent = True
            if expected_success and not approved and b'INTERACTIVE_READY_FOR_APPROVAL' in output:
                assert termios.tcgetattr(slave)[3] & termios.ECHO == before[3] & termios.ECHO
                os.write(master, b'APPROVE\n')
                approved = True
            if not restored and b'INTERACTIVE_EXIT_CODE:' in output:
                assert termios.tcgetattr(slave)[3] & termios.ECHO == before[3] & termios.ECHO, 'Terminal echo was not restored'
                restored = True
                os.write(master, b'RELEASE\n')
            if process.poll() is not None:
                break
        else:
            raise AssertionError('Interactive signer test timed out')
        process.wait(timeout=5)
        assert sent and restored and (process.returncode == 0) == expected_success, 'Unexpected interactive signer result'
        assert PUBLIC_KEY not in output and b'SYNTHETIC_SECRET_SENTINEL' not in output, 'Entered key text escaped into terminal output'
        if expected_success:
            assert approved and b'PASS: hidden native key input' in output
        return bytes(output)
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
        os.close(master)
        os.close(slave)


def main():
    directory = Path(tempfile.mkdtemp(prefix='.interactive-signer-', dir=ROOT / 'tests'))
    try:
        os.chmod(directory, 0o700)
        run_terminal(directory, PUBLIC_KEY + b'\nSEND\n', True)
        invalid = run_terminal(directory, b'SYNTHETIC_SECRET_SENTINEL\n')
        assert b'Enter one valid Ethereum private key' in invalid
        interrupted = run_terminal(directory, b'\x03')
        assert b'interrupted' in interrupted
        for interruption in [signal.SIGTERM, signal.SIGHUP, signal.SIGQUIT]:
            interrupted = run_terminal(directory, b'', interrupt=interruption)
            assert b'interrupted' in interrupted
        run_terminal(directory, b'\x04')
        run_terminal(directory, b'X' * 1100 + b'\n')
        no_terminal = subprocess.run([str(BINARY), str(directory), 'interactive'],
                                     stdin=subprocess.DEVNULL, capture_output=True,
                                     start_new_session=True, timeout=10)
        assert no_terminal.returncode != 0 and b'No interactive terminal is available' in no_terminal.stderr
        assert list(directory.iterdir()) == [], 'Interactive signer created a disk key'
        print('PASS: hidden PTY input, native signing, paste isolation, cancellation, EOF, no-TTY and terminal restoration')
    finally:
        shutil.rmtree(directory)


if __name__ == '__main__':
    main()
