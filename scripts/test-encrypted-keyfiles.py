#!/usr/bin/env python3
"""Offline Web3 Secret Storage v3 checks with universally public fixture keys.

Official PBKDF2/scrypt vectors are from go-ethereum's published v3 fixtures:
https://github.com/ethereum/go-ethereum/blob/master/accounts/keystore/testdata/v3_test_vector.json
No real account key, RPC endpoint, or external transaction is used.
"""
import copy
import errno
import fcntl
import hashlib
import json
import os
from pathlib import Path
import pty
import select
import shutil
import signal
import subprocess
import tempfile
import termios
import time

ROOT = Path(__file__).resolve().parent.parent
BINARY = ROOT / '.lake/build/bin/encrypted_keyfile_test'
CLI = ROOT / '.lake/build/bin/tornado'
PUBLIC_KEY_ONE = '0x' + '0' * 63 + '1'
PUBLIC_KEY_TWO = '0x' + '0' * 63 + '2'
OFFICIAL_KEY = '7a28b5ba57c53603b0b07b56bba752f7784bf506fa95edc395f5cf6c7514fe9d'
SENTINEL = 'SYNTHETIC_PASSWORD_MUST_NOT_APPEAR_IN_DIAGNOSTICS'
PASSWORD = 'testpassword'
OFFICIAL = {
    'pbkdf2': {
        'crypto': {
            'cipher': 'aes-128-ctr',
            'cipherparams': {'iv': '6087dab2f9fdbbfaddc31a909735c1e6'},
            'ciphertext': '5318b4d5bcd28de64ee5559e671353e16f075ecae9f99c7a79a38af5f869aa46',
            'kdf': 'pbkdf2',
            'kdfparams': {'c': 262144, 'dklen': 32, 'prf': 'hmac-sha256',
                          'salt': 'ae3cd4e7013836a3df6bd7241b12db061dbe2c6785853cce422d148a624ce0bd'},
            'mac': '517ead924a9d0dc3124507e3393d175ce3ff7c1e96529c6c555ce9e51205e9b2',
        },
        'id': '3198bc9c-6672-5ab3-d995-4942343ae5b6', 'version': 3,
    },
    'scrypt': {
        'crypto': {
            'cipher': 'aes-128-ctr',
            'cipherparams': {'iv': '83dbcc02d8ccb40e466191a123791e0e'},
            'ciphertext': 'd172bf743a674da9cdad04534d56926ef8358534d458fffccd4e6ad2fbde479c',
            'kdf': 'scrypt',
            'kdfparams': {'dklen': 32, 'n': 262144, 'p': 8, 'r': 1,
                          'salt': 'ab0c7876052600dd703518d6fc3fe8984592145b591fc8fb5c6d43190334ba19'},
            'mac': '2103ac29920d71da29f15d75b4a16dbe95cfd7ff8faea1056c33131d846e3097',
        },
        'id': '3198bc9c-6672-5ab3-d995-4942343ae5b6', 'version': 3,
    },
}
SHORT_KEYS = {
    'geth31': {
        'crypto': {'cipher': 'aes-128-ctr', 'cipherparams': {'iv': 'e0c41130a323adc1446fc82f724bca2f'},
                   'ciphertext': '9517cd5bdbe69076f9bf5057248c6c050141e970efa36ce53692d5d59a3984',
                   'kdf': 'scrypt', 'kdfparams': {'dklen': 32, 'n': 2, 'r': 8, 'p': 1,
                   'salt': '711f816911c92d649fb4c84b047915679933555030b3552c1212609b38208c63'},
                   'mac': 'd5e116151c6aa71470e67a7d42c9620c75c4d23229847dcc127794f0732b0db5'},
        'id': 'fecfc4ce-e956-48fd-953b-30f8b52ed66c', 'version': 3},
    'geth30': {
        'crypto': {'cipher': 'aes-128-ctr', 'cipherparams': {'iv': '3ca92af36ad7c2cd92454c59cea5ef00'},
                   'ciphertext': '108b7d34f3442fc26ab1ab90ca91476ba6bfa8c00975a49ef9051dc675aa',
                   'kdf': 'scrypt', 'kdfparams': {'dklen': 32, 'n': 2, 'r': 8, 'p': 1,
                   'salt': 'd0769e608fb86cda848065642a9c6fa046845c928175662b8e356c77f914cd3b'},
                   'mac': '75d0e6759f7b3cefa319c3be41680ab6beea7d8328653474bd06706d4cc67420'},
        'id': 'a37e1559-5955-450d-8075-7b8931b392b2', 'version': 3},
}
_password_sequence = 0


def write_private(path, value, mode=0o600):
    data = value if isinstance(value, (str, bytes)) else json.dumps(value)
    path.write_bytes(data.encode() if isinstance(data, str) else data)
    path.chmod(mode)
    return path


def invoke(args, success=True, contains=None, timeout=35):
    result = subprocess.run([str(BINARY), *map(str, args)], cwd=ROOT,
                            capture_output=True, start_new_session=True, timeout=timeout)
    output = result.stdout + result.stderr
    assert (result.returncode == 0) == success, 'Unexpected public keystore driver result'
    assert SENTINEL.encode() not in output and OFFICIAL_KEY.encode() not in output
    assert PUBLIC_KEY_ONE.encode() not in output and PUBLIC_KEY_TWO.encode() not in output
    if contains:
        assert contains.encode() in output, 'Missing fixed keystore diagnostic'
    return output


def probe(path, password=None, password_file=None, noninteractive=True, expected='one', **checks):
    """Fixture convenience: no password is passed in the native driver's argv."""
    global _password_sequence
    if password is not None:
        assert password_file is None
        _password_sequence += 1
        password_file = write_private(path.parent / f'public-password-{_password_sequence}.txt', password)
    mode = (2 if password_file is not None else 0) | (4 if noninteractive else 0)
    return invoke(['probe', path, password_file or '', str(mode), expected], **checks)


def generated_keystore(password, key_hex=PUBLIC_KEY_ONE, dklen=32, scrypt=False):
    """Independent Python/OpenSSL construction, all inputs deliberately public."""
    salt = bytes(range(32))
    iv = bytes(range(16, 32))
    if scrypt:
        key = hashlib.scrypt(password.encode(), salt=salt, n=262144, r=8, p=1,
                             dklen=dklen, maxmem=512*1024*1024)
        params = {'n': 262144, 'r': 8, 'p': 1, 'dklen': dklen, 'salt': salt.hex()}
    else:
        key = hashlib.pbkdf2_hmac('sha256', password.encode(), salt, 2048, dklen)
        params = {'c': 2048, 'dklen': dklen, 'prf': 'hmac-sha256', 'salt': salt.hex()}
    cipher = subprocess.run(['openssl', 'enc', '-aes-128-ctr', '-K', key[:16].hex(),
                             '-iv', iv.hex()], input=bytes.fromhex(key_hex.removeprefix('0x')),
                            capture_output=True, check=True).stdout
    mac = subprocess.run(['openssl', 'dgst', '-keccak-256', '-binary'],
                         input=key[16:32] + cipher, capture_output=True, check=True).stdout
    assert len(cipher) == len(mac) == 32
    return {'version': 3, 'id': '00000000-0000-4000-8000-000000000001',
            'address': '7e5f4552091a69125d5dfcb7b8c2659029395bdf' if key_hex == PUBLIC_KEY_ONE else None,
            'crypto': {'cipher': 'aes-128-ctr', 'cipherparams': {'iv': iv.hex()},
                       'ciphertext': cipher.hex(), 'kdf': 'scrypt' if scrypt else 'pbkdf2',
                       'kdfparams': params,
                       'mac': mac.hex()}}


def run_terminal(path, password, success=False, expected='one', interrupt=None):
    master, slave = pty.openpty()
    before = termios.tcgetattr(slave)

    def controlling_terminal():
        os.setsid()
        fcntl.ioctl(0, termios.TIOCSCTTY, 0)

    process = subprocess.Popen([str(BINARY), 'interactive', str(path), expected],
                               cwd=ROOT, stdin=slave, stdout=slave, stderr=slave,
                               preexec_fn=controlling_terminal, close_fds=True)
    output = bytearray()
    sent = approved = restored = False
    deadline = time.monotonic() + 40
    try:
        while time.monotonic() < deadline:
            ready, _, _ = select.select([master], [], [], 0.05)
            if ready:
                try:
                    output.extend(os.read(master, 65536))
                except OSError as error:
                    if error.errno != errno.EIO:
                        raise
            if not sent and b'Keystore password (hidden):' in output:
                assert not termios.tcgetattr(slave)[3] & termios.ECHO
                if interrupt is None:
                    os.write(master, password)
                else:
                    process.send_signal(interrupt)
                sent = True
            if success and not approved and b'KEYSTORE_READY_FOR_APPROVAL' in output:
                assert termios.tcgetattr(slave)[3] & termios.ECHO == before[3] & termios.ECHO
                os.write(master, b'APPROVE\n')
                approved = True
            if not restored and b'KEYSTORE_EXIT_CODE:' in output:
                assert termios.tcgetattr(slave)[3] & termios.ECHO == before[3] & termios.ECHO
                restored = True
                os.write(master, b'RELEASE\n')
            if process.poll() is not None:
                break
        else:
            raise AssertionError('Hidden keystore password test timed out')
        process.wait(timeout=5)
        assert sent and restored and (process.returncode == 0) == success
        assert SENTINEL.encode() not in output and PUBLIC_KEY_ONE.encode() not in output
        entered_secret = password.split(b'\n', 1)[0]
        if len(entered_secret) >= 8:
            assert entered_secret not in output, 'Entered password escaped into terminal output'
        # This password is public, but echoing it would reveal a production one.
        assert b'PUBLIC_PTY_PASSWORD' not in output
        if success:
            assert approved and b'PASS: hidden keystore password' in output
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
        os.close(master)
        os.close(slave)


def cli_admission(directory, encrypted, pwd_file):
    notes = directory / 'notes.txt'
    subprocess.run([str(CLI), 'notes', 'create', '--chain', '11155111', '--asset', 'ETH',
                    '--denom', '0.01', '--count', '2', '--out', str(notes)], cwd=ROOT,
                   capture_output=True, check=True, timeout=30)
    invoice = directory / 'invoice.json'
    exported = subprocess.run([str(CLI), 'notes', 'invoice', '--file', str(notes), '--chain', '11155111'], cwd=ROOT,
                              capture_output=True, check=True, timeout=30)
    write_private(invoice, exported.stdout)
    loopback = 'http://127.0.0.1:1'
    wrong_password = write_private(directory/'wrong-cli-password.txt', SENTINEL)
    common = ['--chain', '11155111', '--rpc', loopback]
    commands = [
        ['deposit', 'send', '--notes-file', str(notes), '--key-file', str(encrypted), '--dry-run'],
        ['deposit', 'send', '--notes-file', str(notes), '--key-file', str(encrypted),
         '--resume', '--journal', str(directory / 'missing-resume.json'), '--dry-run'],
        ['deposit', 'pay-invoice', '--invoice-file', str(invoice), '--key-file', str(encrypted), '--dry-run'],
        ['withdraw', 'batch', '--notes-file', str(notes), '--owner-key-file', str(encrypted), '--dry-run'],
        ['withdraw', 'batch', '--notes-file', str(notes), '--owner-key-file', str(encrypted),
         '--bundler-url', loopback, '--broadcast'],
        ['smart-account', 'recover', '--owner-key-file', str(encrypted), '--dry-run'],
        ['smart-account', 'recover', '--owner-key-file', str(encrypted), '--broadcast',
         '--journal', str(directory / 'missing-recovery.json')],
    ]
    for command in commands:
        def run(extra):
            result = subprocess.run([str(CLI), *command, *common, '--non-interactive', *extra],
                                    cwd=directory, capture_output=True, start_new_session=True, timeout=20)
            output = result.stdout + result.stderr
            assert result.returncode != 0
            assert SENTINEL.encode() not in output and PUBLIC_KEY_ONE.encode() not in output
            return output
        missing = run([])
        assert b'--pwd-file' in missing, 'Encrypted noninteractive admission did not fail early'
        assert b'No interactive terminal' not in missing
        wrong = run(['--pwd-file', str(wrong_password)])
        assert b'incorrect password or corrupted file' in wrong, 'Wrong-password admission reached later work'
        conflict = run(['--pwd-file', str(wrong_password), '--pwd-file', str(pwd_file)])
        assert b'--pwd-file' in conflict
        # Equals forms must be parsed rather than rejected as unknown options.
        equals = run(['--pwd-file=' + str(wrong_password)])
        assert b'incorrect password or corrupted file' in equals
        equals_file = run(['--pwd-file=' + str(directory / 'missing-password')])
        assert b'password' in equals_file.lower() and b'unknown option' not in equals_file.lower()
        for option_spelling in ['--help', '--broadcast', '--dry-run', '--non-interactive']:
            literal = run(['--pwd-file', option_spelling])
            assert b'password' in literal.lower(), 'Password-file path was interpreted as a control flag'
        empty = run(['--pwd-file', ''])
        assert b'--pwd-file' in empty
        for legacy in [['--pwd', SENTINEL], ['--pwd='+SENTINEL]]:
            removed = run(legacy)
            assert b'--pwd-file' in removed
    assert not (directory / 'missing-resume.json').exists()
    assert not (directory / 'missing-recovery.json').exists()
    assert not list(directory.glob('.tornado-*')), 'Rejected password created transaction reservations'
    for base in [['deposit', 'send'], ['deposit', 'pay-invoice'], ['withdraw', 'batch'], ['smart-account', 'recover']]:
        help_text = subprocess.check_output([str(CLI), *base, '--help'], cwd=ROOT)
        assert b'--pwd-file' in help_text and b'--pwd <' not in help_text
    for command in [
        ['deposit','send','--notes-file',str(notes)],
        ['deposit','pay-invoice','--invoice-file',str(invoice)],
        ['withdraw','batch','--notes-file',str(notes)],
        ['smart-account','recover','--owner','0x'+'11'*20],
    ]:
        result=subprocess.run([str(CLI),*command,'--dry-run','--non-interactive','--pwd-file',str(pwd_file)],
                              cwd=directory,capture_output=True,start_new_session=True,timeout=15)
        output=result.stdout+result.stderr
        assert result.returncode!=0 and b'No interactive terminal' not in output
        assert b'--key-file' in output or b'--owner-key-file' in output
    for base in [['withdraw', 'one', '--note-file', str(notes), '--recipient', '0x'+'11'*20,
                  '--chain', '11155111', '--dry-run'],
                 ['withdraw', 'one', '--note-file', str(notes), '--recipient', '0x'+'11'*20,
                  '--chain', '11155111', '--route', 'relayer', '--broadcast', '--rpc', loopback]]:
        result = subprocess.run([str(CLI), *base, '--pwd-file', str(pwd_file), '--non-interactive'],
                                cwd=directory, capture_output=True, start_new_session=True, timeout=15)
        assert result.returncode != 0 and SENTINEL.encode() not in result.stdout+result.stderr


def main():
    directory = Path(tempfile.mkdtemp(prefix='.encrypted-keyfiles-', dir=ROOT / 'tests'))
    try:
        directory.chmod(0o700)
        for name, vector in OFFICIAL.items():
            path = write_private(directory / (name+'.json'), vector)
            probe(path, PASSWORD, expected='official', contains='PASS: protected')
        for name, vector in SHORT_KEYS.items():
            probe(write_private(directory/(name+'.json'), vector), 'foo', expected=name)
        # Normal geth-default work/memory parameters, independently constructed.
        large_scrypt = write_private(directory/'scrypt-256mib.json',generated_keystore('PUBLIC_SCRYPT_PASSWORD',scrypt=True))
        probe(large_scrypt,'PUBLIC_SCRYPT_PASSWORD')
        uppercase = copy.deepcopy(OFFICIAL['pbkdf2'])
        uppercase['Crypto'] = uppercase.pop('crypto')
        uppercase['address'] = '008aeeda4d805471df9b2a5b0f38a0c3bcba786b'
        uppercase['x-ethers'] = {'client': 'public-test', 'mnemonicCiphertext': '00'}
        probe(write_private(directory/'uppercase.json', uppercase), PASSWORD, expected='official')

        for index, password in enumerate(['PUBLIC_PTY_PASSWORD', '', '  significant spaces  ', 'pāss🔐']):
            path = write_private(directory/f'generated-{index}.json', generated_keystore(password, dklen=64 if index==3 else 32))
            probe(path, password)
        encrypted = directory/'generated-0.json'
        boundary = write_private(directory/'password-boundary.json', generated_keystore('P'*1024))
        boundary_pwd = write_private(directory/'password-boundary.txt', 'P'*1024)
        probe(boundary, password_file=boundary_pwd)
        boundary_line = write_private(directory/'password-boundary-crlf.txt', 'P'*1024+'\r\n')
        probe(boundary, password_file=boundary_line)
        beyond_pwd = write_private(directory/'password-too-long.txt', 'P'*1025)
        probe(boundary, password_file=beyond_pwd, success=False)
        pwd_file = write_private(directory/'password.txt', 'PUBLIC_PTY_PASSWORD\r\n')
        probe(encrypted, password_file=pwd_file)
        spaces_file = write_private(directory/'spaces-password.txt', '  significant spaces  \n')
        probe(directory/'generated-2.json', password_file=spaces_file)
        empty_file = write_private(directory/'empty-password.txt', '')
        probe(directory/'generated-1.json', password_file=empty_file)
        invoke(['cleanup', encrypted, pwd_file], contains='PASS: encrypted native session cleanup')

        raw = write_private(directory/'raw-key.txt', PUBLIC_KEY_ONE+'\n')
        probe(raw)
        raw_next = write_private(directory/'raw-key-next.txt', PUBLIC_KEY_TWO+'\n')
        invoke(['raw-reload', raw, raw_next], contains='PASS: raw key files are reloaded')
        write_private(raw, PUBLIC_KEY_ONE+'\n')
        probe(raw, SENTINEL, success=False)
        probe(encrypted, success=False, contains='--pwd-file')
        probe(encrypted, SENTINEL, success=False, contains='incorrect password or corrupted file')
        invoke(['probe', encrypted, pwd_file, '7', 'one'], success=False)
        probe(encrypted, password_file=directory/'missing-password', success=False)
        unsafe_password = write_private(directory/'unsafe-password.txt', 'PUBLIC_PTY_PASSWORD', 0o644)
        probe(encrypted, password_file=unsafe_password, success=False, contains='chmod 600')
        for name, value in [('newline-password', b'PUBLIC_PTY_PASSWORD\nextra'),
                            ('nul-password', b'PUBLIC_PTY_PASSWORD\x00'),
                            ('utf8-password', b'\xff'), ('long-password', b'X'*2000)]:
            bad_password_file=write_private(directory/(name+'.txt'),value)
            probe(encrypted,password_file=bad_password_file,success=False)
        password_symlink=directory/'password-symlink'
        password_symlink.symlink_to(pwd_file)
        probe(encrypted,password_file=password_symlink,success=False)
        password_hardlink=directory/'password-hardlink'
        os.link(pwd_file,password_hardlink)
        probe(encrypted,password_file=password_hardlink,success=False)
        password_hardlink.unlink()
        unsafe_key = write_private(directory/'unsafe-keystore.json', generated_keystore('PUBLIC_PTY_PASSWORD'), 0o644)
        probe(unsafe_key, 'PUBLIC_PTY_PASSWORD', success=False, contains='chmod 600')
        link = directory/'key-symlink'
        link.symlink_to(encrypted)
        probe(link, 'PUBLIC_PTY_PASSWORD', success=False)
        hard = directory/'key-hardlink'
        os.link(encrypted, hard)
        probe(hard, 'PUBLIC_PTY_PASSWORD', success=False)
        hard.unlink()

        def reject(name, mutate):
            value = generated_keystore('PUBLIC_PTY_PASSWORD')
            mutate(value)
            path = write_private(directory/(name+'.json'), value)
            probe(path, 'PUBLIC_PTY_PASSWORD', success=False)
        for name, mutate in [
            ('wrong-version', lambda x:x.update(version=4)),
            ('string-version', lambda x:x.update(version='3')),
            ('wrong-address', lambda x:x.update(address='11'*20)),
            ('wrong-cipher', lambda x:x['crypto'].update(cipher='aes-128-cbc')),
            ('wrong-kdf', lambda x:x['crypto'].update(kdf='argon2')),
            ('wrong-prf', lambda x:x['crypto']['kdfparams'].update(prf='hmac-sha512')),
            ('short-dk', lambda x:x['crypto']['kdfparams'].update(dklen=16)),
            ('huge-dk', lambda x:x['crypto']['kdfparams'].update(dklen=2**32)),
            ('zero-iterations', lambda x:x['crypto']['kdfparams'].update(c=0)),
            ('huge-iterations', lambda x:x['crypto']['kdfparams'].update(c=2**64-1)),
            ('fractional-iterations', lambda x:x['crypto']['kdfparams'].update(c=2048.5)),
            ('invalid-iv', lambda x:x['crypto']['cipherparams'].update(iv='gg'*16)),
            ('short-ciphertext', lambda x:x['crypto'].update(ciphertext='00'*31)),
            ('bad-mac', lambda x:x['crypto'].update(mac='00'*32)),
            ('short-mac', lambda x:x['crypto'].update(mac='00')),
            ('dual-crypto', lambda x:x.update(Crypto=copy.deepcopy(x['crypto']))),
        ]:
            reject(name,mutate)
        for name, field, value in [('scrypt-n', 'n',3), ('scrypt-zero-r','r',0),
                                    ('scrypt-huge-n','n',2**63), ('scrypt-huge-p','p',2**63)]:
            item=copy.deepcopy(OFFICIAL['scrypt'])
            item['crypto']['kdfparams'][field]=value
            probe(write_private(directory/(name+'.json'),item), PASSWORD,expected='official',success=False)
        valid = json.dumps(generated_keystore('PUBLIC_PTY_PASSWORD'))
        for name, text in [('truncated',valid[:-2]), ('duplicate-version',valid[:-1]+',"version":3}'),
                           ('trailing',valid+' false'), ('oversized',' '*65537),
                           ('duplicate-kdf',valid.replace('"kdf": "pbkdf2"','"kdf":"pbkdf2","kdf":"pbkdf2"')),
                           ('escaped-crypto',valid.replace('"crypto"','"\\u0063rypto"')),
                           ('escaped-crypto-duplicate',valid[:-1]+',"\\u0063rypto":{}}'),
                           ('integer-overflow',valid.replace('"c": 2048','"c": 18446744073709551616'))]:
            probe(write_private(directory/(name+'.json'),text),'PUBLIC_PTY_PASSWORD',success=False)
        changed = write_private(directory/'changed-source.json',valid)
        replacement = write_private(directory/'replacement.json',valid+'\n')
        invoke(['replace',changed,pwd_file,replacement],contains='PASS: changed encrypted keystore')

        # Foundry-generated v3 keystore, with a deliberately public key and password.
        cast=shutil.which('cast')
        if cast:
            cast_dir=directory/'cast'
            cast_dir.mkdir(mode=0o700)
            subprocess.run([cast,'wallet','import','public-one','--keystore-dir',str(cast_dir),
                            '--private-key',PUBLIC_KEY_ONE,'--unsafe-password','PUBLIC_FOUNDRY_PASSWORD'],
                           capture_output=True,check=True,timeout=40)
            cast_file=cast_dir/'public-one'
            cast_file.chmod(0o600)
            foundry = json.loads(cast_file.read_text())
            crypto = foundry.get('crypto', foundry.get('Crypto'))
            assert crypto['kdf'] == 'scrypt' and crypto['kdfparams']['n'] >= 8192
            probe(cast_file,'PUBLIC_FOUNDRY_PASSWORD')

        run_terminal(encrypted,b'PUBLIC_PTY_PASSWORD\nSEND\n',True)
        run_terminal(encrypted,b'PUBLIC_PTY_PASSWORD'+'🔐'.encode()+b'\x7f\nSEND\n',True)
        run_terminal(encrypted,'discard pāss🔐'.encode()+b'\x15PUBLIC_PTY_PASSWORD\n',True)
        run_terminal(boundary,b'P'*1024+b'\nSEND\n',True)
        run_terminal(boundary,b'P'*1025+b'\n')
        run_terminal(encrypted,SENTINEL.encode()+b'\n')
        run_terminal(encrypted,b'\x04')
        for sig in [signal.SIGINT,signal.SIGTERM,signal.SIGHUP,signal.SIGQUIT]:
            run_terminal(encrypted,b'',interrupt=sig)
        run_terminal(encrypted,b'X'*1100+b'\n')
        probe(encrypted,noninteractive=False,success=False,contains='No interactive terminal')
        cli_admission(directory,encrypted,pwd_file)
        print('PASS: encrypted keyfile vectors, guarded unlock/signing, password sources, CLI admission and hidden PTY checks')
    finally:
        shutil.rmtree(directory)


if __name__ == '__main__':
    main()
