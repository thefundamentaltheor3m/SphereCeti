"""Pinned bubblewrap launcher adapted from TauCeti's approved PR workflow.

TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5,
.github/workflows/pr-build.yml (Apache-2.0; TauCeti contributors).
Keep the clean launcher environment, explicit namespaces, immutable PATH, read-only
synthetic root, separately mounted tools, and fail-closed probes from that design.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import secrets
from pathlib import Path
import socket
import subprocess
import sys
import tempfile


class SandboxError(RuntimeError):
    pass


class Sandbox:
    def __init__(self, gate: Path, candidate: Path, toolchain: Path):
        self.gate = gate.resolve()
        self.candidate = candidate.resolve()
        self.toolchain = toolchain.resolve()
        lake_dir = self.candidate / '.lake'
        if lake_dir.is_symlink() or not lake_dir.is_dir():
            raise SandboxError('candidate .lake must be a real, precreated directory')
        pin = json.loads((self.gate / 'tools/ci/bubblewrap.json').read_text())
        if hashlib.sha256(Path('/usr/bin/bwrap').read_bytes()).hexdigest() != pin['binary_sha256']:
            raise SandboxError('bubblewrap binary differs from approved pin; refusing candidate execution')

    def argv(self, command: list[str]) -> list[str]:
        return [
            '/usr/bin/bwrap', '--tmpfs', '/',
            '--ro-bind', '/usr', '/usr', '--ro-bind', '/etc', '/etc',
            '--symlink', 'usr/bin', '/bin', '--symlink', 'usr/sbin', '/sbin',
            '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
            '--dev', '/dev', '--proc', '/proc', '--tmpfs', '/tmp',
            '--dir', '/home/sandbox',
            '--ro-bind', str(self.toolchain), '/toolchain',
            '--ro-bind', str(self.gate), '/gate',
            '--ro-bind', str(self.candidate), '/project',
            '--bind', str(self.candidate / '.lake'), '/project/.lake',
            '--remount-ro', '/',
            '--setenv', 'PATH', '/toolchain/bin:/usr/bin:/bin',
            '--setenv', 'HOME', '/home/sandbox',
            '--setenv', 'LAKE_NO_CACHE', 'true',
            '--setenv', 'LAKE_ARTIFACT_CACHE', 'false',
            '--chdir', '/project',
            '--unshare-user', '--unshare-ipc', '--unshare-pid', '--unshare-net',
            '--unshare-uts', '--unshare-cgroup', '--disable-userns',
            '--die-with-parent', '--new-session', '--', *command,
        ]

    def run(self, command: list[str], timeout: int = 60) -> subprocess.CompletedProcess:
        # Empty *launcher* environment, not merely bwrap --clearenv: PID 1 must have no secrets.
        # Buffer candidate output: never let candidate workflow commands reach the Actions parser.
        return subprocess.run(self.argv(command), env={}, text=True, capture_output=True, timeout=timeout)

    def probe(self) -> None:
        ok = self.run(['/usr/bin/true'])
        if ok.returncode:
            raise SandboxError(f'sandbox cannot start: {ok.stderr.strip()}; refusing candidate execution')
        host_user = os.readlink('/proc/self/ns/user')
        host_net = os.readlink('/proc/self/ns/net')
        with tempfile.NamedTemporaryFile(prefix='sphereceti-host-canary-') as canary, \
                socket.socket() as listener:
            canary.write(b'host-only test data')
            canary.flush()
            listener.bind(('127.0.0.1', 0))
            listener.listen()
            port = listener.getsockname()[1]
            with socket.create_connection(('127.0.0.1', port), timeout=2):
                pass
            code = '''
import os, pathlib, socket, sys
host_file, host_user, host_net, port = sys.argv[1:]
assert os.readlink('/proc/self/ns/user') != host_user
assert os.readlink('/proc/self/ns/net') != host_net
assert pathlib.Path('/proc/1/environ').read_bytes() == b''
assert not pathlib.Path(host_file).exists()
for path in ('/gate/sandbox-probe', '/project/sandbox-probe', '/etc/sandbox-probe', '/sandbox-probe'):
    try:
        pathlib.Path(path).write_text('should be denied')
    except OSError:
        pass
    else:
        raise RuntimeError('write escaped: ' + path)
try:
    socket.create_connection(('127.0.0.1', int(port)), timeout=2)
except OSError:
    pass
else:
    raise RuntimeError('host network reachable')
p = pathlib.Path('/project/.lake/sandbox-probe')
p.write_text('permitted build output')
p.unlink()
'''
            result = self.run(['/usr/bin/python3', '-I', '-c', code,
                               canary.name, host_user, host_net, str(port)])
            if result.returncode:
                raise SandboxError(f'sandbox probe failed: {result.stderr.strip()}; refusing candidate execution')
        nested = self.run(['/usr/bin/unshare', '--user', '--map-root-user', '/usr/bin/true'])
        if nested.returncode == 0:
            raise SandboxError('nested user namespace permitted; refusing candidate execution')

    def build(self) -> subprocess.CompletedProcess:
        self.probe()
        return self.run(['/usr/bin/bash', '/gate/scripts/sandbox-build.sh'], timeout=1800)


def emit_candidate_output(output: str) -> None:
    # Generate the resume token only AFTER the candidate exits; it cannot guess or read it.
    token = secrets.token_hex(32)
    print(f'::stop-commands::{token}', flush=True)
    for line in output.splitlines():
        print('sandbox | ' + line)
    print(f'::{token}::', flush=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gate', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--toolchain', type=Path, required=True)
    args = parser.parse_args()
    try:
        result = Sandbox(args.gate, args.candidate, args.toolchain).build()
        emit_candidate_output(result.stdout + result.stderr)
        return result.returncode
    except (SandboxError, OSError, ValueError, subprocess.SubprocessError) as error:
        emit_candidate_output(f'sandbox: {error}')
        return 1


if __name__ == '__main__':
    sys.exit(main())
