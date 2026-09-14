"""Offline measurement using #6's sandbox and host-owned GNU time counters.

Adapted from TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5,
scripts/perf/measure.py (Apache-2.0; TauCeti contributors). No candidate log or
writable build artifact is read by the host. Dependencies are operator-prepared.
"""
from __future__ import annotations

import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import time
import uuid

from .gate import GateError, blob, git, tree
from .profiling import markdown, plan, summarize
from .sandbox import Sandbox

FILES = ('__init__.py', 'cli.py', 'config.py', 'gate.py', 'sandbox.py',
         'profiling.py', 'profile_runner.py')


def verify_tools(repo: Path, tooling: str) -> None:
    entries = tree(repo, tooling)
    for name in FILES:
        path = 'tools/project/sphereceti/' + name
        if path not in entries or blob(repo, entries[path]) != Path(__file__).with_name(name).read_bytes():
            raise GateError(f'installed profiler differs from tooling revision: {name}')


def materialize(repo: Path, sha: str, destination: Path) -> None:
    destination.mkdir()
    for path, entry in tree(repo, sha).items():
        target = destination / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(blob(repo, entry))
        target.chmod(0o755 if entry.mode == '100755' else 0o644)
    (destination / '.lake' / 'packages').mkdir(parents=True)


def verify_dependencies(repo: Path, tooling: str, directory: Path) -> None:
    """Same tracked-source/pin contract as #6; built dependency artifacts are trusted inputs."""
    manifest = json.loads(blob(repo, tree(repo, tooling)['lake-manifest.json']))
    if manifest['packagesDir'] != '.lake/packages':
        raise GateError('unsupported dependency layout')
    for package in manifest['packages']:
        if (package['type'] != 'git' or not re.fullmatch(r'[A-Za-z0-9_-]+', package['name'])
                or not re.fullmatch(r'[0-9a-f]{40}', package['rev'])):
            raise GateError('dependencies must be exact Git packages')
        root = directory / package['name']
        if root.is_symlink() or not root.is_dir():
            raise GateError('dependency must be an ordinary directory')
        if git(root, 'rev-parse', 'HEAD').decode().strip() != package['rev']:
            raise GateError(f"dependency revision mismatch: {package['name']}")
        if git(root, 'status', '--porcelain', '--untracked-files=no').strip():
            raise GateError(f"dirty dependency sources: {package['name']}")


class ProfileSandbox(Sandbox):
    def __init__(self, gate: Path, candidate: Path, toolchain: Path, dependencies: Path):
        super().__init__(gate, candidate, toolchain)
        self.dependencies = dependencies.resolve()

    def argv(self, command: list[str]) -> list[str]:
        args = super().argv(command)
        position = args.index('--remount-ro')
        args[position:position] = ['--ro-bind', str(self.dependencies), '/project/.lake/packages']
        return args


def run_host(command: list[str], timeout: float) -> int:
    # No inherited credentials, candidate stdout, or workflow-command processing.
    process = subprocess.Popen(command, env={}, stdout=subprocess.DEVNULL,
                               stderr=subprocess.DEVNULL, start_new_session=True)
    try:
        return process.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        # Kill the GNU time wrapper and bwrap; destroying bwrap's PID namespace
        # also kills candidate descendants, including their separate session.
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()
        return 124
    except BaseException:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()
        raise


def counter(path: Path) -> float:
    # This file is written by host GNU time OUTSIDE all sandbox mounts.
    value = path.read_text().strip().split()
    if len(value) != 2:
        raise ValueError('missing CPU counters')
    numbers = [float(item) for item in value]
    if not all(math.isfinite(item) and item >= 0 for item in numbers):
        raise ValueError('invalid CPU counters')
    return sum(numbers)


def measure(box: ProfileSandbox, path: str, raw: Path, timeout: float) -> dict:
    # Direct re-elaboration forces work even when the module's .olean is cached.
    # No -o: this invocation does not replace the prebuilt environment for later files.
    command = box.argv(['/toolchain/bin/lake', 'env', '/toolchain/bin/lean', '-j1', path])
    started = time.monotonic()
    code = run_host(['/usr/bin/time', '--quiet', '--format', '%U %S', '--output', str(raw),
                     '--', *command], timeout)
    elapsed = time.monotonic() - started
    try:
        cpu = counter(raw) if code == 0 else None
    except (OSError, ValueError):
        cpu = None
    return {'status': 'ok' if code == 0 and cpu is not None else 'failed',
            'returncode': code, 'cpu_seconds': cpu, 'wall_seconds': elapsed}


def run(repo: Path, tooling: str, base: str, head: str, workspace: Path,
        toolchain: Path, dependencies: Path) -> dict:
    manifest = plan(repo, tooling, base, head)
    verify_tools(repo, tooling)
    dependencies, toolchain = dependencies.resolve(), toolchain.resolve()
    workspace = workspace.absolute()
    for mounted in (dependencies, toolchain):
        resolved = workspace.resolve()
        if resolved == mounted or resolved in mounted.parents or mounted in resolved.parents:
            raise GateError('workspace must be disjoint from dependency and toolchain mounts')
    # Existing state is never replayed or overwritten; measurements get a fresh run identity.
    if workspace.exists() or workspace.is_symlink():
        raise GateError('profile workspace must be new')
    if not dependencies.is_dir():
        raise GateError('missing prepared dependencies')
    verify_dependencies(repo, tooling, dependencies)
    version = subprocess.check_output([str(toolchain / 'bin/lean'), '--version'],
                                      env={}, text=True, timeout=10)
    expected = manifest['lean'].removeprefix('leanprover/lean4:v')
    if not version.startswith(f'Lean (version {expected},'):
        raise GateError('toolchain version differs from profiling plan')
    workspace.mkdir(parents=True)
    run_id = uuid.uuid4().hex
    (workspace / 'plan.json').write_text(json.dumps(manifest, indent=2) + '\n')
    raw = workspace / 'raw'
    raw.mkdir()
    # Only the pin is needed by the shared launcher. Neither raw counters nor reports
    # live below this mount. The candidate cannot replace this host-owned file.
    gate = workspace / 'gate'
    (gate / 'tools/ci').mkdir(parents=True)
    entries = tree(repo, tooling)
    (gate / 'tools/ci/bubblewrap.json').write_bytes(blob(repo, entries['tools/ci/bubblewrap.json']))
    samples = []
    deadline = time.monotonic() + 1800
    for side in ('base', 'head'):
        selected = [entry for entry in manifest['changes'] if entry[side + '_blob'] is not None]
        if not selected:
            continue
        revision = manifest['diff_base' if side == 'base' else 'head']
        candidate = workspace / side
        materialize(repo, revision, candidate)
        box = ProfileSandbox(gate, candidate, toolchain, dependencies)
        box.probe()
        # Build each side's environment independently, using read-only prebuilt dependencies.
        modules = [entry['path'].removesuffix('.lean').replace('/', '.') for entry in selected]
        remaining = deadline - time.monotonic()
        prebuild = run_host(box.argv(['/toolchain/bin/lake', 'build', *modules]),
                            min(900, remaining)) if remaining > 0 else 124
        for index, entry in enumerate(selected):
            remaining = deadline - time.monotonic()
            result = (measure(box, entry['path'], raw / f'{side}-{index}.time', min(300, remaining))
                      if prebuild == 0 and remaining > 0 else
                      {'status': 'prebuild_failed' if prebuild else 'deadline_exceeded',
                       'returncode': prebuild or 124, 'cpu_seconds': None, 'wall_seconds': None})
            samples.append({**result, 'path': entry['path'], 'side': side, 'revision': revision,
                            'run_id': run_id, 'plan_digest': manifest['plan_digest']})
    report = summarize(manifest, samples, run_id)
    report['environment'] = {'platform': platform.platform(), 'machine': platform.machine(),
                             'lean_version': version.strip(), 'dependency_artifacts': 'operator_prepared',
                             'lean_binary_sha256': hashlib.sha256((toolchain / 'bin/lean').read_bytes()).hexdigest(),
                             'lake_binary_sha256': hashlib.sha256((toolchain / 'bin/lake').read_bytes()).hexdigest()}
    report['limits'] = {'max_modules': 32, 'prebuild_seconds': 900, 'sample_seconds': 300,
                        'measurement_seconds': 1800, 'lean_threads': 1}
    (workspace / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    (workspace / 'report.md').write_text(markdown(report))
    return report
