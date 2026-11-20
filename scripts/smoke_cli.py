#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Exercise the contributor CLI and official-worker boundaries without live automation.

Default checks use local sources, fake providers and fake GitHub. --online only reads
GitHub. --package builds and tests fresh distributions (package downloads may be needed).
--sandbox requires the approved bubblewrap binary and an explicit Lean toolchain.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import tempfile
import time

from smoke_process import run_owned

ROOT = Path(__file__).resolve().parents[1]
SUITES = (
    'test_project_cli', 'test_worker', 'test_worker_loop',
    'test_worker_round', 'test_review_records', 'test_merge_controller',
    'test_cli_smoke',
)
FEATURE_SUITES = {'worker_checks': 'test_worker_checks', 'authoring': 'test_authoring'}


def fixture_suites(root):
    """Independent infra branches can land in either order; installed features need tests."""
    suites = list(SUITES)
    for module, suite in FEATURE_SUITES.items():
        source = root / 'tools/project/sphereceti' / f'{module}.py'
        test = root / 'tests' / f'{suite}.py'
        if source.is_file() != test.is_file():
            raise ValueError(f'incomplete smoke feature inventory: {module} requires {suite}')
        if source.is_file():
            suites.append(suite)
    return suites


def python_command(body: str) -> list[str]:
    # Ignore the caller's PYTHONPATH and import the checkout being tested explicitly.
    prelude = f'import sys; sys.path[:0] = {list(map(str, (ROOT / "tools/project", ROOT / "tests")))!r}; '
    return [sys.executable, '-I', '-c', prelude + body]


def run_step(name, command, output, timeout, *, validate=None):
    log = output / f'{name}.log'
    started = time.monotonic()
    result = {'name': name, 'command': command, 'log': str(log), 'state': 'failed',
              'cleanup_verified': False}
    try:
        with log.open('x') as stream:
            result.update(run_owned(command, cwd=ROOT, stdout=stream, timeout=timeout))
        if 'reason' in result:
            pass
        elif result['exit_code'] != 0:
            result['reason'] = 'command failed; inspect the stage log'
        else:
            if validate:
                validate(log.read_text())
            result['state'] = 'passed'
    except (OSError, ValueError, RuntimeError, AssertionError, KeyError, TypeError) as error:
        result['reason'] = str(error)
    finally:
        result['seconds'] = round(time.monotonic() - started, 2)
    return result


def check_status(raw, *, online=False):
    report = json.loads(raw)
    expected = 'available' if online else 'not_checked'
    if report['queue']['state'] != expected:
        raise ValueError(f'queue state must be {expected}')
    if report['setup']['merging_ready'] or report['setup']['state'] != 'not_verified':
        raise ValueError('diagnostics must not claim verified merge activation')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--online', action='store_true', help='also test the real read-only GitHub query')
    parser.add_argument('--package', action='store_true', help='build and test wheel/source installs; needs uv')
    parser.add_argument('--sandbox', action='store_true', help='also run the disposable Lean isolation smoke')
    parser.add_argument('--toolchain', type=Path, help='exact installed Lean toolchain for --sandbox')
    parser.add_argument('--output', type=Path, help='new directory for report.json and per-stage logs')
    parser.add_argument('--timeout-seconds', type=int, default=600, help='per-stage deadline, 30–1800 seconds')
    args = parser.parse_args(argv)
    if not 30 <= args.timeout_seconds <= 1800:
        parser.error('--timeout-seconds must be between 30 and 1800')
    if args.sandbox != (args.toolchain is not None):
        parser.error('--sandbox and --toolchain must be supplied together')
    try:
        suites = fixture_suites(ROOT)
    except ValueError as error:
        parser.error(str(error))
    output = args.output.expanduser().absolute() if args.output else Path(tempfile.mkdtemp(prefix='sphereceti-cli-smoke-'))
    if args.output:
        output.mkdir(parents=True, exist_ok=False)
    stages = []

    def step(name, command, **kwargs):
        result = run_step(name, command, output, args.timeout_seconds, **kwargs)
        stages.append(result)
        print(f'{name}: {result["state"]}', file=sys.stderr, flush=True)
        return result['state'] == 'passed'

    cli = 'from sphereceti.cli import main; raise SystemExit(main({args!r}))'
    step('offline-status', python_command(cli.format(args=['status', '--offline', '--json'])), validate=check_status)
    step('fixture-pipeline', python_command(
        f'import unittest; unittest.main(module=None, argv={["smoke", *suites]!r})'))
    if args.online:
        step('github-read', python_command(cli.format(args=['status', '--json'])),
             validate=lambda raw: check_status(raw, online=True))
    if args.package:
        if step('package-lock', ['uv', 'lock', '--check']):
            if step('package-build', ['uv', 'build']):
                step('package-install', [sys.executable, str(ROOT / 'scripts/test_package.py')])
    if args.sandbox:
        step('sandbox', [sys.executable, '-I', str(ROOT / 'scripts/test_sandbox_smoke.py'),
                         '--toolchain', str(args.toolchain.expanduser().resolve())])
    report = {
        'schema': 'sphereceti.cli-smoke/v1',
        'state': 'passed' if all(s['state'] == 'passed' for s in stages) else 'failed',
        'checkout': str(ROOT), 'output': str(output), 'stages': stages,
        'not_run': [name for name, enabled in (('github-read', args.online),
                    ('package-install', args.package), ('sandbox', args.sandbox)) if not enabled],
        'live_review_exercised': False, 'live_merge_exercised': False,
        'activation_verified': False,
    }
    (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    return int(report['state'] != 'passed')


if __name__ == '__main__':
    raise SystemExit(main())
