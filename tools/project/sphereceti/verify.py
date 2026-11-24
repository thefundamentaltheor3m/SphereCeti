"""`sphereceti verify`: the author's one-command proof check, run in a SphereCeti checkout.

Every check reuses what CI already runs, from the checkout being verified (the ordinary `CI`
workflow's `build` job also runs the candidate's own scripts):

* roadmap contracts: `python3 -I scripts/check_roadmap.py`;
* build: `lake build` of the changed modules (`+Module`), the library (`@/SphereCeti`) when its
  root changed, or the default targets when no Lean source changed;
* module boundaries: `lake env python3 -I scripts/check_modules.py --json`;
* library root: `SphereCeti.lean` is unchanged from the merge base. Proof PRs never edit it; the
  `SphereCeti.*` Lake glob builds every topic module, `scripts/check_roadmap.py` rejects topic
  imports in the root, and the auto-approval decision routes any root edit to human review;
* compiled audit: `lake env python3 -I scripts/check_audits.py --report ...`, whose verdict
  is read back to list new admissions and other regressions against `policy/audits.json`.

This is advisory. It is not the trusted build, which runs approved main's tooling and policy on
the exact PR head in a sandbox. Nothing here posts, pushes, fetches or calls a model provider.
It never writes to the repository.
"""
from __future__ import annotations

import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

SCHEMA = 'sphereceti.verify/v1'
STEPS = ('changes', 'roadmap', 'build', 'boundaries', 'root_imports', 'audit')
ROOT_MODULE = 'SphereCeti.lean'
CONFIG = ('lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain')
SCRIPTS = ('check_roadmap.py', 'check_modules.py', 'check_audits.py')
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
# Lean/Lake diagnostics: `error: ././SphereCeti/Foo.lean:12:4: message`.
LOCATION = re.compile(r"^(?:[^\s:]*\s)?(error|warning): (?:\./)*(\S+?\.lean):(\d+):(\d+): (.*)$",
                      re.MULTILINE)
BUILD_TIMEOUT = 3600   # check_audits.BUILD_TIMEOUT
AUDIT_TIMEOUT = 4 * 3600
CACHE_GUIDANCE = ('Run `lake exe cache get` in this checkout (CONTRIBUTING.md#building), '
                  'then rerun `sphereceti verify`.')


class EnvironmentProblem(RuntimeError):
    """The checkout or toolchain cannot run the checks (exit 2)."""

    def __init__(self, message: str, guidance: str):
        super().__init__(message)
        self.guidance = guidance


def add_parser(commands):
    p = commands.add_parser(
        'verify', help="check this checkout's proof changes the way CI does (build, root imports, "
                       'compiled audit, module boundaries)')
    p.add_argument('--repo', type=Path, default=Path.cwd(), help='SphereCeti checkout (default: current directory)')
    p.add_argument('--base', default='origin/main',
                   help='compare against the merge base with this ref (default: origin/main)')
    p.add_argument('--module', action='append', default=[], metavar='MODULE',
                   help='build these modules instead of the changed ones (repeatable)')
    p.add_argument('--skip-audit', action='store_true',
                   help='skip the full compiled audit; the result is then incomplete, never a pass')
    p.add_argument('--json', action='store_true', help=f'emit the {SCHEMA} report')


# ---------------------------------------------------------------------------------------------
# Small process helpers


def progress(message: str) -> None:
    """Progress goes to stderr only; with --json, stdout carries exactly one JSON document."""
    print(f'verify: {message}', file=sys.stderr, flush=True)


def _run(command, cwd, *, timeout, env=None):
    progress('running ' + ' '.join(str(part) for part in command))
    started = time.monotonic()
    try:
        result = subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True,
                                timeout=timeout, check=False)
    except FileNotFoundError as error:
        raise EnvironmentProblem(f'cannot execute {command[0]}: {error.strerror}',
                                 'Install the pinned toolchain (elan; see CONTRIBUTING.md#building).') from error
    except subprocess.TimeoutExpired as error:
        out = (error.stdout or '') if isinstance(error.stdout, str) else ''
        return subprocess.CompletedProcess(command, 124, out, f'timed out after {timeout}s'), time.monotonic() - started
    return result, time.monotonic() - started


def _git(root: Path, *args: str) -> str:
    result = subprocess.run(['git', '-C', str(root), *args], text=True, capture_output=True, check=False)
    if result.returncode:
        raise EnvironmentProblem(f"git {args[0]} failed: {result.stderr.strip() or 'no diagnostic'}",
                                 'Run inside a SphereCeti Git checkout.')
    return result.stdout


def _tail(text: str, lines: int = 20) -> str:
    return '\n'.join(text.strip().splitlines()[-lines:])


def locations(text: str, *, severities=('error',)) -> list[dict]:
    """Lean/Lake `file:line:column` diagnostics in a build log, first line of each message."""
    found, seen = [], set()
    for match in LOCATION.finditer(text):
        severity, path, line, column, message = match.groups()
        item = (path, int(line), int(column), message)
        if severity in severities and item not in seen:
            seen.add(item)
            found.append({'file': path, 'line': int(line), 'column': int(column), 'message': message.strip()})
    return found


# ---------------------------------------------------------------------------------------------
# Environment


def checkout(repo: Path) -> Path:
    try:
        top = subprocess.run(['git', '-C', str(repo), 'rev-parse', '--show-toplevel'], text=True,
                             capture_output=True, check=False)
    except FileNotFoundError as error:
        raise EnvironmentProblem('git is not installed', 'Install git.') from error
    if top.returncode:
        raise EnvironmentProblem(f'{repo} is not a Git checkout', 'Run inside a SphereCeti checkout or pass --repo.')
    root = Path(top.stdout.strip())
    lakefile = root / 'lakefile.toml'
    if (not lakefile.is_file() or not re.search(r'^name\s*=\s*"SphereCeti"\s*$', lakefile.read_text(), re.MULTILINE)
            or not (root / ROOT_MODULE).is_file()):
        raise EnvironmentProblem(f'{root} is not a SphereCeti checkout (no SphereCeti lakefile.toml and {ROOT_MODULE})',
                                 'Run inside a SphereCeti checkout or pass --repo.')
    missing = [name for name in SCRIPTS if not (root / 'scripts' / name).is_file()]
    if missing:
        raise EnvironmentProblem(f"this checkout lacks CI's scripts/{', scripts/'.join(missing)}",
                                 'Rebase onto current origin/main, which carries the CI checks verify reuses.')
    return root


def environment(root: Path) -> dict:
    """Locate Lake and confirm the pinned dependencies and Mathlib cache are present."""
    lake = shutil.which('lake')
    if not lake:
        raise EnvironmentProblem('lake is not on PATH',
                                 'Install elan and the pinned toolchain (`bash scripts/install_lean.sh '
                                 '--toolchain-only`, or elan per CONTRIBUTING.md#building), then '
                                 '`lake exe cache get`.')
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    packages_dir = root / manifest.get('packagesDir', '.lake/packages')
    notes = []
    for package in manifest.get('packages', []):
        if package.get('type') != 'git':
            continue
        name, rev = package['name'], package['rev']
        directory = packages_dir / name
        if not directory.is_dir():
            raise EnvironmentProblem(f'pinned dependency {name} is not fetched ({directory} is missing)', CACHE_GUIDANCE)
        head = subprocess.run(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True,
                              capture_output=True, check=False).stdout.strip()
        if head != rev:
            raise EnvironmentProblem(f'dependency {name} is at {head or "an unknown revision"}, '
                                     f'but lake-manifest.json pins {rev}', CACHE_GUIDANCE)
    mathlib = packages_dir / 'mathlib/.lake/build/lib/lean/Mathlib.olean'
    if any(p.get('name') == 'mathlib' for p in manifest.get('packages', [])) and not mathlib.is_file():
        raise EnvironmentProblem('the Mathlib build cache is missing (no Mathlib.olean); '
                                 'a build would compile Mathlib from source', CACHE_GUIDANCE)
    tauceti = packages_dir / 'TauCeti/.lake/build/lib/lean'
    if (packages_dir / 'TauCeti').is_dir() and not tauceti.is_dir():
        notes.append('TauCeti has no local build outputs; the first build compiles the imported TauCeti '
                     'modules from source (CI fetches its cache map with scripts/prepare_cache.sh).')
    return {'ok': True, 'lake': lake, 'packages_dir': str(packages_dir), 'notes': notes}


# ---------------------------------------------------------------------------------------------
# Step 1: affected modules


def module_kind(path: str) -> str:
    parts = Path(path).with_suffix('').parts
    if parts[0] == 'SphereCeti':
        return 'library'
    if parts[0] == 'SphereCetiRoadmap':
        return 'roadmap'
    if len(parts) > 1 and parts[0] == 'scripts':
        return 'tooling'
    if len(parts) > 2 and parts[:2] == ('tests', 'fixtures'):
        return 'fixture'
    return 'unclassified'


def module_name(path: str) -> str:
    return '.'.join(Path(path).with_suffix('').parts)


def changes(root: Path, base: str, explicit: list[str]) -> dict:
    head = _git(root, 'rev-parse', 'HEAD').strip()
    if subprocess.run(['git', '-C', str(root), 'rev-parse', '--verify', '--quiet', base + '^{commit}'],
                      capture_output=True, check=False).returncode:
        raise EnvironmentProblem(f'base {base!r} is not a commit in this checkout',
                                 'Run `git fetch origin` (or pass --base REF).')
    merge_base = _git(root, 'merge-base', base, 'HEAD').strip()
    status = {}
    # Working tree against the merge base: what Lake builds is what verify reports.
    records = _git(root, 'diff', '--name-status', '--no-renames', '-z', merge_base, '--').split('\0')
    for flag, path in zip(records[0::2], records[1::2]):
        if path:
            status[path] = {'A': 'added', 'D': 'deleted'}.get(flag[:1], 'modified')
    for path in _git(root, 'ls-files', '--others', '--exclude-standard', '-z').split('\0'):
        if path:
            status[path] = 'added'
    lean = {p: s for p, s in status.items() if p.endswith('.lean')}
    report = {
        'selection': 'explicit' if explicit else 'changed',
        'base': base, 'merge_base': merge_base, 'head': head,
        'dirty': bool(_git(root, 'status', '--porcelain', '--untracked-files=normal').strip()),
        'changed_paths': [{'path': p, 'status': status[p]} for p in sorted(status)],
        'library': [], 'roadmap': [], 'other_lean': [], 'deleted': [], 'added_library': [],
        'config_changed': sorted(p for p in status if p in CONFIG),
        'policy_changed': 'policy/audits.json' in status,
        'build_targets': [],
    }
    for path, state in sorted(lean.items()):
        kind, name = module_kind(path), module_name(path)
        if state == 'deleted':
            report['deleted'].append(name)
        elif kind in ('library', 'roadmap'):
            report[kind].append(name)
            if kind == 'library' and state == 'added' and path != ROOT_MODULE:
                report['added_library'].append(name)
        else:
            report['other_lean'].append(name)
    if explicit:
        for name in explicit:
            if not MODULE.fullmatch(name) or not (root / (name.replace('.', '/') + '.lean')).is_file():
                raise EnvironmentProblem(f'--module {name!r} names no Lean source in this checkout',
                                         'Pass a module name such as SphereCeti.Analysis.ExactZeroOrder.')
        report['build_targets'] = [{'target': '+' + n, 'reason': 'requested'} for n in dict.fromkeys(explicit)]
        return report
    targets = []
    deleted_kinds = {module_kind(n.replace('.', '/') + '.lean') for n in report['deleted']}
    if report['config_changed']:
        targets.append({'target': None, 'reason': 'dependency configuration changed; default targets'})
    else:
        for library, aggregator in (('library', 'SphereCeti'), ('roadmap', 'SphereCetiRoadmap')):
            if aggregator in report[library] or library in deleted_kinds:
                why = 'library root changed' if aggregator in report[library] else 'a module was deleted'
                targets.append({'target': '@/' + aggregator, 'reason': why})
            else:
                targets += [{'target': '+' + n, 'reason': 'changed'} for n in report[library]]
        if not targets:
            targets.append({'target': None, 'reason': 'no changed library or roadmap module; default targets'})
    report['build_targets'] = targets
    return report


# ---------------------------------------------------------------------------------------------
# Steps


def step(name, status, summary, *, seconds=0.0, command=None, failures=(), details=None):
    return {'name': name, 'status': status, 'summary': summary, 'seconds': round(seconds, 2),
            'command': command, 'failures': list(failures), 'details': details or {}}


def skipped(name, reason):
    return step(name, 'skipped', reason)


def roadmap_step(root: Path) -> dict:
    command = [sys.executable, '-I', 'scripts/check_roadmap.py']
    result, seconds = _run(command, root, timeout=300)
    output = result.stdout + result.stderr
    if result.returncode == 0:
        return step('roadmap', 'pass', _tail(result.stdout, 1) or 'roadmap static checks: OK',
                    seconds=seconds, command=command)
    failures = [{'message': line[len('ERROR: '):]} for line in output.splitlines() if line.startswith('ERROR: ')]
    return step('roadmap', 'fail', failures[0]['message'] if failures else _tail(output, 1),
                seconds=seconds, command=command, failures=failures or [{'message': _tail(output)}])


def build_step(root: Path, modules: dict) -> dict:
    total, failures, ran = 0.0, [], []
    for item in modules['build_targets']:
        command = ['lake', 'build'] + ([item['target']] if item['target'] else [])
        result, seconds = _run(command, root, timeout=BUILD_TIMEOUT)
        total += seconds
        output = result.stdout + result.stderr
        ran.append({'target': item['target'] or '(default)', 'reason': item['reason'],
                    'exit_code': result.returncode, 'seconds': round(seconds, 2)})
        if result.returncode:
            # Lake's log is progress, never part of the report stream.
            sys.stderr.write(_inert(_tail(output, 40)) + '\n')
            found = locations(output)
            failures += [{'target': item['target'] or '(default)', **f} for f in found] or [
                {'target': item['target'] or '(default)', 'message': _tail(output)}]
    names = ', '.join(r['target'] for r in ran)
    if failures:
        first = failures[0]
        where = f"{first['file']}:{first['line']}:{first['column']}: " if 'file' in first else ''
        return step('build', 'fail', f"{where}{first['message'].splitlines()[0]}", seconds=total,
                    command=['lake', 'build', '<target>'], failures=failures, details={'targets': ran})
    return step('build', 'pass', f'built {names}', seconds=total, command=['lake', 'build', '<target>'],
                details={'targets': ran})


def boundaries_step(root: Path) -> tuple[dict, list | None]:
    command = ['lake', 'env', sys.executable, '-I', 'scripts/check_modules.py', '--json']
    result, seconds = _run(command, root, timeout=1800)
    if result.returncode:
        message = result.stderr.strip().removeprefix('module boundaries: ') or _tail(result.stdout)
        failure = {'message': message}
        match = re.match(r'(?:forbidden import|missing import source|import outside inventory): (\S+)', message)
        if match:
            failure['file'] = match[1].replace('.', '/') + '.lean'
        return step('boundaries', 'fail', message.splitlines()[0], seconds=seconds, command=command,
                    failures=[failure]), None
    try:
        modules = json.loads(result.stdout)['modules']
    except (ValueError, KeyError, TypeError):
        return step('boundaries', 'fail', 'check_modules.py printed no module inventory', seconds=seconds,
                    command=command, failures=[{'message': _tail(result.stdout + result.stderr)}]), None
    return step('boundaries', 'pass', f'{len(modules)} modules checked; no forbidden imports',
                seconds=seconds, command=command), modules


def _blob(root: Path, oid: str) -> bytes:
    return subprocess.run(['git', '-C', str(root), 'cat-file', 'blob', oid], capture_output=True,
                          check=True).stdout


def root_step(root: Path, modules: dict) -> dict:
    """Proof PRs never edit SphereCeti.lean: the `SphereCeti.*` Lake glob builds every topic module.

    The same rule as the auto-approval decision (any root edit needs human review) and as the
    checkout's `scripts/check_roadmap.py` (the root imports only its stable scaffold).
    """
    from .gate import tree
    progress('checking that the library root is unchanged')
    started = time.monotonic()
    base_entry = tree(root, modules['merge_base']).get(ROOT_MODULE)
    unchanged = base_entry is not None and (root / ROOT_MODULE).read_bytes() == _blob(root, base_entry.oid)
    new = modules['added_library']
    details = {'root_changed': not unchanged, 'new_modules': new}
    if unchanged:
        summary = f'{ROOT_MODULE} unchanged' + (
            f'; {len(new)} new module(s) built by the SphereCeti.* glob' if new else '')
        return step('root_imports', 'pass', summary, seconds=time.monotonic() - started, details=details)
    message = (f'{ROOT_MODULE} changed: proof PRs do not edit the library root (the SphereCeti.* glob '
               f'builds every topic module); restore it with `git checkout {modules["merge_base"][:12]} -- '
               f'{ROOT_MODULE}`')
    return step('root_imports', 'fail', message, seconds=time.monotonic() - started,
                failures=[{'file': ROOT_MODULE, 'message': message}], details=details)


AXIOM_ERROR = re.compile(r'axioms: (\S+): (\S+) depends on (\S+)\Z')


def audit_step(root: Path, modules: dict) -> dict:
    with tempfile.TemporaryDirectory(prefix='sphereceti-verify-') as directory:
        report_path = Path(directory) / 'audit.json'
        command = ['lake', 'env', sys.executable, '-I', 'scripts/check_audits.py', '--report', str(report_path)]
        result, seconds = _run(command, root, timeout=AUDIT_TIMEOUT)
        report = None
        if report_path.is_file():
            try:
                report = json.loads(report_path.read_text())
            except ValueError:
                report = None
    shown = [command[0], *command[1:-1], '<report>']
    verdict = report.get('verdict', {}) if isinstance(report, dict) else {}
    ratchet = [line.removeprefix('audit ratchet: ') for line in result.stdout.splitlines()
               if line.startswith('audit ratchet: ')]
    details = {'roadmap_admissions': verdict.get('roadmap_admissions'),
               'declarations': sum(verdict.get('declaration_counts', {}).values()) if verdict else None,
               'ratchet': ratchet, 'new_admissions': [], 'regressions': [],
               'policy_changed': modules['policy_changed']}
    if modules['policy_changed']:
        details['policy_note'] = ('policy/audits.json differs from the base; the trusted build applies '
                                  "main's policy, so this change needs human review")
    if result.returncode == 0:
        summary = (f"{details['declarations']} owned declarations checked; "
                   f"{details['roadmap_admissions']} ledgered roadmap admissions; no new admissions")
        return step('audit', 'pass', summary, seconds=seconds, command=shown, details=details)
    failures = []
    paths = {m: m.replace('.', '/') + '.lean' for m in modules['library'] + modules['roadmap']}
    for error in verdict.get('errors', []) if verdict.get('passed') is False else []:
        match = AXIOM_ERROR.match(error)
        if match and match[3] == 'sorryAx':
            details['new_admissions'].append({'module': match[1], 'declaration': match[2]})
        else:
            details['regressions'].append(error)
        failure = {'message': error}
        owner = match[1] if match else None
        if owner:
            failure['file'] = paths.get(owner, owner.replace('.', '/') + '.lean')
        failures.append(failure)
    if not failures:
        text = result.stdout + result.stderr
        failures = locations(text, severities=('error', 'warning')) or [
            {'message': _tail(result.stderr.removeprefix('compiled audits: ') or result.stdout)}]
        details['regressions'] = [f.get('message', '') for f in failures]
    first = failures[0]
    where = f"{first['file']}:{first['line']}: " if 'line' in first else ''
    count = len(details['new_admissions'])
    summary = (f'{count} new admission(s); ' if count else '') + where + first['message'].splitlines()[0]
    return step('audit', 'fail', summary, seconds=seconds, command=shown, failures=failures, details=details)


# ---------------------------------------------------------------------------------------------
# Orchestration


def next_action(verdict: str, steps: list[dict], guidance: str | None) -> str:
    if verdict == 'environment_error':
        return guidance or 'Fix the environment and rerun `sphereceti verify`.'
    if verdict == 'pass':
        return ('Open or update the PR. CI and the trusted build repeat these checks with main\'s '
                'approved tooling.')
    if verdict == 'fail':
        failed = next(s for s in steps if s['status'] == 'fail')
        return f"Fix the {failed['name']} failure ({failed['summary']}), then rerun `sphereceti verify`."
    skipped_steps = [s for s in steps if s['status'] == 'skipped']
    return ('Not verified: ' + '; '.join(f"{s['name']} skipped ({s['summary']})" for s in skipped_steps) +
            '. Rerun `sphereceti verify` without skipping before opening the PR.')


def verify(repo: Path, base: str = 'origin/main', explicit: list[str] | None = None, *,
           skip_audit: bool = False) -> dict:
    started = time.monotonic()
    report = {'schema': SCHEMA, 'verdict': None, 'exit_code': None, 'next_action': None,
              'root': None, 'head': None, 'base': None, 'environment': None, 'modules': None,
              'steps': [], 'failures': [], 'seconds': None}
    guidance = None
    try:
        root = checkout(repo.resolve())
        report['root'] = str(root)
        report['environment'] = environment(root)
        modules = changes(root, base, list(explicit or []))
        report['modules'] = modules
        report['head'] = modules['head']
        report['base'] = {'ref': base, 'merge_base': modules['merge_base']}
        counts = len(modules['library']) + len(modules['roadmap'])
        summary = (f"{len(explicit)} requested module(s)" if explicit else
                   f"{counts} changed library/roadmap module(s), {len(modules['deleted'])} deleted"
                   f" against {base} (merge base {modules['merge_base'][:12]})")
        steps = [step('changes', 'pass', summary)]
        steps.append(roadmap_step(root))
        steps.append(build_step(root, modules))
        boundaries, _ = boundaries_step(root)
        steps.append(boundaries)
        steps.append(root_step(root, modules))
        if skip_audit:
            steps.append(skipped('audit', 'skipped on request (--skip-audit)'))
        elif steps[2]['status'] == 'fail':
            steps.append(skipped('audit', 'the build failed; the audit rebuilds every source'))
        elif boundaries['status'] == 'fail':
            steps.append(skipped('audit', 'module boundaries failed; the audit inventory rejects the same import'))
        else:
            steps.append(audit_step(root, modules))
        report['steps'] = steps
        statuses = {s['status'] for s in steps}
        verdict = 'fail' if 'fail' in statuses else 'incomplete' if 'skipped' in statuses else 'pass'
    except EnvironmentProblem as problem:
        verdict, guidance = 'environment_error', problem.guidance
        env = report['environment'] or {'ok': False}
        report['environment'] = {**env, 'ok': False, 'problem': str(problem), 'guidance': problem.guidance}
        done = {s['name'] for s in report['steps']}
        report['steps'] = report['steps'] + [skipped(n, 'environment unavailable') for n in STEPS if n not in done]
    report['verdict'] = verdict
    report['exit_code'] = {'pass': 0, 'fail': 1, 'incomplete': 1, 'environment_error': 2}[verdict]
    report['failures'] = [{'step': s['name'], **f} for s in report['steps'] for f in s['failures']]
    report['next_action'] = next_action(verdict, report['steps'], guidance)
    report['seconds'] = round(time.monotonic() - started, 2)
    return report


def _inert(text) -> str:
    """Terminal-safe: candidate diagnostics cannot emit control sequences."""
    return ''.join(c if c == '\n' or ord(c) >= 32 and ord(c) != 127 else '?' for c in str(text))


def render(report: dict) -> str:
    lines = []
    if report['head']:
        lines.append(f"sphereceti verify: {report['root']} at {report['head'][:12]} "
                     f"against {report['base']['ref']}")
    for note in (report['environment'] or {}).get('notes', []):
        lines.append(f'note: {note}')
    for s in report['steps']:
        label = {'pass': 'PASS', 'fail': 'FAIL', 'skipped': 'SKIPPED'}[s['status']]
        timing = f" ({s['seconds']:.1f}s)" if s['seconds'] else ''
        lines.append(f"  {s['name']:<13} {label:<8} {_inert(s['summary']).splitlines()[0] if s['summary'] else ''}{timing}")
        for f in s['failures'][1:6]:
            where = f"{f['file']}:{f['line']}:{f['column']}: " if 'line' in f else (f"{f['file']}: " if 'file' in f else '')
            lines.append(f"      {where}{_inert(f['message']).splitlines()[0] if f['message'] else ''}")
        if len(s['failures']) > 6:
            lines.append(f"      ... {len(s['failures']) - 6} more (see --json)")
    env = report['environment'] or {}
    if env.get('problem'):
        lines.append(f"environment: {_inert(env['problem'])}")
    policy_note = next((s['details'].get('policy_note') for s in report['steps'] if s['name'] == 'audit'), None)
    if policy_note:
        lines.append(f'note: {policy_note}')
    lines.append(f"Verdict: {report['verdict'].upper().replace('_', ' ')} (exit {report['exit_code']})")
    lines.append(f"Next: {_inert(report['next_action'])}")
    return '\n'.join(lines)


def run(args) -> int:
    report = verify(args.repo, args.base, args.module, skip_audit=args.skip_audit)
    print(json.dumps(report, indent=2) if args.json else render(report))
    return report['exit_code']
