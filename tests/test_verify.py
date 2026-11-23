"""`sphereceti verify` over Git fixtures, a fake `lake` on PATH, and stand-in CI scripts.

The stand-in `scripts/check_audits.py` builds a compiled report and judges it with the real
`check_audits.assess` and `load_policy`, so audit regressions keep CI's exact message format.
The real Lean-backed checks are exercised by test_compiled_audits and test_module_boundaries.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
GIT = shutil.which('git')

FAKE_LAKE = '''#!{python}
import json, os, sys
args = sys.argv[1:]
with open(os.environ['FAKE_LAKE_LOG'], 'a') as log:
    log.write(json.dumps(args) + '\\n')
if args[:1] == ['env']:
    os.execv(args[1], args[1:])
if args[:1] == ['build']:
    failures = json.loads(os.environ.get('FAKE_LAKE_FAIL', '{{}}'))
    for target in args[1:] or ['(default)']:
        print('\\u2714 [1/3] Building ' + target, flush=True)
        if target in failures:
            print(failures[target])
            print('error: Lean exited with code 1')
            print('Some required targets logged failures:')
            sys.exit(1)
    print('Build completed successfully (3 jobs).')
    sys.exit(0)
sys.exit(2)
'''

CHECK_ROADMAP = '''import os, sys
if os.environ.get('FAKE_ROADMAP_ERROR'):
    print('ERROR: ' + os.environ['FAKE_ROADMAP_ERROR'], file=sys.stderr)
    raise SystemExit(1)
print('roadmap static checks: 0 intentional sorry commands')
print('roadmap static checks: OK')
'''

# Fixture-only inventory: the real script asks `lean --src-deps`; this reads `import` lines.
CHECK_MODULES = '''import json, os, re, sys
from pathlib import Path
root = Path(__file__).resolve().parents[1]
if os.environ.get('FAKE_BOUNDARY_ERROR'):
    print('module boundaries: ' + os.environ['FAKE_BOUNDARY_ERROR'], file=sys.stderr)
    raise SystemExit(1)
modules = []
for path in sorted(root.rglob('*.lean')):
    rel = path.relative_to(root)
    if rel.parts[0] in ('.lake', '.git'):
        continue
    kind = {'SphereCeti': 'library', 'SphereCetiRoadmap': 'roadmap'}.get(rel.with_suffix('').parts[0], 'tooling')
    imports = re.findall(r'^(?:public )?import (\\S+)$', path.read_text(), re.M)
    modules.append({'name': '.'.join(rel.with_suffix('').parts), 'path': rel.as_posix(), 'kind': kind,
                    'imports': sorted(i for i in imports if i.startswith('SphereCeti'))})
print(json.dumps({'modules': modules}, indent=2) if '--json' in sys.argv else 'module boundaries: OK')
'''

CHECK_AUDITS = '''import argparse, json, os, sys
from pathlib import Path
sys.path.insert(0, os.environ['REAL_SCRIPTS'])
from check_audits import AuditError, assess, load_policy
root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--report', type=Path)
args = parser.parse_args()
policy = load_policy(root / 'policy/audits.json')
inventory = json.loads(os.popen(sys.executable + ' -I ' + str(root / 'scripts/check_modules.py') + ' --json').read())['modules']
empty = {e['moduleName'] for e in policy['empty_modules']}
sorry = os.environ.get('FAKE_SORRY_DECL', '')
declarations = []
for m in inventory:
    if m['kind'] in ('library', 'roadmap') and m['name'] not in empty:
        name = m['name'] + '.ok'
        declarations.append({'moduleName': m['name'], 'name': name,
                             'axioms': ['propext', 'sorryAx'] if name == sorry else ['propext']})
compiled = {'schema_version': 1, 'linters': policy['linters'], 'findings': [], 'nolints': [],
            'declarations': declarations,
            'modules': [{'name': m['name'], 'isModule': True, 'imports': m['imports']}
                        for m in inventory if m['kind'] in ('library', 'roadmap')]}
verdict = assess(compiled, inventory, policy)
args.report.write_text(json.dumps({'verdict': verdict, 'compiled': compiled}))
for reminder in verdict['ratchet']:
    print('audit ratchet: ' + reminder)
if not verdict['passed']:
    print('compiled audits: ' + '\\n'.join(verdict['errors']), file=sys.stderr)
    raise SystemExit(1)
print('compiled audits: OK')
'''

POLICY = {
    'schema_version': 1, 'linters': ['checkType'],
    'empty_modules': [{'moduleName': name, 'reason': 'imports-only scaffold'}
                      for name in ('SphereCeti', 'SphereCetiRoadmap')],
    'axiom_exceptions': [], 'roadmap_admissions': [], 'lint_baseline': [], 'nolint_allowlist': [],
}


def git(repo, *args):
    return subprocess.check_output([GIT, '-C', str(repo), *args], text=True, stderr=subprocess.PIPE).strip()


def commit_all(repo, message='fixture'):
    git(repo, 'add', '-A')
    git(repo, 'commit', '-qm', message)
    return git(repo, 'rev-parse', 'HEAD')


def init(repo):
    repo.mkdir(parents=True)
    git(repo, 'init', '-q', '-b', 'main')
    git(repo, 'config', 'user.name', 'Verify fixture')
    git(repo, 'config', 'user.email', 'fixture@example.invalid')


class VerifyTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='sphereceti-verify-test-')
        self.addCleanup(self.temp.cleanup)
        base = Path(self.temp.name)
        self.repo, self.bin, self.log = base / 'repo', base / 'bin', base / 'lake.log'
        self.bin.mkdir()
        lake = self.bin / 'lake'
        lake.write_text(FAKE_LAKE.format(python=sys.executable))
        lake.chmod(0o755)
        init(self.repo)
        revs = {}
        for name in ('mathlib', 'TauCeti'):
            package = self.repo / '.lake/packages' / name
            init(package)
            (package / 'README').write_text(name)
            revs[name] = commit_all(package)
        olean = self.repo / '.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean'
        olean.parent.mkdir(parents=True)
        olean.write_bytes(b'olean')
        (self.repo / '.lake/packages/TauCeti/.lake/build/lib/lean').mkdir(parents=True)
        self.write('.gitignore', '/.lake/\n')
        self.write('lakefile.toml', 'name = "SphereCeti"\ndefaultTargets = ["SphereCeti", "SphereCetiRoadmap"]\n')
        self.write('lean-toolchain', 'leanprover/lean4:v4.36.0-rc2\n')
        self.write('lake-manifest.json', json.dumps({'version': '1.1.0', 'packagesDir': '.lake/packages',
                                                     'packages': [{'type': 'git', 'name': n, 'rev': r}
                                                                  for n, r in revs.items()]}))
        self.write('policy/audits.json', json.dumps(POLICY, indent=2))
        self.write('scripts/check_roadmap.py', CHECK_ROADMAP)
        self.write('scripts/check_modules.py', CHECK_MODULES)
        self.write('scripts/check_audits.py', CHECK_AUDITS)
        self.write('SphereCeti.lean', 'module\n\npublic import SphereCeti.Basic\n')
        self.write('SphereCeti/Basic.lean', 'module\n')
        self.write('SphereCetiRoadmap.lean', 'module\n\npublic import SphereCeti\n')
        self.main = commit_all(self.repo, 'main')
        git(self.repo, 'update-ref', 'refs/remotes/origin/main', self.main)
        git(self.repo, 'switch', '-qc', 'proof/topic')

    def write(self, path, text):
        file = self.repo / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(text)

    def add_topic(self, *, export=True, extra_root=''):
        self.write('SphereCeti/Topic/Main.lean', 'module\n\npublic import SphereCeti.Topic.Lemma\n')
        self.write('SphereCeti/Topic/Lemma.lean', 'module\n')
        if export:
            self.write('SphereCeti.lean', 'module\n\npublic import SphereCeti.Basic\n'
                       'public import SphereCeti.Topic.Main\n' + extra_root)
        elif extra_root:
            self.write('SphereCeti.lean', 'module\n\npublic import SphereCeti.Basic\n' + extra_root)
        commit_all(self.repo, 'topic')

    def verify(self, *args, path=None, **env):
        environment = {k: v for k, v in os.environ.items() if not k.startswith(('FAKE_', 'GIT_'))}
        environment.update(PATH=path if path is not None else f'{self.bin}{os.pathsep}{Path(GIT).parent}',
                           PYTHONPATH=str(ROOT / 'tools/project'), FAKE_LAKE_LOG=str(self.log),
                           REAL_SCRIPTS=str(ROOT / 'scripts'), **env)
        result = subprocess.run([sys.executable, '-m', 'sphereceti.cli', 'verify', '--json', *args],
                                cwd=self.repo, env=environment, capture_output=True, text=True, timeout=120)
        # Acceptance: stdout is exactly one JSON document, whatever progress is printed.
        report = json.loads(result.stdout)
        self.assertEqual(result.returncode, report['exit_code'], result.stderr)
        return report, result

    def steps(self, report):
        return {s['name']: s for s in report['steps']}

    def lake_calls(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()] if self.log.exists() else []

    def test_changed_modules_are_detected_and_built(self):
        self.add_topic()
        self.write('SphereCeti/Topic/Scratch.lean', 'module\n')  # untracked work counts too
        report, _ = self.verify()
        modules = report['modules']
        self.assertEqual(modules['merge_base'], self.main)
        self.assertEqual(modules['library'], ['SphereCeti', 'SphereCeti.Topic.Lemma', 'SphereCeti.Topic.Main',
                                              'SphereCeti.Topic.Scratch'])
        self.assertEqual(modules['added_library'], ['SphereCeti.Topic.Lemma', 'SphereCeti.Topic.Main',
                                                    'SphereCeti.Topic.Scratch'])
        # The library root changed, so the whole library is built rather than module by module.
        self.assertEqual([t['target'] for t in modules['build_targets']], ['@/SphereCeti'])
        self.assertIn(['build', '@/SphereCeti'], self.lake_calls())
        # Scratch is not reachable from the root: verify catches the forgotten export.
        self.assertEqual(self.steps(report)['root_imports']['status'], 'fail')

    def test_module_changes_without_root_change_build_each_module(self):
        self.add_topic()
        git(self.repo, 'update-ref', 'refs/remotes/origin/main', 'HEAD')
        self.write('SphereCeti/Topic/Lemma.lean', 'module\n-- edited\n')
        report, _ = self.verify()
        self.assertEqual(report['verdict'], 'pass')
        self.assertEqual(report['exit_code'], 0)
        self.assertEqual([t['target'] for t in report['modules']['build_targets']], ['+SphereCeti.Topic.Lemma'])
        self.assertIn('unchanged', self.steps(report)['root_imports']['summary'])

    def test_explicit_modules_and_base(self):
        self.add_topic()
        report, _ = self.verify('--module', 'SphereCeti.Basic', '--base', self.main)
        self.assertEqual(report['modules']['selection'], 'explicit')
        self.assertEqual([t['target'] for t in report['modules']['build_targets']], ['+SphereCeti.Basic'])
        report, _ = self.verify('--module', 'SphereCeti.Missing')
        self.assertEqual(report['exit_code'], 2)

    def test_build_failure_exits_1_with_location(self):
        self.add_topic()
        failure = "error: ././SphereCeti/Topic/Main.lean:12:4: Unknown identifier `foo`\n  more context"
        report, result = self.verify(FAKE_LAKE_FAIL=json.dumps({'@/SphereCeti': failure}))
        self.assertEqual(report['exit_code'], 1)
        self.assertEqual(report['verdict'], 'fail')
        build = self.steps(report)['build']
        self.assertEqual(build['status'], 'fail')
        self.assertEqual(build['failures'][0], {'target': '@/SphereCeti', 'file': 'SphereCeti/Topic/Main.lean',
                                                'line': 12, 'column': 4, 'message': 'Unknown identifier `foo`'})
        self.assertIn('SphereCeti/Topic/Main.lean:12:4', build['summary'])
        self.assertEqual(report['failures'][0]['step'], 'build')
        # The audit is not run on a broken build, and is never reported as passing.
        self.assertEqual(self.steps(report)['audit']['status'], 'skipped')
        self.assertIn('Unknown identifier', result.stderr)  # Lake's log went to stderr

    def test_missing_root_import_fails(self):
        self.add_topic(export=False)
        report, _ = self.verify()
        root = self.steps(report)['root_imports']
        self.assertEqual(report['exit_code'], 1)
        self.assertEqual(root['status'], 'fail')
        self.assertEqual({f['file'] for f in root['failures']},
                         {'SphereCeti/Topic/Main.lean', 'SphereCeti/Topic/Lemma.lean'})
        self.assertIn('not imported from SphereCeti.lean', root['summary'])

    def test_unrelated_root_edit_fails(self):
        self.add_topic(extra_root='-- unrelated\n')
        report, _ = self.verify()
        root = self.steps(report)['root_imports']
        self.assertEqual(root['status'], 'fail')
        self.assertEqual(root['failures'][0]['file'], 'SphereCeti.lean')
        self.assertIn('non-import line', root['summary'])

    def test_sorted_root_imports_pass_with_auto_approval_note(self):
        # Most proof PRs alphabetize the root; CI accepts it, auto-approve-check does not.
        # Like main's root today: Basic precedes a later topic that sorts before it.
        self.write('SphereCeti.lean', 'module\n\npublic import SphereCeti.Zeta\npublic import SphereCeti.Basic\n')
        self.write('SphereCeti/Zeta.lean', 'module\n')
        commit_all(self.repo, 'zeta')
        git(self.repo, 'update-ref', 'refs/remotes/origin/main', 'HEAD')
        self.add_topic(export=False, extra_root='public import SphereCeti.Topic.Main\n')
        self.write('SphereCeti.lean', 'module\n\npublic import SphereCeti.Basic\npublic import SphereCeti.Topic.Main\n'
                   'public import SphereCeti.Zeta\n')
        report, result = self.verify()
        root = self.steps(report)['root_imports']
        self.assertEqual(root['status'], 'pass', root)
        self.assertTrue(root['details']['reordered'])
        self.assertEqual(root['details']['added_imports'], ['SphereCeti.Topic.Main'])
        self.assertIn('auto-approve-check', root['details']['auto_approval_note'])
        self.assertEqual(report['verdict'], 'pass')

    def test_removed_root_import_fails(self):
        self.add_topic(export=False)
        self.write('SphereCeti.lean', 'module\n\npublic import SphereCeti.Topic.Main\n')
        report, _ = self.verify()
        root = self.steps(report)['root_imports']
        self.assertEqual(root['status'], 'fail')
        self.assertFalse(root['details']['reordered'])
        self.assertIn('removes or edits existing lines', root['summary'])

    def test_topic_submodules_reachable_through_entry_point_pass(self):
        self.add_topic()
        report, result = self.verify()
        root = self.steps(report)['root_imports']
        self.assertEqual(root['status'], 'pass', root)
        self.assertEqual(root['details']['added_imports'], ['SphereCeti.Topic.Main'])
        self.assertEqual(report['verdict'], 'pass')
        self.assertIn('verify: running', result.stderr)

    def test_audit_regression_fails(self):
        self.add_topic()
        report, _ = self.verify(FAKE_SORRY_DECL='SphereCeti.Topic.Lemma.ok')
        audit = self.steps(report)['audit']
        self.assertEqual(report['exit_code'], 1)
        self.assertEqual(audit['status'], 'fail')
        self.assertEqual(audit['details']['new_admissions'],
                         [{'module': 'SphereCeti.Topic.Lemma', 'declaration': 'SphereCeti.Topic.Lemma.ok'}])
        self.assertEqual(audit['failures'][0]['file'], 'SphereCeti/Topic/Lemma.lean')
        self.assertIn('1 new admission', audit['summary'])

    def test_policy_change_is_flagged(self):
        policy = dict(POLICY, empty_modules=POLICY['empty_modules'] +
                      [{'moduleName': 'SphereCeti.Basic', 'reason': 'scaffold'}])
        self.write('policy/audits.json', json.dumps(policy))
        report, _ = self.verify()
        audit = self.steps(report)['audit']
        self.assertTrue(audit['details']['policy_changed'])
        self.assertIn('human review', audit['details']['policy_note'])

    def test_missing_cache_exits_2_with_guidance(self):
        (self.repo / '.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean').unlink()
        report, _ = self.verify()
        self.assertEqual(report['exit_code'], 2)
        self.assertEqual(report['verdict'], 'environment_error')
        self.assertIn('Mathlib build cache is missing', report['environment']['problem'])
        self.assertIn('lake exe cache get', report['environment']['guidance'])
        self.assertIn('lake exe cache get', report['next_action'])
        self.assertTrue(all(s['status'] == 'skipped' for s in report['steps']))
        self.assertEqual(self.lake_calls(), [])

    def test_unpinned_dependency_exits_2(self):
        package = self.repo / '.lake/packages/TauCeti'
        (package / 'README').write_text('moved')
        commit_all(package)
        report, _ = self.verify()
        self.assertEqual(report['exit_code'], 2)
        self.assertIn('lake-manifest.json pins', report['environment']['problem'])

    def test_missing_lake_exits_2_with_guidance(self):
        report, _ = self.verify(path=self.git_only_path())
        self.assertEqual(report['exit_code'], 2)
        self.assertIn('lake is not on PATH', report['environment']['problem'])
        self.assertIn('install_lean.sh', report['environment']['guidance'])

    def git_only_path(self):
        only = Path(self.temp.name) / 'git-only'
        only.mkdir()
        (only / 'git').symlink_to(GIT)
        return str(only)

    def test_not_a_checkout_exits_2(self):
        (self.repo / 'scripts/check_audits.py').unlink()
        report, _ = self.verify()
        self.assertEqual(report['exit_code'], 2)
        self.assertIn('scripts/check_audits.py', report['environment']['problem'])

    def test_json_shape(self):
        self.add_topic()
        report, result = self.verify()
        self.assertEqual(report['schema'], 'sphereceti.verify/v1')
        self.assertEqual(set(report), {'schema', 'verdict', 'exit_code', 'next_action', 'root', 'head', 'base',
                                       'environment', 'modules', 'steps', 'failures', 'seconds'})
        self.assertEqual([s['name'] for s in report['steps']],
                         ['changes', 'roadmap', 'build', 'boundaries', 'root_imports', 'audit'])
        for s in report['steps']:
            self.assertEqual(set(s), {'name', 'status', 'summary', 'seconds', 'command', 'failures', 'details'})
            self.assertIn(s['status'], ('pass', 'fail', 'skipped'))
            self.assertIsInstance(s['seconds'], float)
        self.assertEqual(report['base'], {'ref': 'origin/main', 'merge_base': self.main})
        self.assertEqual(report['head'], git(self.repo, 'rev-parse', 'HEAD'))
        self.assertEqual(report['failures'], [])
        self.assertTrue(report['environment']['ok'])
        self.assertTrue(result.stderr.strip())  # progress was emitted, on stderr only

    def test_skipped_step_is_never_reported_as_pass(self):
        self.add_topic()
        report, _ = self.verify('--skip-audit')
        self.assertEqual(self.steps(report)['audit']['status'], 'skipped')
        self.assertEqual(report['verdict'], 'incomplete')
        self.assertEqual(report['exit_code'], 1)
        self.assertIn('Not verified', report['next_action'])
        # Boundary failure: the root reachability check cannot run, so it is skipped, not passed.
        report, _ = self.verify(FAKE_BOUNDARY_ERROR='forbidden import: SphereCeti.Topic.Main (library) -> '
                                                    'SphereCetiRoadmap (roadmap)')
        steps = self.steps(report)
        self.assertEqual(steps['boundaries']['status'], 'fail')
        self.assertEqual(steps['boundaries']['failures'][0]['file'], 'SphereCeti/Topic/Main.lean')
        self.assertEqual(steps['root_imports']['status'], 'skipped')
        self.assertEqual(steps['audit']['status'], 'skipped')
        self.assertEqual(report['verdict'], 'fail')

    def test_text_output_marks_skips(self):
        self.add_topic()
        environment = {k: v for k, v in os.environ.items() if not k.startswith(('FAKE_', 'GIT_'))}
        environment.update(PATH=f'{self.bin}{os.pathsep}{Path(GIT).parent}', FAKE_LAKE_LOG=str(self.log),
                           PYTHONPATH=str(ROOT / 'tools/project'), REAL_SCRIPTS=str(ROOT / 'scripts'))
        result = subprocess.run([sys.executable, '-m', 'sphereceti.cli', 'verify', '--skip-audit'],
                                cwd=self.repo, env=environment, capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, 1)
        self.assertRegex(result.stdout, r'audit\s+SKIPPED')
        self.assertIn('Verdict: INCOMPLETE (exit 1)', result.stdout)
        self.assertNotIn('Verdict: PASS', result.stdout)


if __name__ == '__main__':
    unittest.main()
