"""Immutable Git-tree gate: adversarial scope/config changes cannot authorize themselves."""
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools/project'))
from sphereceti.gate import GateError, evaluate, git, prepare


def with_paths(value):
    """The shipped policy with an explicit allowlist, for fixtures that test other allowlists.

    These fixtures test scope, not merging, so merging is off (an empty allowlist forbids it)."""
    text = (ROOT / 'policy/automation.toml').read_text()
    text = re.sub(r'(?m)^merging = .*$', 'merging = false', text)
    return re.sub(r'(?m)^mathematical_paths = .*$', f'mathematical_paths = {value}', text)


class TrustedGateTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name) / 'repo'
        self.repo.mkdir()
        git(self.repo, 'init', '-q')
        for name in ('sphereceti.toml', 'policy/automation.toml', 'lakefile.toml',
                     'lake-manifest.json', 'lean-toolchain'):
            self.write(name, (ROOT / name).read_text())
        self.write('README.md', 'Protected roadmap\n')
        self.write('SphereCeti/Example.lean', '-- fixture\n')
        # An explicit approved allowlist tests future classification, not current activation.
        self.write('policy/automation.toml', with_paths('["SphereCeti"]'))
        self.base = self.commit()

    def write(self, name, content):
        path = self.repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)

    def commit(self):
        git(self.repo, 'add', '-A', '-f', '.')
        git(self.repo, '-c', 'user.name=Test', '-c', 'user.email=test@example.com',
            '-c', 'core.hooksPath=/dev/null', 'commit', '-qm', 'fixture')
        return git(self.repo, 'rev-parse', 'HEAD').decode().strip()

    def verdict(self):
        return evaluate(self.repo, self.base, self.base, self.commit())

    def test_approved_mathematics_scope_is_not_merge_authorization(self):
        self.write('SphereCeti/Example.lean', '-- changed\n')
        report = self.verdict()
        self.assertEqual(report['scope'], 'mathematical')
        self.assertTrue(report['config_attested'])
        self.assertNotIn('merge', report)

    def test_candidate_policy_and_mixed_changes_need_human(self):
        self.write('SphereCeti/Example.lean', '-- changed\n')
        self.write('policy/automation.toml', 'merging = true\n')
        self.write('scripts/trusted_gate.py', 'raise RuntimeError("untrusted")\n')
        report = self.verdict()
        self.assertTrue(report['config_attested'])
        self.assertEqual(report['scope'], 'human_review')
        self.assertEqual(len(report['changes']), 3)

    def test_protected_and_unknown_files_remain_protected(self):
        from sphereceti.gate import path_class
        for path in ('README.md', 'CONVENTIONS.md', 'SphereCetiRoadmap/Suggested.lean',
                     'SphereCeti/Pinned.lean', 'SphereCeti/Suggested.lean', 'SphereCeti/Basic.lean',
                     'SphereCeti.lean', 'rubrics/review.md', '.github/workflows/ci.yml', 'unknown.txt'):
            with self.subTest(path=path):
                self.assertEqual(path_class(path), 'protected')
        self.write('unknown.txt', 'not in a known class')
        self.assertEqual(self.verdict()['scope'], 'human_review')

    def test_empty_allowlist_requires_human_for_lean(self):
        self.write('policy/automation.toml', with_paths('[]'))
        self.base = self.commit()
        self.write('SphereCeti/Example.lean', '-- changed\n')
        self.assertEqual(self.verdict()['scope'], 'human_review')

    def test_configuration_changes_never_materialize_or_execute(self):
        for name in ('lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain'):
            with self.subTest(name=name):
                git(self.repo, 'reset', '--hard', self.base)
                self.write(name, 'invalid executable config\n')
                head = self.commit()
                dest = Path(self.temp.name) / 'candidate'
                report = prepare(self.repo, self.base, self.base, head, dest)
                self.assertFalse(report['config_attested'])
                self.assertIn(name, report['config_differences'])
                self.assertFalse(dest.exists())

    def test_rename_of_protected_file_cannot_hide_deletion(self):
        (self.repo / 'README.md').rename(self.repo / 'SphereCeti/New.lean')
        report = self.verdict()
        self.assertEqual(report['scope'], 'human_review')
        self.assertEqual({c['path'] for c in report['changes']}, {'README.md', 'SphereCeti/New.lean'})

    def test_full_diff_over_api_page_limit(self):
        for index in range(301):
            self.write(f'SphereCeti/Many{index}.lean', '-- new\n')
        self.write('zzz-unknown', 'protected at end of listing')
        report = self.verdict()
        self.assertEqual(len(report['changes']), 302)
        self.assertEqual(report['scope'], 'human_review')

    def test_symlink_and_reserved_tree_paths_fail_closed(self):
        for path in ('.lake/evil', '.venv/evil', 'lake-packages/evil'):
            with self.subTest(path=path):
                git(self.repo, 'reset', '--hard', self.base)
                self.write(path, 'evil')
                with self.assertRaises(GateError):
                    self.verdict()
        git(self.repo, 'reset', '--hard', self.base)
        (self.repo / 'escape').symlink_to('/tmp')
        with self.assertRaises(GateError):
            self.verdict()

    def test_submodule_and_control_character_paths_fail_closed(self):
        git(self.repo, 'update-index', '--add', '--cacheinfo', f'160000,{self.base},submodule')
        git(self.repo, '-c', 'user.name=Test', '-c', 'user.email=test@example.com',
            '-c', 'core.hooksPath=/dev/null', 'commit', '-qm', 'submodule')
        head = git(self.repo, 'rev-parse', 'HEAD').decode().strip()
        with self.assertRaises(GateError):
            evaluate(self.repo, self.base, self.base, head)
        git(self.repo, 'reset', '--hard', self.base)
        self.write('bad\npath', 'bad')
        with self.assertRaises(GateError):
            self.verdict()

    def test_missing_or_mutable_revision_and_empty_diff_fail(self):
        for head in ('HEAD', '0' * 40, self.base):
            with self.subTest(head=head), self.assertRaises(GateError):
                evaluate(self.repo, self.base, self.base, head)

    def test_raw_materialization_preserves_head_despite_attributes_and_new_tip(self):
        self.write('.gitattributes', 'SphereCeti/* export-ignore\n*.lean filter=evil\n')
        self.write('SphereCeti/Example.lean', '-- exact immutable bytes\n')
        head = self.commit()
        self.write('SphereCeti/Example.lean', '-- later tip\n')
        later = self.commit()
        dest = Path(self.temp.name) / 'candidate'
        report = prepare(self.repo, self.base, self.base, head, dest)
        self.assertEqual(report['head'], head)
        self.assertEqual((dest / 'SphereCeti/Example.lean').read_text(), '-- exact immutable bytes\n')
        self.assertEqual(git(dest, 'rev-parse', 'HEAD').decode().strip(), head)
        self.assertEqual(git(self.repo, 'rev-parse', 'HEAD').decode().strip(), later)
        self.assertTrue((dest / '.lake').is_dir())
        with self.assertRaises(GateError):
            prepare(self.repo, self.base, self.base, head, dest)

    def test_approved_config_is_stricter_than_old_merge_base(self):
        self.write('SphereCeti/Example.lean', '-- candidate\n')
        head = self.commit()
        git(self.repo, 'checkout', '--detach', self.base)
        self.write('lean-toolchain', 'leanprover/lean4:changed-approved-pin\n')
        tooling = self.commit()
        report = evaluate(self.repo, tooling, tooling, head)
        self.assertEqual(report['diff_base'], self.base)
        self.assertFalse(report['config_attested'])

    def test_multiple_merge_bases_fail_closed(self):
        tree_oid = git(self.repo, 'rev-parse', self.base + '^{tree}').decode().strip()
        def node(message, *parents):
            args = ['-c', 'user.name=Test', '-c', 'user.email=test@example.com',
                    'commit-tree', tree_oid, '-m', message]
            for parent in parents:
                args.extend(['-p', parent])
            return git(self.repo, *args).decode().strip()
        a, b = node('A', self.base), node('B', self.base)
        left, right = node('left', a, b), node('right', b, a)
        with self.assertRaisesRegex(GateError, 'unambiguous merge base'):
            evaluate(self.repo, self.base, left, right)


class ShippedAllowlistGateTest(unittest.TestCase):
    """The shipped policy through the scope gate that pr-build's candidate job runs."""
    ROOT_TEXT = (ROOT / 'SphereCeti.lean').read_text()
    write, commit, verdict = TrustedGateTest.write, TrustedGateTest.commit, TrustedGateTest.verdict

    def setUp(self):
        TrustedGateTest.setUp(self)
        self.write('policy/automation.toml', (ROOT / 'policy/automation.toml').read_text())
        self.write('SphereCeti.lean', self.ROOT_TEXT)
        for module in ('SphereCeti/Basic.lean', 'SphereCeti/Pinned.lean', 'SphereCeti/Suggested.lean',
                       'SphereCeti/E8/Basic.lean', 'SphereCeti/Contour/Basic.lean', 'SphereCeti/Leech/Basic.lean'):
            self.write(module, 'module\n')
        self.base = self.commit()

    def reset(self):
        git(self.repo, 'reset', '-q', '--hard', self.base)
        git(self.repo, 'clean', '-qfdx')

    def test_shipped_policy_names_the_whole_library(self):
        from sphereceti.config import parse_policy
        policy = parse_policy((ROOT / 'policy/automation.toml').read_text())
        self.assertEqual(policy.mathematical_paths, ('SphereCeti/',))
        # Activated: merging and approving on, every authorized reviewer opted in (2026-11-25).
        self.assertTrue(policy.merging);self.assertTrue(policy.approving)
        self.assertEqual(policy.approving_reviewers, policy.authorized_reviewers)

    def test_module_only_proofs_in_any_topic_get_mathematical_scope(self):
        cases = {'new topic directory': ['SphereCeti/NumberTheory/Foo.lean'],
                 'new Contour module': ['SphereCeti/Contour/TopEdgeDecay.lean'],
                 'modified Leech module': ['SphereCeti/Leech/Basic.lean'],
                 'nested E8 module': ['SphereCeti/E8/Lattice/Even.lean'],
                 'module directly under SphereCeti/': ['SphereCeti/CohnElkies.lean'],
                 'several topics together': ['SphereCeti/Analysis/Gaussian.lean', 'SphereCeti/ZLattice/Dual.lean',
                                             'SphereCeti/MeasureTheory/Periodic.lean']}
        for name, paths in cases.items():
            with self.subTest(name=name):
                self.reset()
                for path in paths:
                    self.write(path, 'module\n-- proof\n')
                report = self.verdict()
                self.assertEqual(report['scope'], 'mathematical', report)
                self.assertEqual({c['class'] for c in report['changes']}, {'library'})

    def test_protected_files_root_outside_paths_and_mixed_changes_keep_human_review(self):
        export = lambda module: self.write('SphereCeti.lean', self.ROOT_TEXT + f'public import {module}\n')
        cases = {
            # The library root is frozen: even exporting the PR's own module needs a human.
            'proof with its root import': lambda: (
                self.write('SphereCeti/NumberTheory/Foo.lean', 'module\n'), export('SphereCeti.NumberTheory.Foo')),
            'root import alone': lambda: export('SphereCeti.E8.Basic'),
            'other root edit': lambda: self.write('SphereCeti.lean', self.ROOT_TEXT + '-- note\n'),
            'protected Basic.lean': lambda: self.write('SphereCeti/Basic.lean', '-- changed\n'),
            'protected Pinned.lean': lambda: self.write('SphereCeti/Pinned.lean', '-- changed\n'),
            'protected Suggested.lean': lambda: self.write('SphereCeti/Suggested.lean', '-- changed\n'),
            'sibling directory outside SphereCeti/': lambda: self.write('SphereCetiExtra/Foo.lean', 'module\n'),
            'roadmap module': lambda: self.write('SphereCetiRoadmap/Foo.lean', 'module\n'),
            'non-Lean file under SphereCeti/': lambda: self.write('SphereCeti/NumberTheory/notes.md', 'notes\n'),
        }
        mixed = {'CI': '.github/workflows/ci.yml', 'policy': 'policy/automation.toml', 'spec': 'README.md',
                 'roadmap': 'SphereCetiRoadmap/Suggested.lean', 'machinery': 'tools/project/sphereceti/gate.py',
                 'scripts': 'scripts/check_audits.py', 'dependencies': 'lean-toolchain'}
        for name, path in mixed.items():
            cases['proof plus ' + name] = (lambda path=path: (
                self.write('SphereCeti/NumberTheory/Foo.lean', 'module\n'), self.write(path, 'changed\n')))
        for name, change in cases.items():
            with self.subTest(name=name):
                self.reset()
                change()
                report = self.verdict()
                self.assertEqual(report['scope'], 'human_review', report)
                if 'root' in name:
                    self.assertIn({'path': 'SphereCeti.lean', 'class': 'protected'}, report['changes'])
                if name.startswith('protected'):
                    self.assertEqual([c['class'] for c in report['changes']], ['protected'])

    def test_status_job_routes_the_scope_to_trusted_scope(self):
        # pr-build.yml publishes trusted-scope success exactly when the candidate job's scope output
        # is `mathematical`; this is the routing a positive gate verdict produces.
        workflow = (ROOT / '.github/workflows/pr-build.yml').read_text()
        self.assertIn('[ "$SCOPE" != mathematical ] || scope_state=success', workflow)
