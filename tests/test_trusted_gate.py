"""Immutable Git-tree gate: adversarial scope/config changes cannot authorize themselves."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools/project'))
from sphereceti.gate import GateError, evaluate, git, prepare


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
        self.write('policy/automation.toml', (ROOT / 'policy/automation.toml').read_text().replace(
            'mathematical_paths = []', 'mathematical_paths = ["SphereCeti"]'))
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

    def test_empty_actual_allowlist_requires_human_for_lean(self):
        self.write('policy/automation.toml', (ROOT / 'policy/automation.toml').read_text())
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
