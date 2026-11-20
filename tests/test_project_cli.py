"""Profile validation, policy isolation, and unknown-vs-empty queue contracts."""

from dataclasses import asdict, replace
import io
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))

from sphereceti import cli
from sphereceti.config import (ConfigError, parse_operator, parse_policy, parse_project,
                              parse_source_lock, resource_text)


DISABLED_POLICY_TEXT = '''schema_version = 1
review_generation = false
posting = false
authoring = false
reporting = false
merging = false
mathematical_paths = []
authorized_reviewers = []
'''
DISABLED_POLICY = parse_policy(DISABLED_POLICY_TEXT)


class ProjectConfigTest(unittest.TestCase):
    def test_shipped_configuration_and_pins(self):
        profile = parse_project(resource_text('sphereceti.toml'))
        self.assertEqual(profile.phase, 'roadmap')
        self.assertTrue(profile.roadmap_approved)
        self.assertEqual(profile.implementation_repository, 'thefundamentaltheor3m/Sphere-Packing-Lean')
        root = Path(__file__).resolve().parents[1]
        source = parse_project((root / 'sphereceti.toml').read_text())
        self.assertEqual(profile, source)
        self.assertEqual(profile.lean, (root / 'lean-toolchain').read_text().strip())
        manifest = json.loads((root / 'lake-manifest.json').read_text())
        packages = {p['name']: p for p in manifest['packages']}
        self.assertEqual(profile.tauceti, packages['TauCeti']['rev'])
        self.assertEqual(profile.mathlib, packages['mathlib']['rev'])

    def test_invalid_profile_is_rejected(self):
        original = resource_text('sphereceti.toml')
        profile = parse_project(original)
        approval = str(profile.roadmap_approved).lower()
        opposite = str(not profile.roadmap_approved).lower()
        cases = [original.replace(f'roadmap_approved = {approval}', f'roadmap_approved = {opposite}'),
                 original.replace('schema_version = 1', 'schema_version = 2'),
                 original.replace('library_root = "SphereCeti"', 'library_root = "../Elsewhere"'),
                 original.replace('library_root = "SphereCeti"', 'library_root = "./"'),
                 original.replace(profile.tauceti, 'main')]
        for text in cases:
            with self.subTest(text=text), self.assertRaises(ConfigError):
                parse_project(text)

    def test_operator_cannot_override_policy_or_sources(self):
        for text in ('merging = true', 'repository = "attacker/project"', '[policy]\nposting = true',
                     'roadmap_approved = true'):
            with self.subTest(text=text), self.assertRaises(ConfigError):
                parse_operator(text)
        prefs = parse_operator('provider = "local"\nbudget_usd = 12.5\nstorage = "/tmp/my-state"')
        self.assertEqual(prefs.budget_usd, 12.5)
        for text in ('budget_usd = -1', 'budget_usd = nan', 'budget_usd = inf', 'budget_usd = true'):
            with self.subTest(text=text), self.assertRaises(ConfigError):
                parse_operator(text)

    def test_shipped_policy_matches_repository_configuration(self):
        root = Path(__file__).resolve().parents[1]
        self.assertEqual(parse_policy(resource_text('automation.toml')),
                         parse_policy((root / 'policy/automation.toml').read_text()))

    def test_explicit_disabled_policy_and_invalid_types(self):
        text = DISABLED_POLICY_TEXT
        policy = parse_policy(text)
        self.assertFalse(any(asdict(policy).values()))
        for bad in (text.replace('posting = false', 'posting = "false"'),
                    text.replace('merging = false', 'merging = true')):
            with self.assertRaises(ConfigError):
                parse_policy(bad)

    def test_enabled_policy_requires_reviewers_and_mathematical_paths(self):
        text = DISABLED_POLICY_TEXT.replace('false', 'true')
        for paths, reviewers in (([], []), (['SphereCeti/Math'], []), ([], ['user:7'])):
            candidate = text.replace('mathematical_paths = []', f'mathematical_paths = {json.dumps(paths)}')
            candidate = candidate.replace('authorized_reviewers = []', f'authorized_reviewers = {json.dumps(reviewers)}')
            with self.subTest(paths=paths, reviewers=reviewers), self.assertRaises(ConfigError):
                parse_policy(candidate)
        enabled = text.replace('mathematical_paths = []', 'mathematical_paths = ["SphereCeti/Math"]')
        enabled = enabled.replace('authorized_reviewers = []', 'authorized_reviewers = ["user:7"]')
        self.assertTrue(parse_policy(enabled).merging)

    def test_source_lock_requires_exact_provenance_and_reuse_terms(self):
        text = resource_text('upstream-lock.toml')
        entries = parse_source_lock(text)
        docs = next(entry for entry in entries if entry['name'] == 'docs-cache-operations')
        self.assertEqual(docs['repository'], 'TauCetiProject/TauCeti')
        self.assertEqual(docs['commit'], 'b743b607ce3e9742b18026ad79082e5d15badff5')
        cases = [text.replace('8671bee98125933c56b9b00a08ded873b77dd23b', 'main'),
                 text.replace('source_paths = ["scripts/source-modules.sh"]', 'source_paths = []'),
                 text.replace('source_paths = ["scripts/source-modules.sh"]', 'source_paths = ["../escape"]'),
                 text.replace('license_status = "unresolved"', 'license_status = "recorded"'),
                 text.replace('state = "planned"', 'state = "imported"')]
        for bad in cases:
            with self.subTest(bad=bad), self.assertRaises(ConfigError):
                parse_source_lock(bad)


class ProjectCLITest(unittest.TestCase):
    def run_json(self, *args):
        output = io.StringIO()
        with patch('sys.stdout', output):
            result = cli.main(list(args))
        return result, json.loads(output.getvalue())

    @patch('sphereceti.cli.subprocess.run')
    def test_offline_is_unknown_not_empty_and_does_not_query(self, run):
        code, report = self.run_json('status', '--offline', '--json')
        self.assertEqual(code, 0)
        self.assertEqual(report['queue'], {'state': 'not_checked', 'pull_requests': None})
        project = parse_project(resource_text('sphereceti.toml'))
        self.assertEqual(report['roadmap']['state'], 'approved' if project.roadmap_approved else 'not_installed')
        self.assertFalse(report['setup']['merging_ready'])
        self.assertTrue(all(not item['enabled'] for item in report['capabilities'].values()))
        run.assert_not_called()

    @patch('sphereceti.cli.subprocess.run')
    def test_requested_policy_does_not_claim_verified_activation(self, run):
        policy = replace(DISABLED_POLICY, review_generation=True, posting=True, reporting=True,
                         merging=True, mathematical_paths=('SphereCeti/Math',),
                         authorized_reviewers=('user:7',))
        with patch('sphereceti.cli.parse_policy', return_value=policy):
            code, report = self.run_json('status', '--offline', '--json')
        self.assertEqual(code, 0)
        for name in ('review_generation', 'posting', 'merging'):
            capability = report['capabilities'][name]
            self.assertTrue(capability['implemented'])
            self.assertTrue(capability['policy_requested'])
            self.assertFalse(capability['enabled'])
            self.assertEqual(capability['readiness'], 'unverified')
        self.assertTrue(report['capabilities']['reporting']['policy_requested'])
        for name in ('authoring', 'reporting'):
            self.assertFalse(report['capabilities'][name]['implemented'])
            self.assertEqual(report['capabilities'][name]['readiness'], 'not_implemented')
        self.assertFalse(report['setup']['merging_ready'])
        self.assertTrue(report['merge_controller']['policy_requested'])
        self.assertFalse(report['merge_controller']['activation_verified'])
        run.assert_not_called()

    @patch('sphereceti.cli.subprocess.run')
    def test_human_status_distinguishes_policy_request_from_readiness(self, run):
        policy = replace(DISABLED_POLICY, review_generation=True, posting=True)
        output = io.StringIO()
        with patch('sphereceti.cli.parse_policy', return_value=policy), patch('sys.stdout', output):
            code = cli.main(['status', '--offline'])
        self.assertEqual(code, 0)
        self.assertIn('Repository policy requests: review_generation, posting.', output.getvalue())
        self.assertIn('Execution readiness is unverified', output.getvalue())
        self.assertNotIn('remain disabled', output.getvalue())
        run.assert_not_called()

    @patch('sphereceti.cli.subprocess.run')
    def test_available_empty_queue(self, run):
        run.return_value = subprocess.CompletedProcess([], 0, '[[]]', '')
        code, report = self.run_json('status', '--json')
        self.assertEqual(code, 0)
        self.assertEqual(report['queue'], {'state': 'available', 'pull_requests': []})
        argv = run.call_args.args[0]
        self.assertEqual(argv[:4], ['gh', 'api', '--paginate', '--slurp'])
        self.assertIn('repos/thefundamentaltheor3m/SphereCeti/pulls?', argv[4])

    @patch('sphereceti.cli.subprocess.run')
    def test_paginated_queue(self, run):
        run.return_value = subprocess.CompletedProcess([], 0, '[[{"number": 1, "title": "One"}], [{"number": 4, "title": "Four"}]]', '')
        code, report = self.run_json('status', '--json')
        self.assertEqual(code, 0)
        self.assertEqual([p['number'] for p in report['queue']['pull_requests']], [1, 4])

    @patch('sphereceti.cli.subprocess.run')
    def test_api_failures_never_look_like_no_work(self, run):
        for result in (subprocess.CompletedProcess([], 1, '', 'connection failed'),
                       subprocess.CompletedProcess([], 0, '{}', ''),
                       subprocess.CompletedProcess([], 0, '[]', ''),
                       subprocess.CompletedProcess([], 0, '[[{}]]', '')):
            run.return_value = result
            code, report = self.run_json('status', '--json')
            self.assertEqual(code, 1)
            self.assertEqual(report['queue']['state'], 'error')
            self.assertIsNone(report['queue']['pull_requests'])
        run.side_effect = subprocess.TimeoutExpired('gh', 45)
        code, report = self.run_json('status', '--json')
        self.assertEqual(code, 1)
        self.assertEqual(report['queue']['state'], 'error')

    @patch('sphereceti.cli.shutil.which', return_value=None)
    def test_doctor_reports_missing_commands(self, which):
        code, report = self.run_json('doctor', '--json', '--offline')
        self.assertEqual(code, 1)
        self.assertTrue(all(value is None for value in report['executables'].values()))

    def test_no_mutating_command_is_available(self):
        for command in ('work', 'merge', 'post'):
            with self.subTest(command=command), patch('sys.stderr', io.StringIO()), self.assertRaises(SystemExit) as error:
                cli.main([command])
            self.assertEqual(error.exception.code, 2)


if __name__ == '__main__':
    unittest.main()
