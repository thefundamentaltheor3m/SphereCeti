"""Profile validation, policy isolation, and unknown-vs-empty queue contracts."""

from dataclasses import asdict
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


class ProjectConfigTest(unittest.TestCase):
    def test_shipped_configuration_and_pins(self):
        profile = parse_project(resource_text('sphereceti.toml'))
        self.assertEqual(profile.phase, 'scaffold')
        self.assertFalse(profile.roadmap_approved)
        self.assertEqual(profile.implementation_repository, 'thefundamentaltheor3m/Sphere-Packing-Lean')
        root = Path(__file__).resolve().parents[1]
        self.assertEqual(profile.lean, (root / 'lean-toolchain').read_text().strip())
        manifest = json.loads((root / 'lake-manifest.json').read_text())
        packages = {p['name']: p for p in manifest['packages']}
        self.assertEqual(profile.tauceti, packages['TauCeti']['rev'])
        self.assertEqual(profile.mathlib, packages['mathlib']['rev'])

    def test_invalid_profile_is_rejected(self):
        original = resource_text('sphereceti.toml')
        cases = [original.replace('roadmap_approved = false', 'roadmap_approved = true'),
                 original.replace('schema_version = 1', 'schema_version = 2'),
                 original.replace('library_root = "SphereCeti"', 'library_root = "../Elsewhere"'),
                 original.replace('library_root = "SphereCeti"', 'library_root = "./"'),
                 original.replace('8671bee98125933c56b9b00a08ded873b77dd23b', 'main')]
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

    def test_policy_defaults_and_invalid_types(self):
        text = resource_text('automation.toml')
        policy = parse_policy(text)
        self.assertFalse(any(asdict(policy).values()))
        for bad in (text.replace('posting = false', 'posting = "false"'),
                    text.replace('merging = false', 'merging = true')):
            with self.assertRaises(ConfigError):
                parse_policy(bad)

    def test_source_lock_requires_exact_provenance_and_reuse_terms(self):
        text = resource_text('upstream-lock.toml')
        entries = parse_source_lock(text)
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
        self.assertEqual(report['roadmap']['state'], 'not_installed')
        self.assertFalse(report['setup']['merging_ready'])
        self.assertTrue(all(not item['enabled'] for item in report['capabilities'].values()))
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
        for command in ('work', 'review', 'merge', 'post'):
            with self.subTest(command=command), patch('sys.stderr', io.StringIO()), self.assertRaises(SystemExit) as error:
                cli.main([command])
            self.assertEqual(error.exception.code, 2)


if __name__ == '__main__':
    unittest.main()
