"""Static roadmap checks for registered sibling roadmaps, run on disposable copies of the checkout."""
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SIBLING = ('[[sources.additional_roadmaps]]\nname = "fixture-sibling"\n'
           'document = "SphereCetiRoadmap/FixtureSibling/README.md"\n'
           'companions = ["SphereCetiRoadmap/FixtureSibling/NOTES.md"]\n'
           'targets = ["SphereCetiRoadmap/FixtureSibling/Targets.lean"]\n\n')
TARGET = 'module\n\n/-- Fixture target. -/\ntheorem fixtureTarget : 1 = 1 := by\n  sorry\n'


class RoadmapChecksTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='sphereceti-roadmap-checks-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'repo'
        shutil.copytree(ROOT, self.root, symlinks=True,
                        ignore=lambda d, names: {'.git', '.lake', '.venv', '__pycache__'} & set(names))
        profile = self.root / 'sphereceti.toml'
        text = profile.read_text()
        self.assertEqual(text.count('\n[dependencies]'), 1)
        profile.write_text(text.replace('\n[dependencies]', '\n' + SIBLING + '[dependencies]'))
        self.write('SphereCetiRoadmap/FixtureSibling/README.md', 'See [notes](NOTES.md).\n')
        self.write('SphereCetiRoadmap/FixtureSibling/NOTES.md', 'Coefficient `[q⁻¹](p - m)` notation.\n')
        self.write('SphereCetiRoadmap/FixtureSibling/Targets.lean', TARGET)
        aggregator = self.root / 'SphereCetiRoadmap.lean'
        aggregator.write_text(aggregator.read_text() + 'public import SphereCetiRoadmap.FixtureSibling.Targets\n')
        self.append('VALIDATION.md', '\nThe fixture has 1 intentional `sorry` commands in the\n'
                    '`fixture-sibling` roadmap.\n')
        # Errors unrelated to the fixture (for example a sibling roadmap still being drafted) are
        # the baseline; each test asserts on the errors its own change adds or removes.
        self.baseline, _ = self.run_check()

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def append(self, path, text):
        target = self.root / path
        target.write_text(target.read_text() + text)

    def run_check(self):
        result = subprocess.run([sys.executable, str(self.root / 'scripts/check_roadmap.py')],
                                cwd=self.root, capture_output=True, text=True, timeout=60)
        errors = set(re.findall(r'^ERROR: (.*)$', result.stderr, re.M))
        self.assertEqual(result.returncode != 0, bool(errors), result.stderr)
        return errors, result.stdout

    def added_errors(self):
        errors, _ = self.run_check()
        return errors - self.baseline

    def test_fixture_sibling_is_accepted_and_counted_separately(self):
        self.assertFalse({e for e in self.baseline if 'FixtureSibling' in e or 'fixture-sibling' in e},
                         self.baseline)
        self.assertFalse({e for e in self.baseline if 'Pinned.lean' in e}, self.baseline)
        _, stdout = self.run_check()
        self.assertIn('1 intentional sorry commands in fixture-sibling', stdout)
        self.assertRegex(stdout, r'roadmap static checks: \d+ intentional sorry commands\n')

    def test_nested_targets_get_the_generic_lean_checks(self):
        self.write('SphereCetiRoadmap/FixtureSibling/Targets.lean',
                   TARGET + 'theorem vacuous : True := by\n  exact True.intro')
        self.assertTrue({'vacuous True target in FixtureSibling/Targets.lean',
                         'vacuous True proof in FixtureSibling/Targets.lean',
                         'missing final newline in FixtureSibling/Targets.lean'} <= self.added_errors())

    def test_unregistered_nested_lean_source_is_rejected(self):
        self.write('SphereCetiRoadmap/FixtureSibling/Extra.lean', 'module\n')
        self.assertIn('roadmap Lean source is not registered in sphereceti.toml: '
                      'SphereCetiRoadmap/FixtureSibling/Extra.lean', self.added_errors())

    def test_registered_sources_must_exist(self):
        (self.root / 'SphereCetiRoadmap/FixtureSibling/NOTES.md').unlink()
        added = self.added_errors()
        self.assertIn('registered roadmap source is missing: SphereCetiRoadmap/FixtureSibling/NOTES.md', added)
        self.assertIn('broken local link in SphereCetiRoadmap/FixtureSibling/README.md: NOTES.md', added)

    def test_companion_links_are_checked_but_code_spans_are_not_links(self):
        self.append('SphereCetiRoadmap/FixtureSibling/NOTES.md', 'See [gone](missing.md).\n')
        added = self.added_errors()
        self.assertEqual(added, {'broken local link in SphereCetiRoadmap/FixtureSibling/NOTES.md: missing.md'})

    def test_sibling_sorry_count_is_separate_and_exact(self):
        self.append('SphereCetiRoadmap/FixtureSibling/Targets.lean',
                    'theorem second : 2 = 2 := by\n  sorry\n')
        self.assertEqual(self.added_errors(),
                         {'VALIDATION.md has a stale intentional-sorry count for the fixture-sibling roadmap'})
        self.append('VALIDATION.md', '\n2 intentional `sorry` commands in the `fixture-sibling` roadmap.\n')
        self.assertEqual(self.added_errors(), set())

    def test_sibling_statement_cannot_stand_for_the_primary_count(self):
        _, stdout = self.run_check()
        primary = re.search(r'roadmap static checks: (\d+) intentional sorry commands\n', stdout).group(1)
        validation = self.root / 'VALIDATION.md'
        text = validation.read_text()
        self.assertIn(f'{primary} intentional `sorry` commands', text)
        validation.write_text(text.replace(f'{primary} intentional `sorry` commands', 'N/A') +
                              f'\n{primary} intentional `sorry` commands in the `other` roadmap.\n')
        self.assertIn('VALIDATION.md has a stale intentional-sorry count', self.added_errors())

    def test_aggregator_must_import_each_registered_target(self):
        aggregator = self.root / 'SphereCetiRoadmap.lean'
        aggregator.write_text(aggregator.read_text().replace(
            'public import SphereCetiRoadmap.FixtureSibling.Targets\n', ''))
        self.assertEqual(self.added_errors(), {'SphereCetiRoadmap.lean does not import the registered '
                                               'target SphereCetiRoadmap.FixtureSibling.Targets'})

    def test_invalid_registration_fails_closed(self):
        profile = self.root / 'sphereceti.toml'
        profile.write_text(profile.read_text().replace('name = "fixture-sibling"', 'name = "Fixture Sibling"'))
        result = subprocess.run([sys.executable, str(self.root / 'scripts/check_roadmap.py')],
                                cwd=self.root, capture_output=True, text=True, timeout=60)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('ERROR: sphereceti.toml: additional roadmap name', result.stderr)


if __name__ == '__main__':
    unittest.main()
