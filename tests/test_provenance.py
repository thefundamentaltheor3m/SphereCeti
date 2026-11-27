# SPDX-License-Identifier: Apache-2.0
"""Which build is running (`--version`), is it approved main (`doctor`), and the review's notice."""
from argparse import Namespace
from contextlib import contextmanager, redirect_stdout
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools' / 'project'))
from sphereceti import __version__, cli, provenance
from sphereceti.config import OperatorPreferences, parse_project, resource_text
from sphereceti.review_records import RecordError
from sphereceti.review_summary import announcing

MAIN = '90b086054294b549076792b59cf2e851c00ea511'
NEWER = 'abc1234' + '0' * 33
PACKAGE = Path(provenance.__file__).resolve().parent
UPDATE = 'uv tool install --force --refresh git+https://github.com/thefundamentaltheor3m/SphereCeti@main'


class FakeDistribution:
    """importlib.metadata's view of an installed distribution."""

    def __init__(self, direct_url, package_dir=PACKAGE):
        self.direct_url, self.package_dir = direct_url, package_dir

    def locate_file(self, name):
        return self.package_dir.parent / name

    def read_text(self, name):
        if name != 'direct_url.json' or self.direct_url is None:
            return None
        return self.direct_url if isinstance(self.direct_url, str) else json.dumps(self.direct_url)


GIT_INSTALL = {'url': 'https://github.com/thefundamentaltheor3m/SphereCeti',
               'vcs_info': {'vcs': 'git', 'commit_id': MAIN, 'requested_revision': 'main'}}


class InstalledTest(unittest.TestCase):
    def test_git_install_names_revision_and_commit(self):
        info = provenance.installed(distribution=FakeDistribution(GIT_INSTALL))
        self.assertEqual((info['kind'], info['commit'], info['label']), ('vcs', MAIN, 'main@90b0860'))
        self.assertEqual(provenance.version_string(distribution=FakeDistribution(GIT_INSTALL)),
                         f'{__version__} (main@90b0860)')
        pinned = {**GIT_INSTALL, 'vcs_info': {'vcs': 'git', 'commit_id': MAIN}}
        self.assertEqual(provenance.installed(distribution=FakeDistribution(pinned))['label'], 'commit@90b0860')

    def test_missing_malformed_local_and_foreign_metadata_is_a_local_build(self):
        with tempfile.TemporaryDirectory() as outside:  # not a Git checkout
            elsewhere = Path(outside) / 'sphereceti'
            cases = {
                'no direct_url.json': FakeDistribution(None, elsewhere),
                'malformed JSON': FakeDistribution('{not json', elsewhere),
                'path install': FakeDistribution({'url': 'file:///src', 'dir_info': {}}, elsewhere),
                'short commit': FakeDistribution({'vcs_info': {'commit_id': 'abc'}}, elsewhere),
            }
            for name, dist in cases.items():
                with self.subTest(name=name):
                    info = provenance.installed(distribution=dist, package_dir=elsewhere)
                    self.assertEqual((info['kind'], info['commit'], info['label']), ('local', None, 'local build'))
            editable = FakeDistribution({'url': 'file:///src', 'dir_info': {'editable': True}}, elsewhere)
            self.assertTrue(provenance.installed(distribution=editable, package_dir=elsewhere)['editable'])

    def test_metadata_of_another_copy_is_not_trusted(self):
        # A Git install elsewhere on sys.path must not label the source tree actually imported.
        with tempfile.TemporaryDirectory() as other:
            info = provenance.installed(distribution=FakeDistribution(GIT_INSTALL, Path(other) / 'sphereceti'))
        self.assertEqual(info['kind'], 'local')

    def test_source_checkout_adds_its_commit_read_only(self):
        head = subprocess.run(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], capture_output=True,
                              text=True).stdout.strip()
        info = provenance.installed(distribution=FakeDistribution(None))
        self.assertEqual(info['label'], f'local build, checkout {head[:7]}')
        with patch.object(provenance.metadata, 'distribution', side_effect=provenance.metadata.PackageNotFoundError):
            self.assertEqual(provenance.installed()['label'], f'local build, checkout {head[:7]}')

    def test_version_never_fails(self):
        with patch.object(provenance, 'installed', side_effect=RuntimeError('broken metadata')):
            self.assertEqual(provenance.version_string(), f'{__version__} (local build)')

    def test_cli_version_flag(self):
        result = subprocess.run([sys.executable, '-m', 'sphereceti.cli', '--version'], capture_output=True,
                                text=True, env={'PYTHONPATH': str(ROOT / 'tools/project'), 'PATH': '/usr/bin:/bin'},
                                cwd=tempfile.gettempdir(), timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertRegex(result.stdout, rf'^{__version__} \(local build(, checkout [0-9a-f]{{7}})?\)\n\Z')


def fake_github(tree, *, behind=0, status='identical', fail=False):
    calls = []

    def call(endpoint, **_):
        calls.append(endpoint)
        if fail:
            raise RecordError('GitHub operation failed')
        if endpoint.endswith('/commits/main'):
            return {'sha': NEWER}
        if '/git/trees/' in endpoint:
            return {'truncated': False, 'tree': [{'path': p, 'type': 'blob', 'sha': s} for p, s in tree.items()]}
        if '/compare/' in endpoint:
            return {'ahead_by': behind, 'behind_by': 0, 'status': status}
        raise AssertionError(endpoint)
    return call, calls


class CompareTest(unittest.TestCase):
    files = {'tools/project/sphereceti/cli.py': b'print(1)\n', 'policy/automation.toml': b'x = 1\n'}
    project = parse_project(resource_text('sphereceti.toml'))
    git_install = {'kind': 'vcs', 'commit': MAIN, 'label': 'main@90b0860'}

    def tree(self, **changed):
        return {p: provenance.blob_id(changed.get(p, b) if isinstance(changed.get(p, b), bytes) else b)
                for p, b in self.files.items()}

    def test_up_to_date(self):
        call, calls = fake_github(self.tree())
        result = provenance.compare(self.project, call, info=self.git_install, files=self.files)
        self.assertEqual((result['approved_main'], result['behind_by'], result['up_to_date']), (NEWER, 0, True))
        self.assertEqual(provenance.doctor_line(result), 'installed: main@90b0860 · up to date with approved main')
        self.assertIn(f'repos/thefundamentaltheor3m/SphereCeti/compare/{MAIN}...{NEWER}', calls)

    def test_behind_with_changed_tooling(self):
        tree = {**self.tree(), 'tools/project/sphereceti/cli.py': provenance.blob_id(b'print(2)\n')}
        call, _ = fake_github(tree, behind=3, status='ahead')
        result = provenance.compare(self.project, call, info=self.git_install, files=self.files)
        self.assertEqual((result['behind_by'], result['relation'], result['up_to_date']), (3, 'behind', False))
        self.assertEqual(provenance.doctor_line(result),
                         f'installed: main@90b0860 · 3 commits behind approved main (90b0860 → abc1234); '
                         f'update with: {UPDATE}')

    def test_behind_with_unchanged_tooling_is_still_official(self):
        # Consistent with the review path: only installed_tooling_matches_T decides officialness.
        call, _ = fake_github(self.tree(), behind=2, status='ahead')
        result = provenance.compare(self.project, call, info=self.git_install, files=self.files)
        self.assertTrue(result['up_to_date'])
        self.assertIn('2 commits behind approved main (90b0860 → abc1234), but its tooling is unchanged',
                      provenance.doctor_line(result))

    def test_local_build_and_divergence(self):
        local = {'kind': 'local', 'commit': None, 'label': 'local build'}
        call, calls = fake_github({})
        result = provenance.compare(self.project, call, info=local, files=self.files)
        self.assertEqual((result['behind_by'], result['up_to_date']), (None, False))
        self.assertFalse(any('/compare/' in c for c in calls))
        self.assertEqual(provenance.doctor_line(result),
                         f'installed: local build · not current approved main abc1234; update with: {UPDATE}')
        call, _ = fake_github({}, behind=1, status='diverged')
        diverged = provenance.compare(self.project, call, info=self.git_install, files=self.files)
        self.assertIn('diverged from approved main (90b0860 → abc1234)', provenance.doctor_line(diverged))


class DoctorTest(unittest.TestCase):
    def doctor(self, *args, github=None):
        out = io.StringIO()
        with patch.object(cli, 'pull_requests', return_value=[]), \
                patch('sphereceti.review_post.GitHub.call', side_effect=github or AssertionError('offline')), \
                redirect_stdout(out):
            code = cli.main(['doctor', *args])
        return code, out.getvalue()

    def test_offline_prints_the_installed_build_only(self):
        code, text = self.doctor('--offline')
        self.assertRegex(text, r'\ninstalled: local build(, checkout [0-9a-f]{7})?\n')
        code, text = self.doctor('--offline', '--json')
        installed = json.loads(text)['installed']
        self.assertEqual({k: installed[k] for k in ('approved_main', 'behind_by', 'up_to_date', 'state')},
                         {'approved_main': None, 'behind_by': None, 'up_to_date': None, 'state': 'not_checked'})
        self.assertIn('installed_commit', installed)

    def test_online_up_to_date_and_behind(self):
        from sphereceti.review_resources import tooling_files
        current = {p: provenance.blob_id(b) for p, b in tooling_files().items()}
        call, _ = fake_github(current)
        code, text = self.doctor('--json', github=lambda endpoint, **kw: call(endpoint))
        installed = json.loads(text)['installed']
        self.assertEqual((installed['approved_main'], installed['up_to_date'], installed['state']),
                         (NEWER, True, 'checked'))
        self.assertEqual(set(installed) >= {'installed_commit', 'approved_main', 'behind_by', 'up_to_date'}, True)
        stale = dict(current, **{'tools/project/sphereceti/cli.py': '0' * 40})
        call, _ = fake_github(stale)
        code, text = self.doctor(github=lambda endpoint, **kw: call(endpoint))
        self.assertIn('· not current approved main abc1234; update with: ' + UPDATE, text)

    def test_github_failure_does_not_fail_doctor(self):
        code_offline, _ = self.doctor('--offline')
        call, _ = fake_github({}, fail=True)
        code, text = self.doctor('--json', github=lambda endpoint, **kw: call(endpoint))
        installed = json.loads(text)['installed']
        self.assertEqual((installed['state'], installed['up_to_date']), ('error', None))
        self.assertEqual(code, code_offline)


class ReviewNoticeTest(unittest.TestCase):
    def report(self, matches):
        return {'repository': 'thefundamentaltheor3m/SphereCeti', 'pr': 54, 'head': 'a' * 40, 'base': 'b' * 40,
                'tooling': MAIN, 'tooling_approved': True, 'installed_tooling_matches_T': matches}

    def run_guard(self, report):
        events, sink = [], {}

        @contextmanager
        def inner(args, report, policy, client):
            yield None
        args = Namespace(provider=None, codex_model=None, claude_model=None, kiro_model=None, dry_run=False,
                         post=True, no_post=False, post_default=True)
        with patch.object(provenance, 'installed', return_value={'kind': 'vcs', 'commit': NEWER,
                                                                  'label': 'main@abc1234'}):
            with announcing(OperatorPreferences(provider='codex'), events.append, sink, inner=inner)(
                    args, report, None, None):
                events.append('provider called')
        return events, sink

    def test_stale_tooling_is_announced_before_any_model_call(self):
        events, sink = self.run_guard(self.report(False))
        self.assertTrue(events[0].startswith('Review #54'))
        self.assertEqual(events[1], 'Your sphereceti is not current main (installed main@abc1234, approved main '
                                    f'90b0860): this review will be advisory, not official. Update with: {UPDATE}')
        self.assertEqual(events[2], 'provider called')
        self.assertEqual(sink['tooling_notice'], events[1])

    def run_prompted(self, answer, **flags):
        events, calls = [], []
        args = Namespace(provider=None, codex_model=None, claude_model=None, kiro_model=None, dry_run=False,
                         post=True, no_post=False, post_default=True, **flags)

        @contextmanager
        def inner(args, report, policy, client):
            events.append('claim posted')
            yield None
        with patch.object(provenance, 'installed', return_value={'kind': 'vcs', 'commit': NEWER,
                                                                  'label': 'main@abc1234'}), \
                patch('sys.stdin.isatty', return_value=True), patch('sys.stdout.isatty', return_value=True), \
                patch('sphereceti.review_summary.ask', side_effect=lambda q: calls.append(q) or answer):
            with announcing(OperatorPreferences(provider='codex'), events.append, {}, inner=inner)(
                    args, self.report(False), None, None):
                events.append('provider called')
        return events, calls

    def test_on_a_terminal_an_advisory_review_is_asked_for_first(self):
        from sphereceti.local_review import ReviewError
        with self.assertRaisesRegex(ReviewError, 'advisory review declined'):
            self.run_prompted(False)
        events, calls = self.run_prompted(True)
        self.assertEqual(calls, ['Continue with an advisory review? [y/N] '])
        # The notice and the question come before the claim; the plan line and the model call after.
        self.assertTrue(events[0].startswith('Your sphereceti is not current main'))
        self.assertEqual(events[1], 'claim posted')
        self.assertTrue(events[2].startswith('Review #54'))
        self.assertEqual(events[-1], 'provider called')
        self.assertEqual(sum(e.startswith('Your sphereceti') for e in events), 1)
        events, calls = self.run_prompted(False, allow_advisory=True)  # --allow-advisory: no question
        self.assertEqual(calls, [])
        self.assertEqual(events[-1], 'provider called')

    def test_a_declined_advisory_review_claims_and_calls_nothing(self):
        from sphereceti.local_review import ReviewError
        events = []

        @contextmanager
        def inner(args, report, policy, client):
            events.append('claim posted')
            yield None
        args = Namespace(provider=None, codex_model=None, claude_model=None, kiro_model=None, dry_run=False,
                         post=True, no_post=False, post_default=True)
        with patch.object(provenance, 'installed', return_value={'kind': 'vcs', 'commit': NEWER,
                                                                  'label': 'main@abc1234'}), \
                patch('sys.stdin.isatty', return_value=True), patch('sys.stdout.isatty', return_value=True), \
                patch('sphereceti.review_summary.ask', return_value=False):
            with self.assertRaises(ReviewError):
                with announcing(OperatorPreferences(provider='codex'), events.append, {}, inner=inner)(
                        args, self.report(False), None, None):
                    events.append('provider called')
        self.assertEqual(len(events), 1)  # only the notice: no claim, no model call
        self.assertTrue(events[0].startswith('Your sphereceti is not current main'))

    def test_a_batch_or_a_non_terminal_run_continues_and_says_it_once(self):
        events = []
        args = Namespace(provider=None, codex_model=None, claude_model=None, kiro_model=None, dry_run=False,
                         post=True, no_post=False, post_default=True, new=True)

        @contextmanager
        def inner(args, report, policy, client):
            yield None
        with patch.object(provenance, 'installed', return_value={'kind': 'vcs', 'commit': NEWER,
                                                                  'label': 'main@abc1234'}), \
                patch('sys.stdin.isatty', return_value=True), patch('sys.stdout.isatty', return_value=True), \
                patch('sphereceti.review_summary.ask', side_effect=AssertionError('a batch never asks')):
            for _ in range(3):  # three batch items share the arguments
                with announcing(OperatorPreferences(provider='codex'), events.append, {}, inner=inner)(
                        args, self.report(False), None, None):
                    events.append('provider called')
        self.assertEqual(sum(e.startswith('Your sphereceti') for e in events), 1)
        self.assertEqual(events.count('provider called'), 3)

    def test_current_tooling_or_unknown_evidence_adds_nothing(self):
        for matches in (True, None):
            with self.subTest(matches=matches):
                report = self.report(matches)
                if matches is None:
                    del report['installed_tooling_matches_T']
                events, sink = self.run_guard(report)
                self.assertEqual(len(events), 2)
                self.assertIsNone(sink['tooling_notice'])


if __name__ == '__main__':
    unittest.main()
