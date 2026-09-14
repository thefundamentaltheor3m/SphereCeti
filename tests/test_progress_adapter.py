import contextlib
from datetime import datetime, timezone
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools/project'))
sys.path.insert(0, str(ROOT / 'tests'))
from sphereceti.config import parse_project, resource_text
from sphereceti import cli, progress
from sphereceti.progress_evidence import ProgressError, decode, digest, encode, load_evidence
from sphereceti.progress_sources import sources, git_run
from progress_fixture import PROSE, fixture, git, commit, make_docs


class ProgressAdapterTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.project = parse_project(resource_text('sphereceti.toml'))
        self.repo, self.docs, self.start, self.end = fixture(self.root, self.project)
        self.prose = self.root / 'prose.json'
        self.prose.write_bytes(encode({'status': PROSE, 'progress': PROSE,
                                      'citations': ['targetEntry', 'admittedGlue']}))
        self.output = self.root / 'draft'
        self.args = SimpleNamespace(repo=self.repo, evidence_dir=self.docs, from_sha=self.start,
                                    prose=self.prose, output=self.output, draft=self.output, candidate=None)

    def plan(self, **kwargs):
        return progress.make_plan(self.repo, self.project, evidence_dir=self.docs, from_sha=self.start, **kwargs)

    def prepare(self):
        return progress.prepare(self.args, self.project)

    def change_index(self, change):
        p = self.docs / 'declarations.json'; data = decode(p.read_bytes()); change(data); p.write_bytes(encode(data))

    def test_missing_published_evidence_does_not_query_git_or_claim_completion(self):
        with patch.object(progress, 'git', side_effect=AssertionError('must not run')):
            report = progress.make_plan(self.repo, self.project)
        self.assertEqual(report['state'], 'missing_evidence')
        self.assertEqual(report['achievements'], [])
        self.assertIs(report['production_evidence'], False)

    def test_plan_ends_at_documented_revision_not_local_head(self):
        (self.repo / 'later.txt').write_text('later')
        head = commit(self.repo, 'later change (#22)')
        plan = self.plan()
        self.assertEqual(plan['source_head'], head)
        self.assertEqual(plan['to_sha'], self.end)
        self.assertEqual(plan['prs'], [21])
        self.assertEqual(plan['evidence_mode'], 'fixture-preview')
        self.assertTrue(all(not d['achievement'] for d in plan['declarations']))
        statuses = {d['name']: d['status'] for d in plan['declarations']}
        self.assertEqual(statuses['targetEntry'], 'roadmap-target')
        self.assertEqual(statuses['admittedGlue'], 'admission-dependent')
        self.assertIn('not claims of introduction', plan['fact_scope'])

    def test_private_upstream_resources_are_used_without_global_progress_package(self):
        import importlib.util
        self.assertIsNone(importlib.util.find_spec('progress'))
        self.assertEqual(sources()['files'].STATUS_MARKER, 'tauceti-status:v1')
        self.assertIn('progress', sources()['prompts'])
        self.assertIn('human review', progress.writing_prompt(self.plan()))

    def test_first_report_requires_exact_explicit_cursor(self):
        value = progress.make_plan(self.repo, self.project, evidence_dir=self.docs)
        self.assertEqual(value['state'], 'missing_evidence')
        with self.assertRaises(ProgressError):
            progress.make_plan(self.repo, self.project, evidence_dir=self.docs, from_sha=self.start[:7])

    def test_cursor_ahead_of_published_docs_is_refused(self):
        (self.repo / 'later').write_text('later'); later = commit(self.repo, 'later (#22)')
        with self.assertRaises(ProgressError):
            progress.make_plan(self.repo, self.project, evidence_dir=self.docs, from_sha=later)

    def test_rewritten_history_is_refused(self):
        git(self.repo, 'checkout', '--orphan', 'other')
        other = commit(self.repo, 'other root')
        with self.assertRaises(ProgressError):
            progress.make_plan(self.repo, self.project, evidence_dir=self.docs, from_sha=other)

    def test_published_reader_checks_revision_twice_and_actual_links(self):
        calls = []
        def read(url):
            calls.append(url); return (self.docs / url.removeprefix('https://docs.example/')).read_bytes()
        evidence = load_evidence(self.project, url='https://docs.example', reader=read)
        self.assertEqual(evidence['mode'], 'published')
        self.assertEqual(calls.count('https://docs.example/SOURCE_SHA'), 2)
        self.assertEqual(evidence['source_revision'], self.end)

    def test_publication_race_and_noncanonical_marker_are_refused(self):
        calls = 0
        def read(url):
            nonlocal calls
            if url.endswith('SOURCE_SHA'):
                calls += 1
                if calls == 2: return (self.start + '\n').encode()
            return (self.docs / url.removeprefix('https://docs.example/')).read_bytes()
        with self.assertRaisesRegex(ProgressError, 'changed during'):
            load_evidence(self.project, url='https://docs.example', reader=read)
        (self.docs / 'SOURCE_SHA').write_bytes((self.end + '\0\n').encode())
        with self.assertRaises(ProgressError): self.plan()

    def test_identity_production_claim_and_dependency_drift_are_refused(self):
        original = (self.docs / 'declarations.json').read_bytes()
        changes = [lambda d: d.update(repository='other/repository'),
                   lambda d: d.update(production_evidence=True),
                   lambda d: d.update(source_revision=self.start),
                   lambda d: d['dependencies']['packages'][0].update(rev='a' * 40)]
        for change in changes:
            (self.docs / 'declarations.json').write_bytes(original)
            self.change_index(change)
            with self.subTest(change=change), self.assertRaises(ProgressError): self.plan()

    def test_forged_classification_link_and_missing_anchor_are_refused(self):
        original = (self.docs / 'declarations.json').read_bytes()
        for key, val in [('status', 'proved'), ('url', 'https://attacker.invalid'), ('source_url', 'https://attacker.invalid')]:
            (self.docs / 'declarations.json').write_bytes(original)
            self.change_index(lambda d: d['declarations'][0].update({key: val}))
            with self.subTest(key=key), self.assertRaises(ProgressError): self.plan()
        (self.docs / 'declarations.json').write_bytes(original)
        (self.docs / 'library/index.html').write_text('<html>no anchors</html>')
        with self.assertRaises(ProgressError): self.plan()

    def test_incomplete_index_and_forged_audit_are_refused(self):
        self.change_index(lambda d: d['declarations'].pop())
        with self.assertRaises(ProgressError): self.plan()
        (self.docs / 'audit.json').write_text('{}')
        with self.assertRaises(ProgressError): self.plan()

    def test_duplicate_json_and_symlink_evidence_are_refused(self):
        p = self.docs / 'declarations.json'; data = p.read_bytes()
        p.write_bytes(data.replace(b'"schema_version": 1', b'"schema_version": 1, "schema_version": 1'))
        with self.assertRaises(ProgressError): self.plan()
        p.unlink(); outside = self.root / 'outside.json'; outside.write_bytes(data); p.symlink_to(outside)
        with self.assertRaises(ProgressError): self.plan()

    def test_prepare_and_validate_are_local_and_preserve_roadmap(self):
        before = (self.repo / 'README.md').read_bytes()
        value = self.prepare()
        self.assertEqual(value['state'], 'prepared')
        self.assertEqual(progress.validate(self.args, self.project)['state'], 'valid')
        self.assertEqual((self.repo / 'README.md').read_bytes(), before)
        self.assertFalse((self.repo / 'STATUS.md').exists())
        body = (self.output / 'changes/STATUS.md').read_text()
        self.assertIn('not proved milestones', body)
        self.assertIn('Fixture preview', body)
        self.assertIn('admission-dependent', body)

    def test_output_inside_checkout_and_overwrite_are_refused(self):
        self.args.output = self.repo / 'draft'
        with self.assertRaises(ProgressError): self.prepare()
        self.args.output = self.output
        self.prepare()
        with self.assertRaises(FileExistsError): self.prepare()

    def test_unverified_links_markers_and_unknown_citations_are_refused(self):
        for bad in (PROSE + ' https://attacker.invalid', PROSE + '<!--tauceti-progress:v1 {}-->', PROSE + '<a>hidden</a>'):
            self.prose.write_bytes(encode({'status': bad, 'progress': PROSE, 'citations': []}))
            with self.assertRaises(ValueError): self.prepare()
        self.prose.write_bytes(encode({'status': PROSE, 'progress': PROSE, 'citations': ['missing']}))
        with self.assertRaises(ProgressError): self.prepare()

    def test_draft_tampering_and_extra_roadmap_path_are_refused(self):
        self.prepare()
        status = self.output / 'changes/STATUS.md'; data = status.read_bytes(); status.write_bytes(data + b'changed')
        with self.assertRaises(ProgressError): progress.validate(self.args, self.project)
        status.write_bytes(data)
        (self.output / 'changes/README.md').write_text('rewrite')
        with self.assertRaises(ProgressError): progress.validate(self.args, self.project)

    def test_source_head_or_evidence_advancement_invalidates_draft(self):
        self.prepare()
        (self.repo / 'later').write_text('later'); commit(self.repo, 'later (#22)')
        with self.assertRaisesRegex(ProgressError, 'stale'): progress.validate(self.args, self.project)

    def test_append_preserves_old_bytes_and_uses_progress_cursor(self):
        self.prepare()
        for name in progress.REPORTS: shutil.copyfile(self.output / 'changes' / name, self.repo / name)
        commit(self.repo, 'progress: first report')
        old = (self.repo / 'PROGRESS.md').read_bytes()
        (self.repo / 'SphereCeti/Basic.lean').write_text('-- next synthetic module change\n')
        end = commit(self.repo, 'next update (#22)')
        docs = self.root / 'docs2'; make_docs(docs, end, self.project)
        self.prose.write_bytes(encode({'status': PROSE, 'progress': PROSE, 'citations': ['admittedGlue']}))
        self.args.evidence_dir = docs; self.args.from_sha = None; self.args.output = self.root / 'draft2'
        progress.prepare(self.args, self.project)
        value = (self.args.output / 'changes/PROGRESS.md').read_bytes()
        self.assertTrue(value.startswith(old))
        plan = decode((self.args.output / 'plan.json').read_bytes())
        self.assertEqual(plan['from_sha'], self.end)
        self.assertEqual(plan['prs'], [22])
        with self.assertRaises(ProgressError):
            progress.make_plan(self.repo, self.project, evidence_dir=docs, from_sha=self.start)

    def test_cadence_uses_committed_report_time(self):
        self.prepare()
        for name in progress.REPORTS: shutil.copyfile(self.output / 'changes' / name, self.repo / name)
        commit(self.repo, 'progress: first')
        (self.repo / 'next').write_text('next'); end = commit(self.repo, 'next (#22)')
        docs = self.root / 'nextdocs'; make_docs(docs, end, self.project)
        plan = progress.make_plan(self.repo, self.project, evidence_dir=docs,
                                  now=datetime(2000, 1, 1, 13, tzinfo=timezone.utc))
        self.assertEqual(plan['state'], 'not_due')

    def test_candidate_scope_checks_actual_git_diff(self):
        self.prepare(); base = git(self.repo, 'rev-parse', 'HEAD')
        for name in progress.REPORTS: shutil.copyfile(self.output / 'changes' / name, self.repo / name)
        candidate = commit(self.repo, 'progress: candidate')
        git(self.repo, 'checkout', '--detach', base)
        self.args.candidate = candidate
        self.assertEqual(progress.validate(self.args, self.project)['state'], 'valid')
        draft_status = self.output / 'changes/STATUS.md'; original = draft_status.read_bytes()
        draft_status.write_text('altered draft alongside valid candidate')
        with self.assertRaisesRegex(ProgressError, 'draft report bytes'):
            progress.validate(self.args, self.project)
        draft_status.write_bytes(original)
        git(self.repo, 'checkout', '--detach', candidate)
        (self.repo / 'README.md').write_text('forbidden rewrite'); bad = commit(self.repo, 'bad scope')
        git(self.repo, 'checkout', '--detach', base); self.args.candidate = bad
        with self.assertRaisesRegex(ProgressError, 'protected'): progress.validate(self.args, self.project)

    def test_executable_candidate_report_is_refused(self):
        self.prepare(); base = git(self.repo, 'rev-parse', 'HEAD')
        for name in progress.REPORTS: shutil.copyfile(self.output / 'changes' / name, self.repo / name)
        (self.repo / 'STATUS.md').chmod(0o755)
        self.args.candidate = commit(self.repo, 'executable report')
        git(self.repo, 'checkout', '--detach', base)
        with self.assertRaisesRegex(ProgressError, 'ordinary non-executable'):
            progress.validate(self.args, self.project)

    def test_altered_writing_context_and_symlink_draft_are_refused(self):
        self.prepare()
        prompt = self.output / 'prompt.txt'; original = prompt.read_bytes()
        prompt.write_text('altered context')
        with self.assertRaisesRegex(ProgressError, 'context'): progress.validate(self.args, self.project)
        prompt.write_bytes(original)
        status = self.output / 'changes/STATUS.md'; payload = status.read_bytes(); status.unlink()
        outside = self.root / 'outside.md'; outside.write_bytes(payload); status.symlink_to(outside)
        with self.assertRaisesRegex(ProgressError, 'regular|symlink'): progress.validate(self.args, self.project)

    def test_empty_window_does_not_advance_a_report(self):
        plan = progress.make_plan(self.repo, self.project, evidence_dir=self.docs, from_sha=self.end)
        self.assertEqual(plan['state'], 'no_changes')
        self.args.from_sha = self.end
        with self.assertRaises(ProgressError): self.prepare()
        self.assertFalse(self.output.exists())

    def test_git_transport_removes_credentials_and_refuses_mutations(self):
        with patch('sphereceti.progress_sources.subprocess.run') as run:
            git_run(['git', '-C', str(self.repo), 'log', '--format=%s'])
            env = run.call_args.kwargs['env']
            self.assertNotIn('GH_TOKEN', env)
            self.assertEqual(env['GIT_ALLOW_PROTOCOL'], '')
            self.assertIn('core.fsmonitor=false', run.call_args.args[0])
        with self.assertRaises(ValueError): git_run(['git', '-C', str(self.repo), 'push'])

    def test_cli_plan_prompt_prepare_validate(self):
        base = ['--repo', str(self.repo), '--evidence-dir', str(self.docs)]
        invocations = [(['plan', *base, '--from', self.start, '--json'], 'ready'),
                       (['prompt', *base, '--from', self.start, '--json'], 'ready'),
                       (['prepare', *base, '--from', self.start, '--prose', str(self.prose), '--output', str(self.output), '--json'], 'prepared'),
                       (['validate', *base, '--draft', str(self.output), '--json'], 'valid')]
        for args, state in invocations:
            out = io.StringIO()
            with contextlib.redirect_stdout(out): self.assertEqual(cli.main(['progress', *args]), 0)
            self.assertEqual(json.loads(out.getvalue())['state'], state)


if __name__ == '__main__': unittest.main()
