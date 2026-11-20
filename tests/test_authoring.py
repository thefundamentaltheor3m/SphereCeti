# SPDX-License-Identifier: Apache-2.0
"""Local exact-object handoff contracts; no providers or external writes."""
import argparse
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti import authoring, cli
from sphereceti.config import parse_project, resource_text
from sphereceti.gate import GateError
from sphereceti.local_review import ReviewError

PROJECT = parse_project(resource_text('sphereceti.toml'))


def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args], stderr=subprocess.DEVNULL).decode().strip()


class HandoffTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.roadmap = self.repository('roadmap', {
            PROJECT.roadmap_document: '# Roadmap\n\n## Tiny target\n\nPreserve the theorem statement.\n',
            PROJECT.roadmap_targets: 'theorem target : 1 = 1 := by sorry\n',
            'sphereceti.toml': 'implementation_repository = "attacker/wrong"\n',
        })
        self.production = self.repository('production', {'Packing/Basic.lean': 'theorem existing : 1 = 1 := rfl\n'})
        self.rsha = git(self.roadmap, 'rev-parse', 'HEAD')
        self.psha = git(self.production, 'rev-parse', 'HEAD')
        self.parser = argparse.ArgumentParser()
        authoring.add_parser(self.parser.add_subparsers(dest='command', required=True))

    def repository(self, name, files):
        repo = self.root / name
        repo.mkdir()
        git(repo, 'init', '--quiet')
        git(repo, 'config', 'user.email', 'fixture@example.invalid')
        git(repo, 'config', 'user.name', 'Fixture')
        for name, body in files.items():
            path = repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(body)
        git(repo, 'add', '.')
        git(repo, 'commit', '--quiet', '-m', 'fixture')
        return repo

    def argv(self, *extra):
        return ['author', 'plan', '--roadmap-repo', str(self.roadmap), '--roadmap', self.rsha,
                '--implementation-repo', str(self.production), '--implementation', self.psha,
                '--reference', PROJECT.roadmap_document + '#tiny-target', '--task', 'Propose one helper lemma.',
                '--allow-path', 'Packing/Basic.lean', *extra]

    def run_plan(self, *extra):
        return authoring.run(self.parser.parse_args(self.argv(*extra)), PROJECT)

    def test_exact_sources_dirty_trees_and_no_authority(self):
        first = self.run_plan()
        (self.production / 'Packing/Basic.lean').write_text('uncommitted unrelated content\n')
        (self.roadmap / PROJECT.roadmap_document).write_text('uncommitted replacement\n')
        before = git(self.production, 'status', '--porcelain')
        second = self.run_plan()
        self.assertEqual(first, second)
        self.assertEqual(before, git(self.production, 'status', '--porcelain'))
        self.assertEqual(second['destination'], PROJECT.implementation_repository)
        self.assertIn('Preserve the theorem', second['roadmap_excerpt'])
        self.assertEqual(second['implementation']['revision'], self.psha)
        self.assertEqual(second['authority'], 'local_unverified')
        for key in ('executable', 'publication_allowed', 'merge_eligible', 'source_identity_verified',
                    'source_approval_verified', 'prerequisites_verified'):
            self.assertFalse(second[key])

    def test_full_existing_commits_required(self):
        for option, revision in (('--roadmap', 'HEAD'), ('--implementation', self.psha[:12]),
                                 ('--implementation', 'f' * 40)):
            with self.subTest(revision=revision), self.assertRaises((ReviewError, GateError)):
                self.run_plan(option, revision)

    def test_configured_roadmap_sources_are_required_at_exact_revision(self):
        for name in (PROJECT.roadmap_document, PROJECT.roadmap_targets):
            files = {
                PROJECT.roadmap_document: '# Roadmap\n\n## Tiny target\nSelected source.\n',
                PROJECT.roadmap_targets: 'theorem target : 1 = 1 := by sorry\n',
            }
            del files[name]
            repo = self.repository('missing-' + Path(name).stem, files)
            revision = git(repo, 'rev-parse', 'HEAD')
            with self.subTest(source=name), self.assertRaisesRegex(ValueError, 'required source'):
                self.run_plan('--roadmap-repo', str(repo), '--roadmap', revision)

    def test_promisor_store_is_rejected_without_fetch(self):
        git(self.production, 'config', 'remote.origin.promisor', 'true')
        with self.assertRaisesRegex(ReviewError, 'promisor'):
            self.run_plan()

    def test_ordinary_bounded_explicit_paths(self):
        invalid = ('../Other.lean', '/tmp/Other.lean', 'Packing//Basic.lean', './Packing/Basic.lean',
                   'Packing/../Basic.lean', '.github/workflows/build.md', '.lake/Thing.lean',
                   'Packing/*.lean', 'Packing/Basic.lean/Other.lean', 'Packing', 'AGENTS.md',
                   'lakefile.lean', 'Packing/Basic.lean\n')
        # lakefile.lean is executable project configuration, even though its suffix is .lean.
        for path in invalid:
            args = self.parser.parse_args(self.argv())
            args.allow_path = [path]
            with self.subTest(path=path), self.assertRaises(ValueError):
                authoring.run(args, PROJECT)
        for paths in (['Packing/Basic.lean'] * 2, [f'Packing/New{i}.lean' for i in range(9)]):
            args = self.parser.parse_args(self.argv())
            args.allow_path = paths
            with self.assertRaises(ValueError):
                authoring.run(args, PROJECT)
        report = self.run_plan('--allow-path', 'Packing/New.lean')
        self.assertEqual(report['implementation']['files'][1], {'path': 'Packing/New.lean', 'state': 'new'})
        for args in (('--max-changed-lines', '0'), ('--max-changed-lines', '501'),
                     ('--time-limit-minutes', '121')):
            with self.assertRaises(ValueError):
                self.run_plan(*args)

    def test_reference_must_resolve_to_configured_roadmap_heading(self):
        for reference in ('OTHER.md#tiny-target', 'README.md#missing', 'README.md#tiny-target\n'):
            with self.subTest(reference=reference), self.assertRaises(ValueError):
                self.run_plan('--reference', reference)

    def test_fenced_example_headings_are_not_roadmap_references(self):
        for indent in ('', ' ', '  ', '   '):
            for opener, false_closer, closer in (('```lean', '~~~', '```'),
                                                 ('~~~text', '```', '~~~~'),
                                                 ('````lean', '```', '`````'),
                                                 ('~~~~', '~~~', '~~~~')):
                document = ('# Roadmap\n' + indent + opener + '\n## Hidden target\n'
                            + indent + false_closer + '\n## Still hidden\n'
                            + indent + closer + '  \n   ## Real target\nVisible text.\n')
                with self.subTest(indent=indent, opener=opener, false_closer=false_closer):
                    for anchor in ('hidden-target', 'still-hidden'):
                        with self.assertRaises(ValueError):
                            authoring.section(document, 'README.md#' + anchor, 'README.md')
                    excerpt, truncated = authoring.section(document, 'README.md#real-target', 'README.md')
                    self.assertIn('Visible text.', excerpt)
                    self.assertNotIn('Hidden target', excerpt)
                    self.assertFalse(truncated)

    def test_fence_with_trailing_text_does_not_close_example(self):
        document = ('# Roadmap\n```lean\n``` not-a-closer\n## Hidden target\n```\n'
                    '## Real target\nVisible text.\n')
        with self.assertRaises(ValueError):
            authoring.section(document, 'README.md#hidden-target', 'README.md')
        excerpt, _ = authoring.section(document, 'README.md#real-target', 'README.md')
        self.assertIn('Visible text.', excerpt)

    def test_symlink_and_executable_source_files_are_rejected(self):
        source = self.production / 'Packing/Basic.lean'
        source.chmod(0o755)
        git(self.production, 'add', '.')
        git(self.production, 'commit', '--quiet', '-m', 'executable source')
        executable = git(self.production, 'rev-parse', 'HEAD')
        with self.assertRaisesRegex(ValueError, 'non-executable'):
            self.run_plan('--implementation', executable)
        source.chmod(0o644)
        (self.production / 'Packing/Link.lean').symlink_to('Basic.lean')
        git(self.production, 'add', '.')
        git(self.production, 'commit', '--quiet', '-m', 'linked source')
        linked = git(self.production, 'rev-parse', 'HEAD')
        with self.assertRaisesRegex(GateError, 'symlink/submodule'):
            self.run_plan('--implementation', linked)

    def test_outputs_are_new_outside_sources_and_never_overwritten(self):
        output = self.root / 'handoff'
        report = self.run_plan('--output', str(output))
        self.assertEqual(json.loads((output / 'plan.json').read_text()), report)
        self.assertIn('does not authorize execution', (output / 'brief.md').read_text())
        original = (output / 'plan.json').read_bytes()
        with self.assertRaises(ValueError):
            self.run_plan('--output', str(output))
        self.assertEqual((output / 'plan.json').read_bytes(), original)
        with self.assertRaises(ValueError):
            self.run_plan('--output', str(self.production / 'handoff'))
        with self.assertRaises(ValueError):
            self.run_plan('--implementation-repo', str(self.production / '.git'),
                          '--output', str(self.production / 'handoff'))
        outside = self.root / 'outside'
        outside.mkdir()
        for source in (self.production, self.roadmap):
            alias = outside / '..' / source.name / 'handoff'
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.run_plan('--output', str(alias))
            self.assertFalse((source / 'handoff').exists())
        link = self.root / 'link'
        link.symlink_to(self.production, target_is_directory=True)
        with self.assertRaises(ValueError):
            self.run_plan('--output', str(link / 'handoff'))
        self.assertFalse((self.production / 'handoff').exists())

    def test_foreign_cwd_cannot_override_identity_or_policy(self):
        foreign = self.root / 'foreign'
        foreign.mkdir()
        (foreign / 'sphereceti.toml').write_text('implementation_repository = "attacker/wrong"')
        (foreign / 'policy').mkdir()
        (foreign / 'policy/automation.toml').write_text('authoring = true\nmerging = true\n')
        previous = Path.cwd()
        stream = io.StringIO()
        try:
            os.chdir(foreign)
            with redirect_stdout(stream):
                self.assertEqual(cli.main(self.argv()), 0)
        finally:
            os.chdir(previous)
        report = json.loads(stream.getvalue())
        self.assertEqual(report['destination'], PROJECT.implementation_repository)
        self.assertFalse(report['publication_allowed'])


if __name__ == '__main__':
    unittest.main()
