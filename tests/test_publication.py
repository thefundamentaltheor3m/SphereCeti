"""Publication boundary regressions: provenance, target labels, staged data, and cache outages."""
from pathlib import Path
import json
import http.client
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import publication as p
import compare_cache_bytes as compare
import build_publication as builder

SHA = 'a' * 40
ART = 'b' * 16 + '.ltar'
MAP = ('"2026-03-17"\n' + json.dumps(['c' * 16, ART]) + '\n').encode()


def fixture(root):
    stage = root / 'cache'; stage.mkdir(parents=True)
    (stage / 'outputs.jsonl').write_bytes(MAP)
    (stage / ART).write_bytes(b'opaque archive bytes, never imported')
    modules = [{'name': 'SphereCeti', 'path': 'SphereCeti.lean', 'kind': 'library'},
               {'name': 'SphereCetiRoadmap', 'path': 'SphereCetiRoadmap.lean', 'kind': 'roadmap'}]
    report = {'verdict': {'passed': True}, 'compiled': {
        'modules': [{'name': m['name']} for m in modules],
        'declarations': [
            {'name': 'safe', 'moduleName': 'SphereCeti', 'axioms': ['propext']},
            {'name': 'glue', 'moduleName': 'SphereCeti', 'axioms': ['sorryAx']},
            {'name': 'target<"&>', 'moduleName': 'SphereCetiRoadmap', 'axioms': []}]}}
    p.render_docs(root / 'docs', SHA, report, modules, {'packages': []})
    seal(root)
    return report, modules


def seal(root):
    files = {x.relative_to(root).as_posix(): p.digest(x.read_bytes())
             for folder in ('cache', 'docs') for x in (root / folder).rglob('*') if x.is_file()}
    (root / 'publication.json').write_bytes(p.json_bytes({
        'schema_version': 1, 'repository': p.REPOSITORY, 'source_revision': SHA,
        'toolchain': p.TOOLCHAIN, 'platform': p.PLATFORM, 'files': files}))


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name) / 'bundle'
        self.report, self.modules = fixture(self.root)

    def tearDown(self):
        self.temp.cleanup()

    def test_compiled_evidence_distinguishes_targets_and_admission_glue(self):
        p.verify_bundle(self.root, SHA)
        evidence = json.loads((self.root / 'docs/declarations.json').read_text())
        by_name = {d['name']: d for d in evidence['declarations']}
        self.assertEqual(by_name['safe']['status'], 'audited-library-declaration')
        self.assertEqual(by_name['glue']['status'], 'admission-dependent')
        self.assertEqual(by_name['target<"&>']['status'], 'roadmap-target')
        self.assertIs(evidence['production_evidence'], False)
        for row in evidence['declarations']:
            page, anchor = row['url'].split('#')
            self.assertIn('id="' + anchor + '"', (self.root / 'docs' / page).read_text())
            self.assertIn('/blob/' + SHA + '/', row['source_url'])
        targets = (self.root / 'docs/targets/index.html').read_text()
        self.assertIn('target&lt;&quot;&amp;&gt;', targets)
        self.assertIn('not proved milestones', targets)

    def test_failed_foreign_and_incomplete_audits_cannot_render(self):
        for mutation in ('failed', 'foreign', 'missing'):
            report = json.loads(json.dumps(self.report))
            if mutation == 'failed': report['verdict']['passed'] = False
            if mutation == 'foreign': report['compiled']['declarations'][0]['moduleName'] = 'Mathlib'
            if mutation == 'missing': report['compiled']['modules'].pop()
            with self.subTest(mutation=mutation), self.assertRaises(p.PublicationError):
                p.render_docs(Path(self.temp.name) / mutation, SHA, report, self.modules, {})

    def test_source_marker_rejects_noncanonical_bytes_and_symlinks(self):
        path = self.root / 'docs/SOURCE_SHA'
        for data in [(SHA + '\r\n').encode(), SHA.encode(), (SHA + '\0\n').encode(), ('A' * 40 + '\n').encode()]:
            path.write_bytes(data)
            with self.assertRaises((p.PublicationError, UnicodeError)):
                p.marker(path)
        path.unlink(); path.symlink_to(self.root / 'publication.json')
        with self.assertRaises(p.PublicationError): p.marker(path)

    def test_bundle_rejects_altered_identity_and_payload(self):
        with self.assertRaises(p.PublicationError): p.verify_bundle(self.root, 'd' * 40)
        (self.root / 'docs/index.html').write_text('tampered')
        with self.assertRaises(p.PublicationError): p.verify_bundle(self.root, SHA)

    def test_resealed_forged_cursor_is_rejected(self):
        (self.root / 'docs/SOURCE_SHA').write_text('d' * 40 + '\n'); seal(self.root)
        with self.assertRaises(p.PublicationError): p.verify_bundle(self.root, SHA)

    def test_staging_rejects_traversal_missing_extra_nested_and_links(self):
        stage = self.root / 'cache'
        for output in ('../secret', '/etc/passwd', 'x.ltar', {'file': ART}, [ART]):
            (stage / 'outputs.jsonl').write_text('"2026-03-17"\n' + json.dumps(['c' * 16, output]) + '\n')
            with self.subTest(output=output), self.assertRaises(p.PublicationError): p.validate_staging(stage)
        (stage / 'outputs.jsonl').write_bytes(MAP)
        extra = stage / 'extra'; extra.mkdir()
        with self.assertRaises(p.PublicationError): p.validate_staging(stage)
        extra.rmdir()
        (stage / ART).unlink()
        with self.assertRaises(p.PublicationError): p.validate_staging(stage)
        (stage / ART).symlink_to(self.root / 'docs/index.html')
        with self.assertRaises(p.PublicationError): p.validate_staging(stage)

    def test_map_rejects_empty_duplicate_and_unknown_format(self):
        for data in (b'', b'"2026-03-17"\n', b'"future"\n' + MAP.split(b'\n', 1)[1], MAP + MAP.split(b'\n', 1)[1]):
            with self.subTest(data=data), self.assertRaises((p.PublicationError, ValueError)):
                p.read_map(data)

    def test_endpoint_and_platform_namespace(self):
        url = p.map_url('https://cache.example/revisions', SHA)
        self.assertIn('/thefundamentaltheor3m/SphereCeti/pt/x86_64-unknown-linux-gnu/tc/leanprover--lean4---v4.34.0-rc1/', url)
        for endpoint in ('http://cache.example', 'https://user:pass@cache.example', 'https://cache.example/?q=x',
                         'https://cache.example/a/../b', 'https://cache.example/%2e%2e',
                         'https://cache.taucetiproject.org/artifacts', 'https://cache.example/\nsecret'):
            with self.subTest(endpoint=endpoint), self.assertRaises(p.PublicationError): p.endpoint(endpoint)

    def test_cache_outages_are_inconclusive_without_source_fallback_agreement(self):
        calls = []
        def unavailable(url, limit):
            calls.append(url); raise OSError('offline')
        self.assertEqual(compare.compare(self.root / 'cache', SHA, '', '', unavailable)['status'], 'inconclusive')
        self.assertFalse(calls)
        self.assertEqual(compare.compare(self.root / 'cache', SHA, 'https://cache.example/a', 'https://cache.example/r', unavailable)['status'], 'inconclusive')
        self.assertEqual(len(calls), 1)
        def truncated(url, limit): raise http.client.IncompleteRead(b'partial', 100)
        self.assertEqual(compare.compare(self.root / 'cache', SHA, 'https://cache.example/a',
                                         'https://cache.example/r', truncated)['status'], 'inconclusive')

    def test_comparison_uses_downloaded_bytes_without_executing_them(self):
        def reader(url, limit):
            return MAP if url.endswith('.jsonl') else (self.root / 'cache' / ART).read_bytes()
        args = (self.root / 'cache', SHA, 'https://cache.example/a', 'https://cache.example/r')
        self.assertEqual(compare.compare(*args, reader)['status'], 'agreement')
        def different(url, limit): return MAP if url.endswith('.jsonl') else b'different'
        self.assertEqual(compare.compare(*args, different)['status'], 'divergent')
        def corrupt(url, limit): return b'not a mapping'
        self.assertEqual(compare.compare(*args, corrupt)['status'], 'inconclusive')

    def test_source_mode_refuses_preexisting_project_outputs(self):
        root = Path(self.temp.name) / 'checkout'; (root / '.lake/build').mkdir(parents=True)
        (root / '.lake/build/stale.olean').write_bytes(b'cached')
        with patch.object(builder, 'ROOT', root), patch.object(builder, 'clean_revision', return_value=SHA):
            with self.assertRaisesRegex(p.PublicationError, 'empty project'):
                builder.build(Path(self.temp.name) / 'out', source=True)

    def test_pinned_lake_upload_runs_outside_project_with_fake_transport(self):
        prefix = subprocess.check_output(['lean', '--print-prefix'], cwd=ROOT, text=True).strip()
        scratch = Path(self.temp.name) / 'transport'; scratch.mkdir()
        binary = scratch / 'bin'; binary.mkdir()
        log = scratch / 'requests.jsonl'
        curl = binary / 'curl'
        curl.write_text('#!' + sys.executable + '\n' + '''
import json, os, pathlib, sys
args = sys.argv[1:]
config = pathlib.Path(args[args.index('--config') + 1]).read_text() if '--config' in args else ''
with open(os.environ['TRANSPORT_LOG'], 'a') as f:
    f.write(json.dumps({'args': args, 'config': config}) + '\\n')
print(json.dumps({'http_code': 200, 'response_code': 200, 'urlnum': 0}), file=sys.stderr)
''')
        curl.chmod(0o755)
        env = {'HOME': str(scratch), 'PATH': str(binary) + ':/usr/bin:/bin',
               'TRANSPORT_LOG': str(log), 'LAKE_CACHE_DIR': str(scratch / 'cache'),
               'LAKE_CACHE_KEY': 'fake-id:fake-secret',
               'LAKE_CACHE_ARTIFACT_ENDPOINT': 'https://cache.example/artifacts',
               'LAKE_CACHE_REVISION_ENDPOINT': 'https://cache.example/revisions'}
        result = subprocess.run([prefix + '/bin/lake', 'cache', 'put-staged', str(self.root / 'cache'),
                                 '--repo', p.REPOSITORY, '--rev', SHA, '--toolchain', p.TOOLCHAIN,
                                 '--platform', p.PLATFORM], cwd=scratch, env=env,
                                capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        requests = log.read_text()
        self.assertIn(p.map_url('https://cache.example/revisions', SHA), requests)
        self.assertIn(ART, requests)
        self.assertFalse((scratch / 'lakefile.toml').exists())

    def test_producer_selects_only_library_targets_and_binds_revision(self):
        root = Path(self.temp.name) / 'checkout'; (root / '.lake').mkdir(parents=True)
        (root / 'lakefile.toml').write_text('name="SphereCeti"\n')
        (root / 'lake-manifest.json').write_text('{"packages": []}')
        commands = []
        output = Path(self.temp.name) / 'built'
        def run(command):
            commands.append(command)
            if command[:3] == ['lake', 'cache', 'stage']:
                import shutil
                shutil.copytree(self.root / 'cache', output / 'cache')
            return ''
        def audit(*args): (root / '.lake/publication-audit.json').write_text(json.dumps(self.report))
        with patch.object(builder, 'ROOT', root), patch.object(builder, 'clean_revision', return_value=SHA), \
             patch.object(builder, 'run', side_effect=run), patch.object(builder, 'audit', side_effect=audit), \
             patch.object(builder, 'check', return_value={'modules': self.modules}), patch.dict(builder.os.environ, {}, clear=True):
            builder.build(output, source=True)
            self.assertEqual(builder.os.environ['LAKE_RESTORE_ARTIFACTS'], 'false')
            self.assertEqual(builder.os.environ['LAKE_NO_CACHE'], 'true')
        selected = next(c for c in commands if c[:2] == ['lake', 'build'])
        self.assertEqual([a for a in selected if a.startswith('+')], ['+SphereCeti:olean'])
        self.assertIn('--no-build', selected)
        p.verify_bundle(output, SHA)


if __name__ == '__main__': unittest.main()
