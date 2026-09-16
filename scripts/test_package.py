#!/usr/bin/env python3
"""Smoke-test wheel and source installs outside the repository with hostile cwd config."""

from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import venv
from package_contract import assert_installation

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tests'))
from review_fixture import installed_smoke
from review_post_fixture import installed_post_smoke
from archive_fixture import installed_archive_smoke
from evaluation_fixture import installed_evaluation_smoke
from merge_fixture import installed_merge_smoke
from controller_fixture import installed_controller_smoke
from lifecycle_fixture import installed_lifecycle_smoke


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests'))
from progress_fixture import PROSE, fixture as progress_fixture


PROGRESS_INTEGRITY = r"""
import hashlib, importlib.util, json
from importlib.metadata import metadata
from sphereceti.progress_sources import MANIFEST_SHA256, source_root, sources
assert not metadata('sphereceti').get_all('Requires-Dist')
assert importlib.util.find_spec('progress') is None
assert importlib.util.find_spec('sphereceti_progress_sources') is None
root = source_root()
raw = root.joinpath('import-manifest.json').read_bytes()
assert hashlib.sha256(raw).hexdigest() == MANIFEST_SHA256
manifest = json.loads(raw)
assert manifest['commit'] == '880e8b9737973bfbd8f1f214f4ac2ded67f5b856'
assert len(manifest['files']) == 32
for row in manifest['files']:
    assert hashlib.sha256(root.joinpath(row['destination']).read_bytes()).hexdigest() == row['import_sha256']
assert sources()['files'].STATUS_MARKER == 'tauceti-status:v1'
"""


def main():
    wheels = list((ROOT / 'dist').glob('*.whl'))
    sdists = list((ROOT / 'dist').glob('*.tar.gz'))
    if len(wheels) != 1 or len(sdists) != 1:
        raise SystemExit('Build exactly one wheel and one source distribution before testing.')
    for artifact in (wheels[0], sdists[0]):
        with tempfile.TemporaryDirectory(prefix='sphereceti-install-') as directory:
            scratch = Path(directory)
            environment = scratch / 'environment'
            venv.EnvBuilder(with_pip=True).create(environment)
            python = environment / 'bin' / 'python'
            subprocess.run([str(python), '-m', 'pip', 'install', '--disable-pip-version-check',
                            '--no-cache-dir', '--no-deps', str(artifact)], check=True)
            foreign = scratch / 'foreign'
            foreign.mkdir()
            (foreign / 'sphereceti.toml').write_text('repository = "attacker/checkout"\n')
            (foreign / 'policy').mkdir()
            (foreign / 'policy' / 'automation.toml').write_text('merging = true\n')
            (foreign / 'policy' / 'reporting.toml').write_text('docs_url = "https://attacker.invalid"\n')
            env = os.environ.copy()
            env.pop('PYTHONPATH', None)
            result = subprocess.run([str(environment / 'bin' / 'sphereceti'), 'status', '--json', '--offline'],
                                    cwd=foreign, env=env, text=True, capture_output=True, check=True)
            report = json.loads(result.stdout)
            assert report['project']['repository'] == 'thefundamentaltheor3m/SphereCeti'
            assert report['project']['implementation_repository'] == 'thefundamentaltheor3m/Sphere-Packing-Lean'
            assert report['roadmap']['state'] == 'not_installed'
            assert not any(report['policy'].values())
            assert report['queue']['state'] == 'not_checked'
            assert_installation(ROOT, python, foreign, env, report)
            assert report['progress']['local_drafts'] is True
            assert report['progress']['publishing'] is False
            subprocess.run([str(python), '-I', '-c', PROGRESS_INTEGRITY],
                           cwd=foreign, env=env, check=True)
            docs_source = next(s for s in report['sources'] if s['name'] == 'docs-cache-operations')
            assert docs_source['repository'] == 'TauCetiProject/TauCeti'
            assert docs_source['commit'] == 'b743b607ce3e9742b18026ad79082e5d15badff5'
            assert all(not capability['enabled'] for capability in report['capabilities'].values())
            assert report['local_review']['implemented']
            assert report['merge_observation']['read_only']
            assert report['merge_controller']['implemented'] and not report['merge_controller']['enabled']
            controller_root = scratch / 'controller-fixture'
            controller_root.mkdir()
            installed_controller_smoke(environment / 'bin' / 'sphereceti', controller_root)
            assert not report['maintenance']['labels_enabled']
            lifecycle_root = scratch / 'lifecycle-fixture'
            lifecycle_root.mkdir()
            installed_lifecycle_smoke(environment / 'bin' / 'sphereceti', lifecycle_root)
            merging_root = scratch / 'merge-fixture'
            merging_root.mkdir()
            installed_merge_smoke(environment / 'bin' / 'sphereceti', merging_root)
            review_root = scratch / 'review-fixture'
            review_root.mkdir()
            fixture = installed_smoke(environment / 'bin' / 'sphereceti', review_root)
            installed_archive_smoke(environment / 'bin' / 'sphereceti', fixture)
            installed_evaluation_smoke(environment / 'bin' / 'sphereceti', scratch / 'evaluation-fixture')
            posting_root = scratch / 'posting-fixture'
            posting_root.mkdir()
            installed_post_smoke(environment / 'bin' / 'sphereceti', posting_root)
            survey = foreign / 'survey.json'
            survey.write_text(json.dumps({
                'schema': 'sphereceti.worker-survey/v1', 'repository': report['project']['repository'],
                'actor': 'fixture', 'observed_at': datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
                'scope': None, 'pull_requests': []}))
            worker = subprocess.run([str(environment / 'bin' / 'sphereceti'), 'worker', 'plan',
                                     '--snapshot', str(survey), '--json'], cwd=foreign, env=env,
                                    text=True, capture_output=True, check=True)
            planned = json.loads(worker.stdout)
            assert planned['selected'] is None and not planned['executable']
            assert planned['advisory_only'] and not planned['roadmap']['source_verified']
            subprocess.run([str(python), '-c',
                'from sphereceti.worker import targets; assert targets(["#3,2"]) == (2,3)'],
                cwd=foreign, env=env, check=True)
            disabled = subprocess.run([str(environment / 'bin' / 'sphereceti'), 'worker', 'run',
                                       '--execute', '--pr', '1', '--json'], cwd=foreign, env=env,
                                      text=True, capture_output=True, check=True)
            assert json.loads(disabled.stdout)['state'] == 'disabled'
            loop = subprocess.run([str(environment / 'bin' / 'sphereceti'), 'worker', 'run',
                                   '--loop', '--max-rounds', '2', '--execute', '--json'],
                                  cwd=foreign, env=env, text=True, capture_output=True, check=True)
            assert json.loads(loop.stdout)['state'] == 'disabled'
            assert len(json.loads(loop.stdout)['rounds']) == 1
            # A hostile cwd cannot enable state publication either.
            sync = subprocess.run([str(environment / 'bin' / 'sphereceti'), 'worker', 'sync',
                                   '--receipt', str(survey)], cwd=foreign, env=env,
                                  text=True, capture_output=True)
            assert sync.returncode == 2 and 'disabled' in sync.stderr
            command = str(environment / 'bin' / 'sphereceti')
            missing = subprocess.run([command, 'progress', 'plan', '--json'], cwd=foreign,
                                     env=env, text=True, capture_output=True)
            assert missing.returncode == 1
            assert json.loads(missing.stdout)['state'] == 'missing_evidence'
            data = scratch / 'fixture'; data.mkdir()
            repo, docs, start, end = progress_fixture(data, SimpleNamespace(**report['project']))
            prose = scratch / 'prose.json'
            prose.write_text(json.dumps({'status': PROSE, 'progress': PROSE, 'citations': ['targetEntry']}))
            draft = scratch / 'draft'
            common = ['--repo', str(repo), '--evidence-dir', str(docs), '--json']
            for args, state in (
                (['plan', *common, '--from', start], 'ready'),
                (['prepare', *common, '--from', start, '--prose', str(prose), '--output', str(draft)], 'prepared'),
                (['validate', *common, '--draft', str(draft)], 'valid'),
            ):
                result = subprocess.run([command, 'progress', *args], cwd=foreign, env=env,
                                        text=True, capture_output=True, check=True)
                value = json.loads(result.stdout)
                assert value['state'] == state and value['publication_allowed'] is False

            # Installed profiling resolves exact Git inputs independently of caller config.
            import sys
            sys.path.insert(0, str(ROOT / 'tests'))
            from profiling_fixture import fixture as profiling_fixture
            base, head = profiling_fixture(scratch / 'profile-repo')
            result = subprocess.run([str(environment / 'bin' / 'sphereceti'), 'profile-plan',
                                     '--repo', str(scratch / 'profile-repo'), '--tooling', head,
                                     '--base', base, '--head', head],
                                    cwd=foreign, env=env, text=True, capture_output=True, check=True)
            profile = json.loads(result.stdout)
            assert profile['head'] == head and profile['diff_base'] == base
            assert profile['changes'][0]['path'] == 'SphereCeti/Basic.lean'
            subprocess.run([str(python), '-c',
                            'from pathlib import Path; import sys; '
                            'from sphereceti.profile_runner import verify_tools; '
                            'verify_tools(Path(sys.argv[1]), sys.argv[2])',
                            str(scratch / 'profile-repo'), head], cwd=foreign, env=env, check=True)
            print(f'Fresh installation outside checkout: {artifact.name}: OK')


if __name__ == '__main__':
    main()
