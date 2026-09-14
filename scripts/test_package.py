#!/usr/bin/env python3
"""Smoke-test wheel and source installs outside the repository with hostile cwd config."""

from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import tempfile
import venv
from package_contract import assert_installation
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tests'))
from review_fixture import installed_smoke
from review_post_fixture import installed_post_smoke
from archive_fixture import installed_archive_smoke
from evaluation_fixture import installed_evaluation_smoke


ROOT = Path(__file__).resolve().parents[1]


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
            docs_source = next(s for s in report['sources'] if s['name'] == 'docs-cache-operations')
            assert docs_source['repository'] == 'TauCetiProject/TauCeti'
            assert docs_source['commit'] == 'b743b607ce3e9742b18026ad79082e5d15badff5'
            assert all(not capability['enabled'] for capability in report['capabilities'].values())
            assert report['local_review']['implemented']
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
            print(f'Fresh installation outside checkout: {artifact.name}: OK')


if __name__ == '__main__':
    main()
