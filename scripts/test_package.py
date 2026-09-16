#!/usr/bin/env python3
"""Smoke-test wheel and source installs outside the repository with hostile cwd config."""

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
            assert all(not capability['enabled'] for capability in report['capabilities'].values())
            assert report['local_review']['implemented']
            review_root = scratch / 'review-fixture'
            review_root.mkdir()
            installed_smoke(environment / 'bin' / 'sphereceti', review_root)
            posting_root = scratch / 'posting-fixture'
            posting_root.mkdir()
            installed_post_smoke(environment / 'bin' / 'sphereceti', posting_root)
            print(f'Fresh installation outside checkout: {artifact.name}: OK')


if __name__ == '__main__':
    main()
