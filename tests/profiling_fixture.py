"""Small Git fixture shared by installed-package and hosted profiler tests."""
import json
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def commit(repo: Path) -> str:
    subprocess.run(['git', '-C', str(repo), 'add', '.'], check=True, capture_output=True)
    subprocess.run(['git', '-C', str(repo), '-c', 'user.name=Fixture', '-c',
                    'user.email=fixture@example.invalid', 'commit', '-qm', 'fixture'], check=True)
    return subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()


def fixture(repo: Path) -> tuple[str, str]:
    repo.mkdir()
    subprocess.run(['git', 'init', '-q', str(repo)], check=True)
    shutil.copytree(ROOT / 'tools/project/sphereceti', repo / 'tools/project/sphereceti',
                    ignore=shutil.ignore_patterns('__pycache__', 'resources'))
    shutil.copytree(ROOT / 'tools/ci', repo / 'tools/ci')
    for file in ('sphereceti.toml', 'lean-toolchain'):
        shutil.copyfile(ROOT / file, repo / file)
    (repo / 'lakefile.toml').write_text('name = "profile_fixture"\nversion = "0.0.0"\n[[lean_lib]]\nname = "SphereCeti"\n[[lean_lib]]\nname = "SphereCetiRoadmap"\n')
    (repo / 'lake-manifest.json').write_text(json.dumps({'version': '1.2.0', 'name': 'profile_fixture',
                                'packagesDir': '.lake/packages', 'lakeDir': '.lake', 'packages': []}))
    (repo / 'SphereCeti').mkdir()
    (repo / 'SphereCeti/Basic.lean').write_text('def fixtureValue : Nat := 1\n')
    (repo / 'SphereCeti.lean').write_text('import SphereCeti.Basic\n')
    (repo / 'SphereCetiRoadmap.lean').write_text('-- fixture roadmap\n')
    base = commit(repo)
    (repo / 'SphereCeti/Basic.lean').write_text('def fixtureValue : Nat := 2\n')
    return base, commit(repo)
