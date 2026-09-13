"""Compare installed payloads with the reviewed checkout inventories, by name and digest."""
import hashlib
import json
from pathlib import Path
import subprocess
import tomllib


def assert_installation(root, python, foreign, env, report):
    """Verify actual installed resources and source entries; never infer success from counts."""
    components = tomllib.loads((root / 'tools/upstream-lock.toml').read_text())['components']
    expected_sources = {row['name']: row for row in components}
    actual_sources = {row['name']: row for row in report['sources']}
    assert len(expected_sources) == len(components), 'duplicate source inventory entry'
    assert len(actual_sources) == len(report['sources']), 'duplicate installed source entry'
    assert actual_sources == expected_sources, 'installed source entries differ from checkout ledger'
    mapping = tomllib.loads((root / 'pyproject.toml').read_text())['tool']['hatch']['build']['targets']['wheel']['force-include']
    expected = {}
    for source, destination in mapping.items():
        assert destination.startswith('sphereceti/resources/'), destination
        source = root / source
        assert source.exists() and not source.is_symlink(), source
        paths = sorted(source.rglob('*')) if source.is_dir() else [source]
        for path in paths:
            if '__pycache__' in path.parts:
                continue
            assert not path.is_symlink(), path
            if not path.is_file():
                continue
            name = destination + ('/' + path.relative_to(source).as_posix() if source.is_dir() else '')
            assert name not in expected, name
            expected[name] = hashlib.sha256(path.read_bytes()).hexdigest()
    code = '''
import hashlib,json
from importlib.resources import files
root=files('sphereceti').joinpath('resources')
result={}
def walk(path,prefix):
    for child in path.iterdir():
        if child.name=='__pycache__': continue
        name=prefix+'/'+child.name
        if child.is_dir(): walk(child,name)
        else: result[name]=hashlib.sha256(child.read_bytes()).hexdigest()
walk(root,'sphereceti/resources')
print(json.dumps(result))
'''
    actual = json.loads(subprocess.check_output([str(python), '-I', '-c', code],
                                                cwd=foreign, env=env, text=True, timeout=30))
    assert actual == expected, ('installed resource inventory differs',
                               sorted(set(expected)-set(actual)), sorted(set(actual)-set(expected)),
                               sorted(k for k in expected.keys() & actual.keys() if expected[k] != actual[k]))
