"""Load the exact #12 source bundle in a private namespace; keep upstream files unchanged."""
from functools import lru_cache
from importlib.resources import files
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys
import types

MANIFEST_SHA256 = '8238bddc9ee1c4878646b0076b25edb9b38f1673429e736fa19bf97eec3e2658'
UPSTREAM = '880e8b9737973bfbd8f1f214f4ac2ded67f5b856'

def source_root():
    """Use installed resources or this module's own source tree, never the caller's cwd."""
    root = files('sphereceti').joinpath('resources', 'progress')
    if root.joinpath('import-manifest.json').is_file():
        return root
    return Path(__file__).resolve().parents[3] / 'tools/progress'



def git_run(args, **kwargs):
    """Read-only Git for upstream window logic, without inherited credentials or external helpers."""
    if (not isinstance(args, list) or len(args) < 4 or args[:2] != ['git', '-C'] or
            args[3] not in ('log', 'rev-parse', 'merge-base', 'cat-file', 'diff', 'ls-tree')):
        raise ValueError('unsupported reporting Git operation')
    executable = shutil.which('git')
    if not executable:
        raise ValueError('Git is required for reporting windows')
    env = {'PATH': os.defpath, 'LANG': 'C.UTF-8', 'GIT_CONFIG_NOSYSTEM': '1',
           'GIT_CONFIG_GLOBAL': '/dev/null', 'GIT_NO_REPLACE_OBJECTS': '1',
           'GIT_TERMINAL_PROMPT': '0', 'GIT_ALLOW_PROTOCOL': '', 'GIT_NO_LAZY_FETCH': '1'}
    command = [executable, '-c', 'core.fsmonitor=false', '-c', 'log.showSignature=false',
               '-c', 'core.hooksPath=/dev/null', '-c', 'core.pager=cat', '-c', 'diff.external=', *args[1:]]
    return subprocess.run(command, env=env, timeout=30, **kwargs)


@lru_cache(maxsize=1)
def sources():
    root = source_root()
    manifest_bytes = root.joinpath('import-manifest.json').read_bytes()
    if hashlib.sha256(manifest_bytes).hexdigest() != MANIFEST_SHA256:
        raise ValueError('Progress source bundle manifest differs from reviewed #12')
    manifest = json.loads(manifest_bytes)
    payloads = {}
    for item in manifest['files']:
        data = root.joinpath(item['destination']).read_bytes()
        if hashlib.sha256(data).hexdigest() != item['import_sha256']:
            raise ValueError('Progress source bundle resource digest mismatch')
        payloads[item['destination']] = data
    modules = {}
    for name in ('files', 'window'):
        module_name = 'sphereceti._upstream_progress_' + name
        module = types.ModuleType(module_name)
        module.__file__ = f'<TauCetiProgress@{UPSTREAM}/progress/{name}.py>'
        sys.modules[module_name] = module
        exec(compile(payloads[f'progress/{name}.py'], module.__file__, 'exec'), module.__dict__)
        modules[name] = module
    # Upstream algorithms unchanged; replace only their process transport with read-only Git.
    modules['window'].subprocess = types.SimpleNamespace(run=git_run)
    modules['prompts'] = {name: payloads[f'progress/prompts/{name}.md'].decode()
                          for name in ('status', 'progress')}
    return modules
