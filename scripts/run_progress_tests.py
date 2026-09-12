#!/usr/bin/env python3
"""Run the pinned Progress scripts unchanged, with only disposable local Git subprocesses.

Each script gets a fresh source tree, Git repository, home, and credential-free environment.
The audit hook catches accidental external calls in cooperative tests; it is not a hostile-code
sandbox. Git transport, hooks, signing, inherited config, and external diff drivers are disabled.
"""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ROOT / 'tools/progress'

CHILD = r'''
import os
from pathlib import Path
import runpy
import sys

scratch = Path(sys.argv[2]).resolve()
sys.path.insert(0, str(scratch / 'source'))
blocked = []
class ForbiddenCall(BaseException):
    pass

def inside(value):
    return Path(os.fsdecode(value)).resolve().is_relative_to(scratch)

def deny(event):
    blocked.append(event)
    raise ForbiddenCall('offline Progress tests forbid ' + event)

def guard(event, args):
    # Upstream's canned Docs transport uses /nonexistent as an unwritable cache sentinel.
    # Preserve that failure even when the test runner is root; never create or read that path.
    if event in ('open', 'os.mkdir') and isinstance(args[0], (str, bytes)):
        path = os.fsdecode(args[0])
        if path == '/nonexistent' or path.startswith('/nonexistent/'):
            raise PermissionError('upstream unwritable-cache fixture')
    if event == 'subprocess.Popen':
        executable, argv, cwd, env = args
        if executable != 'git' or not isinstance(argv, (list, tuple)) or not inside(cwd or os.getcwd()):
            deny(event)
        rest = list(argv[1:])
        if rest[:1] == ['-C']:
            if len(rest) < 3 or not inside(rest[1]):
                deny('Git source outside fixture')
            rest = rest[2:]
        allowed = {'init','add','commit','rev-parse','log','merge-base','cat-file','show',
                   'blame','ls-files','update-ref','checkout','diff','rev-list'}
        if not rest or rest[0] not in allowed:
            deny('non-fixture Git command')
        if any(arg.startswith('/') and not inside(arg) for arg in rest):
            deny('Git path outside fixture')
        if rest[0] == 'init' and len(rest) > 1 and not rest[-1].startswith('-'):
            if rest[-2] != '-b' and not inside(rest[-1]):
                deny('Git init outside fixture')
    elif event.startswith(('socket.', 'os.exec', 'os.spawn', 'os.posix_spawn')) or event in (
        'os.system', 'os.fork', 'os.forkpty', 'pty.spawn',
    ):
        deny(event)
    elif event == 'open':
        path, mode, flags = args
        if not isinstance(path, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT):
            if os.fsdecode(path) != os.devnull and not inside(path):
                deny('write outside fixture')
    elif event in ('os.remove', 'os.rmdir', 'os.mkdir', 'os.rename'):
        paths = args[:2] if event == 'os.rename' else args[:1]
        if any(not inside(path) for path in paths):
            deny('mutation outside fixture')

sys.addaudithook(guard)
try:
    runpy.run_path(sys.argv[1], run_name='__main__')
finally:
    if blocked:
        raise SystemExit('forbidden operation attempted: ' + ', '.join(blocked))
'''


def run_script(path: Path, *, upstream=False):
    with tempfile.TemporaryDirectory(prefix='sphereceti-progress-test-') as temp:
        scratch = Path(temp)
        staged = scratch / 'source'
        for name in ('progress', 'tests'):
            shutil.copytree(SOURCES / name, staged / name, ignore=shutil.ignore_patterns('__pycache__'))
        (staged / '.github/scripts').mkdir(parents=True)
        shutil.copy2(SOURCES / 'fixtures/collect.py', staged / '.github/scripts/collect.py')
        binary = scratch / 'bin'
        binary.mkdir()
        git = shutil.which('git')
        if not git:
            raise RuntimeError('Git is required for disposable source-window fixtures')
        (binary / 'git').symlink_to(Path(git).resolve())
        env = {'HOME': temp, 'TMPDIR': temp, 'PATH': str(binary), 'LANG': 'C.UTF-8',
               'TAUCETI_DOCS_CACHE': str(scratch / 'docs-cache'), 'GIT_CONFIG_NOSYSTEM': '1',
               'GIT_CONFIG_GLOBAL': '/dev/null', 'GIT_ATTR_NOSYSTEM': '1', 'GIT_ALLOW_PROTOCOL': '',
               'GIT_TERMINAL_PROMPT': '0', 'GIT_NO_REPLACE_OBJECTS': '1', 'GIT_CONFIG_COUNT': '5',
               'GIT_CONFIG_KEY_0': 'core.hooksPath', 'GIT_CONFIG_VALUE_0': '/dev/null',
               'GIT_CONFIG_KEY_1': 'commit.gpgSign', 'GIT_CONFIG_VALUE_1': 'false',
               'GIT_CONFIG_KEY_2': 'tag.gpgSign', 'GIT_CONFIG_VALUE_2': 'false',
               'GIT_CONFIG_KEY_3': 'diff.external', 'GIT_CONFIG_VALUE_3': '',
               'GIT_CONFIG_KEY_4': 'core.attributesFile', 'GIT_CONFIG_VALUE_4': '/dev/null'}
        subprocess.run(['git', 'init', '-q', str(staged)], env=env, check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
        if upstream:
            path = staged / 'tests' / path.name
        return subprocess.run([sys.executable, '-I', '-B', '-c', CHILD, str(path.resolve()), temp],
                              cwd=staged, env=env, text=True, capture_output=True, timeout=120)


def main():
    scripts = sorted((SOURCES / 'tests').glob('test_*.py'))
    if len(scripts) != 11:
        raise SystemExit('expected all 11 pinned upstream test scripts')
    assertions = 0
    for path in scripts:
        result = run_script(path, upstream=True)
        if result.returncode:
            print(result.stdout)
            print(result.stderr, file=sys.stderr)
            raise SystemExit(f'failed: {path.name} ({result.returncode})')
        assertions += sum(line.startswith('ok ') for line in result.stdout.splitlines())
        print('passed:', path.name, flush=True)
    print(f'{len(scripts)} upstream scripts passed ({assertions} checks); external calls forbidden')


if __name__ == '__main__':
    main()
