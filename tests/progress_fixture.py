"""Synthetic compiled data and disposable Git history; never production proof evidence."""
from pathlib import Path
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from publication import render_docs

PROSE = ('The documented window records changes to the package interfaces and roadmap targets. '
         'The compiled declaration inventory supplies context for reviewing those changes. '
         'These entries describe the roadmap package and do not establish completed production proofs. ')


def git(root, *args):
    env = {**os.environ, 'GIT_CONFIG_NOSYSTEM': '1', 'GIT_CONFIG_GLOBAL': '/dev/null',
           'GIT_AUTHOR_DATE': '2000-01-01T12:00:00+00:00', 'GIT_COMMITTER_DATE': '2000-01-01T12:00:00+00:00'}
    return subprocess.check_output(['git', '-C', str(root), '-c', 'core.hooksPath=/dev/null',
                                    '-c', 'commit.gpgSign=false', *args], env=env, stderr=subprocess.PIPE).decode().strip()


def commit(root, message):
    git(root, 'add', '.'); git(root, 'commit', '-qm', message)
    return git(root, 'rev-parse', 'HEAD')


def fixture(directory, project):
    repo = directory / 'repo'; repo.mkdir()
    git(repo, 'init', '-q', '-b', 'main')
    git(repo, 'config', 'user.name', 'Fixture'); git(repo, 'config', 'user.email', 'fixture@example.invalid')
    (repo / 'README.md').write_text('Human-owned roadmap remains unchanged.\n')
    start = commit(repo, 'initial')
    for path in ('SphereCeti/Basic.lean', 'SphereCetiRoadmap/Suggested.lean'):
        p = repo / path; p.parent.mkdir(parents=True, exist_ok=True); p.write_text('-- synthetic changed-module fixture\n')
    end = commit(repo, 'package targets (#21)')
    docs = directory / 'docs'
    make_docs(docs, end, project)
    return repo, docs, start, end


def make_docs(docs, end, project):
    modules = [{'name': 'SphereCeti.Basic', 'path': 'SphereCeti/Basic.lean', 'kind': 'library'},
               {'name': 'SphereCetiRoadmap.Suggested', 'path': 'SphereCetiRoadmap/Suggested.lean', 'kind': 'roadmap'}]
    declarations = [
        {'name': 'libraryEntry', 'moduleName': 'SphereCeti.Basic', 'axioms': ['propext']},
        {'name': 'admittedGlue', 'moduleName': 'SphereCeti.Basic', 'axioms': ['sorryAx']},
        {'name': 'targetEntry', 'moduleName': 'SphereCetiRoadmap.Suggested', 'axioms': []}]
    report = {'verdict': {'passed': True, 'errors': [], 'ratchet': [],
                          'declaration_counts': {'SphereCeti.Basic': 2, 'SphereCetiRoadmap.Suggested': 1},
                          'roadmap_admissions': 0, 'modules': 2},
              'compiled': {'schema_version': 1, 'modules': [{'name': m['name'], 'isModule': True, 'imports': ['Init']} for m in modules],
                           'declarations': declarations, 'linters': [], 'findings': [], 'nolints': []}}
    dependencies = {'packages': [{'name': 'TauCeti', 'type': 'git', 'rev': project.tauceti},
                                 {'name': 'mathlib', 'type': 'git', 'rev': project.mathlib}]}
    render_docs(docs, end, report, modules, dependencies)
