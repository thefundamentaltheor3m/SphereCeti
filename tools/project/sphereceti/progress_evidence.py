"""Validate #13's published compiled declaration reference without importing Lean artifacts."""
from __future__ import annotations
import hashlib
from html.parser import HTMLParser
import http.client
import json
from pathlib import Path
import re
import stat
import urllib.parse
import urllib.request

MAX_FILE = 16 * 1024 * 1024
SHA = re.compile(r'[0-9a-f]{40}\Z')
MODULE = re.compile(r'SphereCeti(?:Roadmap)?(?:\.[A-Za-z_][A-Za-z0-9_\']*)*\Z')


class ProgressError(ValueError):
    pass


def fields(value, keys):
    if not isinstance(value, dict) or set(value) != set(keys):
        raise ProgressError('unexpected reporting evidence fields')


def sha(value):
    if not isinstance(value, str) or not SHA.fullmatch(value):
        raise ProgressError('reporting cursors must be exact Git revisions')
    return value


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encode(value):
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True) + '\n').encode()


def decode(data):
    def pairs(items):
        result = {}
        for k, v in items:
            if k in result: raise ProgressError('duplicate JSON field')
            result[k] = v
        return result
    def constant(value): raise ProgressError('nonfinite JSON number')
    return json.loads(data, object_pairs_hook=pairs, parse_constant=constant)


def read_file(path, limit=MAX_FILE):
    path = Path(path)
    mode = path.lstat()
    if not stat.S_ISREG(mode.st_mode) or mode.st_size > limit:
        raise ProgressError('expected a bounded regular evidence file')
    if any(p.is_symlink() for p in [path, *path.parents]):
        raise ProgressError('symlinked evidence path')
    return path.read_bytes()


def text(value):
    if not isinstance(value, str) or not value or len(value) > 4096 or any(ord(c) < 32 for c in value):
        raise ProgressError('invalid declaration text')
    return value


def endpoint(url):
    p = urllib.parse.urlsplit(url)
    if (p.scheme != 'https' or not p.hostname or p.username is not None or p.password is not None or
            p.query or p.fragment or '%' in p.path or any(c.isspace() for c in url) or
            any(part in ('.', '..') for part in p.path.split('/'))):
        raise ProgressError('approved documentation must have a plain HTTPS URL')
    return url.rstrip('/')


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args):
        raise ProgressError('documentation redirects require a reviewed endpoint update')


def fetch(url):
    try:
        with urllib.request.build_opener(urllib.request.ProxyHandler({}), NoRedirect).open(url, timeout=30) as r:
            data = r.read(MAX_FILE + 1)
    except (OSError, http.client.HTTPException) as error:
        raise ProgressError('published documentation is unavailable or incomplete') from error
    if len(data) > MAX_FILE: raise ProgressError('oversized documentation response')
    return data


class Anchors(HTMLParser):
    def __init__(self):
        super().__init__(); self.ids = set()
    def handle_starttag(self, tag, attrs):
        for k, value in attrs:
            if k == 'id':
                if value in self.ids: raise ProgressError('duplicate documentation anchor')
                self.ids.add(value)


def load_evidence(project, *, directory=None, url='', reader=None):
    if directory is None and not url:
        return None
    if directory is not None:
        root = Path(directory)
        read = lambda name: read_file(root / name)
        mode = 'fixture-preview'
    else:
        base = endpoint(url)
        read = lambda name: (reader or fetch)(base + '/' + name)
        mode = 'published'
    before = read('SOURCE_SHA')
    if len(before) != 41 or before[-1:] != b'\n':
        raise ProgressError('SOURCE_SHA must be one exact revision and newline')
    revision = sha(before[:-1].decode('ascii'))
    names = ['declarations.json', 'audit.json', 'library/index.html', 'targets/index.html']
    payload = {name: read(name) for name in names}
    if read('SOURCE_SHA') != before:
        raise ProgressError('documentation changed during evidence read')
    index, audit = decode(payload['declarations.json']), decode(payload['audit.json'])
    fields(index, {'schema_version', 'repository', 'source_revision', 'toolchain', 'dependencies',
                   'production_repository', 'production_evidence', 'audit_sha256', 'declarations'})
    if (type(index['schema_version']) is not int or index['schema_version'] != 1 or
            index['repository'] != project.repository or index['source_revision'] != revision or
            index['toolchain'] != project.lean or index['production_evidence'] is not False or
            index['production_repository'] != project.implementation_repository or
            index['audit_sha256'] != digest(payload['audit.json'])):
        raise ProgressError('documentation identity, scope, or audit binding mismatch')
    dependencies = index['dependencies']
    if not isinstance(dependencies, dict) or not isinstance(dependencies.get('packages'), list):
        raise ProgressError('missing pinned documentation dependency graph')
    packages = {}
    for pkg in dependencies['packages']:
        if not isinstance(pkg, dict) or pkg.get('type') != 'git' or pkg.get('name') in packages:
            raise ProgressError('invalid documentation dependency')
        packages[text(pkg['name'])] = sha(pkg['rev'])
    if packages.get('TauCeti') != project.tauceti or packages.get('mathlib') != project.mathlib:
        raise ProgressError('documentation dependency pins differ from project policy')
    fields(audit, {'verdict', 'compiled'})
    verdict, compiled = audit['verdict'], audit['compiled']
    fields(verdict, {'passed', 'errors', 'ratchet', 'declaration_counts', 'roadmap_admissions', 'modules'})
    fields(compiled, {'schema_version', 'modules', 'declarations', 'linters', 'findings', 'nolints'})
    if verdict['passed'] is not True or verdict['errors'] != [] or type(compiled['schema_version']) is not int or compiled['schema_version'] != 1:
        raise ProgressError('published audits did not pass')
    for name in ('modules', 'declarations', 'linters', 'findings', 'nolints'):
        if not isinstance(compiled[name], list): raise ProgressError('invalid compiled report collection')
    if not isinstance(index['declarations'], list) or not isinstance(verdict['declaration_counts'], dict):
        raise ProgressError('invalid declaration index or counts')
    if not isinstance(verdict['ratchet'], list) or type(verdict['roadmap_admissions']) is not int:
        raise ProgressError('invalid audit verdict')
    modules = {}
    for m in compiled['modules']:
        fields(m, {'name', 'isModule', 'imports'})
        if not isinstance(m['name'], str) or not MODULE.fullmatch(m['name']) or m['name'] in modules or m['isModule'] is not True:
            raise ProgressError('invalid compiled module ownership')
        if not isinstance(m['imports'], list): raise ProgressError('invalid imports')
        modules[m['name']] = 0
    pages = {}
    for name in ('library', 'targets'):
        parser = Anchors(); parser.feed(payload[name + '/index.html'].decode('utf-8'))
        pages[name] = parser.ids
    declarations = {}
    for d in compiled['declarations']:
        fields(d, {'moduleName', 'name', 'axioms'})
        name, owner = text(d['name']), text(d['moduleName'])
        if name in declarations or owner not in modules or not isinstance(d['axioms'], list):
            raise ProgressError('duplicate or foreign compiled declaration')
        if d['axioms'] != sorted(set(map(text, d['axioms']))): raise ProgressError('invalid axiom set')
        declarations[name] = d; modules[owner] += 1
    if (verdict['declaration_counts'] != modules or type(verdict['modules']) is not int or
            verdict['modules'] != len(modules) or any(type(n) is not int for n in verdict['declaration_counts'].values())):
        raise ProgressError('incomplete compiled declaration coverage')
    rows = []
    for row in index['declarations']:
        fields(row, {'moduleName', 'name', 'axioms', 'kind', 'status', 'url', 'source_url'})
        original = declarations.pop(row['name'], None)
        if original != {k: row[k] for k in ('moduleName', 'name', 'axioms')}:
            raise ProgressError('declaration index differs from compiled audit')
        target = row['moduleName'] == 'SphereCetiRoadmap' or row['moduleName'].startswith('SphereCetiRoadmap.')
        section = 'targets' if target else 'library'
        kind = 'roadmap' if target else 'library'
        status = 'roadmap-target' if target else 'admission-dependent' if 'sorryAx' in row['axioms'] else 'audited-library-declaration'
        anchor = 'd-' + digest(row['name'].encode())
        source_url = f'https://github.com/{project.repository}/blob/{revision}/{row["moduleName"].replace(".", "/")}.lean'
        if (row['kind'] != kind or row['status'] != status or row['url'] != f'{section}/index.html#{anchor}' or
                row['source_url'] != source_url or anchor not in pages[section]):
            raise ProgressError('invalid declaration classification or documentation link')
        rows.append({**row, 'achievement': False, 'attribution': 'context-in-changed-module'})
    if declarations: raise ProgressError('declaration index omitted compiled declarations')
    return {'mode': mode, 'source_revision': revision, 'docs_url': endpoint(url) if mode == 'published' else '',
            'digest': digest(encode({name: digest(data) for name, data in {'SOURCE_SHA': before, **payload}.items()})),
            'declarations': sorted(rows, key=lambda d: d['name'])}
