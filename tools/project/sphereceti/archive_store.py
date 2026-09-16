"""Immutable local review archive, adapted from TauCetiReview's producer/outbox design.

TauCetiProject/TauCetiReview@afb424eda89e8ac96d9eb69f6a88972055a4cd1b:
runner/archive.py, runner/review.py, runner/post.py; Apache-2.0, upstream contributors.
SphereCeti owns this schema. No TauCetiData schema, tools, or history is imported.
"""
from __future__ import annotations

from contextlib import closing, contextmanager
from datetime import datetime
import fcntl
import gzip
import hashlib
import io
import json
import math
import os
from pathlib import Path
import re
import sqlite3
import stat
import tempfile

from .config import REPOSITORY
from .local_review import RUBRICS
from .review_records import BINDINGS, canonical, parse_json, parse_record, validate_metadata

MAX_FILE = 1024 * 1024
MAX_FILES = 2000
MAX_TOTAL = 64 * MAX_FILE
SCHEMA = 'sphereceti.archive/v1'  # State-branch anchor and legacy records stay unchanged.
RECORD_V2 = 'sphereceti.archive/v2'
HEX = r'[0-9a-f]{64}'
RECORD_PATH = re.compile(r'records/(' + HEX + r')\.json\Z')
BLOB_PATH = re.compile(r'blobs/([0-9a-f]{2})/(' + HEX + r')\.gz\Z')
TOKEN_FIELDS = {'input_tokens', 'output_tokens', 'cached_input_tokens', 'reasoning_output_tokens',
                'cache_read_input_tokens', 'cache_creation_input_tokens', 'total_tokens'}
# Redaction patterns adapted from the pinned runner/archive.py. Opt-in is still required:
# pattern matching cannot guarantee that arbitrary prose contains no private information.
REDACTIONS = (
    (r'\b(?:sk-|ghp_|gho_|github_pat_|xoxb-)[A-Za-z0-9_-]{8,}', '[REDACTED]'),
    (r'\b[A-Z][A-Z0-9_]*(?:KEY|TOKEN|SECRET|PASSWORD)\s*=\s*\S+', '[REDACTED]'),
    (r'(/(?:home|Users)/)[^/\s]+', r'\1[user]'),
)


class ArchiveError(ValueError):
    pass


def require(ok, reason):
    if not ok:
        raise ArchiveError(reason)


def encode(value):
    return canonical(value).encode() + b'\n'


def compress(body):
    # GzipFile fixes both mtime and the OS byte across supported Python versions.
    buffer = io.BytesIO()
    with gzip.GzipFile(filename='', fileobj=buffer, mode='wb', mtime=0) as f:
        f.write(body)
    return buffer.getvalue()


def digest(body):
    return hashlib.sha256(body).hexdigest()


def safe_path(path: Path):
    """Private operator-owned trees only; reject symlinks, including in parent paths."""
    path = path.absolute()
    for part in (*reversed(path.parents), path):
        require(not part.is_symlink(), 'archive paths must not contain symlinks')
    return path


def read(path: Path):
    path = safe_path(path)
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, 'rb') as f:
        require(stat.S_ISREG(os.fstat(f.fileno()).st_mode), 'archive input must be an ordinary file')
        data = f.read(MAX_FILE + 1)
    require(len(data) <= MAX_FILE, 'archive file exceeds 1 MiB')
    return data


@contextmanager
def locked(root: Path):
    root = safe_path(root)
    root.mkdir(parents=True, exist_ok=True, mode=0o700)
    fd = os.open(root / '.lock', os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
    try:
        require(stat.S_ISREG(os.fstat(fd).st_mode), 'archive lock must be an ordinary file')
        fcntl.flock(fd, fcntl.LOCK_EX)
        yield
    finally:
        os.close(fd)


def immutable(path: Path, body: bytes):
    path = safe_path(path)
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    if path.exists():
        require(read(path) == body, 'immutable archive path collision')
        return
    fd, name = tempfile.mkstemp(prefix='.pending-', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as f:
            f.write(body)
            f.flush()
            os.fsync(f.fileno())
        try:
            os.link(name, path)
        except FileExistsError:
            require(read(path) == body, 'immutable archive path collision')
        directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        os.unlink(name)


def usage(value):
    if value is None:
        return None  # Unknown usage must not become zero.
    require(isinstance(value, dict), 'invalid usage')
    result = {k: v for k, v in value.items() if k in TOKEN_FIELDS}
    require(all(type(v) is int and 0 <= v <= 2**63-1 for v in result.values()), 'invalid token count')
    return result


def facts(source, allowed):
    result = {k: v for k, v in source.items() if k in allowed and v is not None}
    for key, value in result.items():
        if key == 'usage':
            result[key] = usage(value)
        elif key == 'cost_estimated':
            require(type(value) is bool, 'invalid estimated-cost flag')
        elif key in ('cost_usd', 'duration_s', 'secs'):
            require(type(value) in (int, float) and math.isfinite(value) and 0 <= value <= 1e12,
                    'invalid numeric run fact')
        elif key == 'returncode':
            require(type(value) is int and -255 <= value <= 255, 'invalid exit code')
        else:
            require(isinstance(value, str) and re.fullmatch(r'[A-Za-z0-9_.:/+-]{1,160}', value),
                    'invalid run identifier')
    return result


RUN_FACTS = {'run_id', 'provider', 'model', 'rubric', 'prompt_policy', 'prices_sha',
             'prompt_sha256', 'duration_s', 'usage', 'cost_usd', 'cost_estimated'}
ATTEMPT_FACTS = {'model', 'secs', 'returncode', 'usage', 'cost_usd', 'cost_estimated'}


def project_run(source, review, request=None):
    require(isinstance(source, dict) and source.get('schema') == 'tauceti.run/v1', 'unknown producer schema')
    for a, b in (('repo', 'repository'), ('pr', 'pr'), ('head_sha', 'head'),
                 ('base_ref_oid', 'base'), ('merge_base_sha', 'diff_base')):
        require(source.get(a) == review[b], 'producer record has different source bindings')
    if request is not None:
        require(source.get('auth') == request['auth'], 'producer authentication mode mismatch')
        require(source.get('arm') == ('shadow:' + request['shadow'] if request['shadow'] else 'production'),
                'producer arm mismatch')
        require(source.get('mode') == ('manual' if request['shadow'] else review['execution_mode']),
                'producer execution mode mismatch')
    run = facts(source, RUN_FACTS | ({'started_at'} if request is not None else set()))
    attempts = source.get('attempts', [])
    require(isinstance(attempts, list) and len(attempts) <= 10 and all(isinstance(a, dict) for a in attempts),
            'invalid producer attempts')
    run['attempts'] = [facts(a, ATTEMPT_FACTS) for a in attempts]
    validate_run(run, v2=request is not None)
    return run


def validate_run(run, *, v2=False):
    allowed = RUN_FACTS | ({'started_at'} if v2 else set())
    require(isinstance(run, dict) and set(run) <= allowed | {'attempts'}, 'unknown run fields')
    require({'run_id', 'provider', 'model', 'rubric', 'prompt_policy', 'attempts'} <= set(run), 'missing run facts')
    require(facts(run, allowed) == {k: v for k, v in run.items() if k != 'attempts'}, 'invalid run facts')
    if v2:
        stamp = run.get('started_at')
        require(isinstance(stamp, str) and re.fullmatch(r'\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ', stamp),
                'missing or invalid producer start time')
        datetime.fromisoformat(stamp)
    require(run['rubric'] in RUBRICS,
            'unknown archive rubric')
    require(run['prompt_policy'] in ('fresh', 'reactivation'), 'unknown prompt policy')
    require(isinstance(run['attempts'], list) and len(run['attempts']) <= 10, 'invalid attempts')
    for attempt in run['attempts']:
        require(isinstance(attempt, dict) and facts(attempt, ATTEMPT_FACTS) == attempt, 'unknown attempt facts')


def validate_record(record, repository):
    require(isinstance(record, dict), 'invalid archive record')
    v2 = record.get('schema') == RECORD_V2
    required = {'schema', 'execution_id', 'finished_at', 'review', 'runs', 'text_blob'} | ({'request'} if v2 else set())
    require(set(record) == required, 'unknown archive fields')
    require(record['schema'] in (SCHEMA, RECORD_V2), 'unknown archive schema')
    require(isinstance(record['execution_id'], str) and re.fullmatch(r'[0-9a-f]{32}', record['execution_id']),
            'invalid execution ID')
    require(isinstance(record['finished_at'], str) and
            re.fullmatch(r'\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d\+00:00', record['finished_at']), 'invalid finish time')
    datetime.fromisoformat(record['finished_at'])
    validate_metadata(record['review'])
    require(record['review']['pr'] <= 2**63-1, 'PR number exceeds archive range')
    require(record['review']['repository'] == repository and REPOSITORY.fullmatch(repository), 'wrong archive repository')
    require(isinstance(record['runs'], list) and len(record['runs']) <= 100, 'invalid archive runs')
    if v2:
        request = record['request']
        require(isinstance(request, dict) and set(request) == {'auth', 'shadow', 'rubrics', 'context', 'daily_budget_usd', 'shadow_budget_usd'}, 'invalid request facts')
        require(request['auth'] in ('api', 'subscription'), 'invalid authentication mode')
        require(isinstance(request['rubrics'], list) and request['rubrics'] and
                all(isinstance(r, str) and r in RUBRICS for r in request['rubrics']) and
                request['rubrics'] == [r for r in RUBRICS if r in request['rubrics']], 'invalid requested rubrics')
        shadow = record['review']['execution_mode'] == 'shadow'
        for key in ('daily_budget_usd', 'shadow_budget_usd'):
            value = request[key]
            if key == 'shadow_budget_usd' and not shadow:
                require(value is None, 'non-shadow request has a shadow allowance')
            else:
                require(type(value) in (int, float) and 0 < value <= 1e12, 'invalid requested budget')
        require((isinstance(request['shadow'], str) and re.fullmatch(r'[A-Za-z0-9_-]{1,80}', request['shadow']))
                if shadow else request['shadow'] is None, 'invalid shadow arm')
        require(request['context'] == ('fresh_shadow' if shadow else 'prior_case_possible'), 'invalid context classification')
    for run in record['runs']:
        validate_run(run, v2=v2)
        if v2:
            require(datetime.fromisoformat(run['started_at']) <= datetime.fromisoformat(record['finished_at']),
                    'run starts after execution finished')
    require(len({r['run_id'] for r in record['runs']}) == len(record['runs']), 'duplicate producer run')
    require(record['text_blob'] is None or (isinstance(record['text_blob'], str) and
            re.fullmatch(HEX, record['text_blob'])), 'invalid text reference')


def validate(files, repository, *, anchored=False):
    require(len(files) <= MAX_FILES and sum(map(len, files.values())) <= MAX_TOTAL, 'archive inventory limit exceeded')
    anchor = encode({'schema': SCHEMA, 'repository': repository, 'branch': 'review-data'})
    if anchored:
        require(files.get('ARCHIVE.json') == anchor, 'review-data requires its exact archive anchor')
    records, blobs = [], set()
    for name, body in files.items():
        require(isinstance(body, bytes) and len(body) <= MAX_FILE, 'oversized archive entry')
        if anchored and name == 'ARCHIVE.json':
            continue
        record_path, blob_path = RECORD_PATH.fullmatch(name), BLOB_PATH.fullmatch(name)
        if record_path:
            require(record_path[1] == digest(body), 'archive record content hash mismatch')
            record = parse_json(body.decode())
            require(encode(record) == body, 'archive JSON must be canonical')
            validate_record(record, repository)
            records.append(record)
        elif blob_path:
            require(blob_path[1] == blob_path[2][:2], 'wrong blob shard')
            try:
                with gzip.GzipFile(fileobj=io.BytesIO(body)) as f:
                    plain = f.read(MAX_FILE + 1)
                plain.decode()
            except (OSError, EOFError, UnicodeError) as error:
                raise ArchiveError('invalid compressed text') from error
            require(len(plain) <= MAX_FILE and digest(plain) == blob_path[2], 'blob hash/size mismatch')
            require(compress(plain) == body, 'noncanonical gzip blob')
            blobs.add(blob_path[2])
        else:
            raise ArchiveError('unexpected archive path; code, state, and databases are not archive entries')
    require(all(r['text_blob'] is None or r['text_blob'] in blobs for r in records), 'missing text blob')
    require(blobs == {r['text_blob'] for r in records if r['text_blob']}, 'unreferenced text blob')
    executions = {}
    for record in records:
        facts = {k: v for k, v in record.items() if k != 'text_blob'}
        prior = executions.setdefault(record['execution_id'], facts)
        require(prior == facts, 'conflicting facts for one execution ID')
    return records


def snapshot(root: Path):
    root = safe_path(root)
    require(root.is_dir(), 'archive directory is missing')
    files = {}
    count, total = 0, 0
    for directory, dirs, names in os.walk(root, followlinks=False):
        for name in [*dirs, *names]:
            path = Path(directory) / name
            safe_path(path)
            count += 1
            require(count <= MAX_FILES * 3, 'archive inventory limit exceeded')
        for name in names:
            path = Path(directory) / name
            body = read(path)
            files[path.relative_to(root).as_posix()] = body
            total += len(body)
            require(total <= MAX_TOTAL, 'archive size limit exceeded')
    return files


def enqueue(output: Path, store: Path, repository: str, *, include_text=False):
    """Recoverable from a completed output; never publish or upload private engine directories."""
    result = parse_json(read(output / 'result.json').decode())
    rendered = read(output / 'record.md').decode()
    review = parse_record(rendered)
    require(parse_json(read(output / 'record.json').decode()) == review, 'local review files disagree')
    require(all(result.get(k) == review[k] for k in (*BINDINGS, 'completion', 'execution_mode', 'verdicts')),
            'result and review bindings disagree')
    producer = output / ('shadow-archive' if review['execution_mode'] == 'shadow' else 'engine-archive') / 'records/runs'
    request = result.get('evaluation_request')
    runs = []
    if producer.exists():
        for body in snapshot(producer).values():
            runs.append(project_run(parse_json(body.decode()), review, request))
    record = {'schema': SCHEMA, 'execution_id': result['execution_id'], 'finished_at': result['finished_at'],
              'review': review, 'runs': sorted(runs, key=lambda r: r['run_id']), 'text_blob': None}
    if request is not None:
        record.update(schema=RECORD_V2, request=request)
    files = {}
    if include_text:
        text = rendered.split('-->\n\n', 1)[1]
        for pattern, replacement in REDACTIONS:
            text = re.sub(pattern, replacement, text)
        body = text.encode()
        key = digest(body)
        record['text_blob'] = key
        files[f'blobs/{key[:2]}/{key}.gz'] = compress(body)
    body = encode(record)
    name = f'records/{digest(body)}.json'
    files[name] = body
    validate(files, repository)
    with locked(store):
        # Journal first. A crash during outbox staging can be repaired by re-enqueuing output.
        for lane in ('journal', 'outbox'):
            for path, content in files.items():
                immutable(store / lane / path, content)
    return {'state': 'queued', 'record': name, 'runs': len(runs), 'text_included': include_text}


def capture(output, store, repository):
    """Archive failures are observable but never invalidate a completed/posted review."""
    try:
        return enqueue(output, store, repository)
    except (OSError, ValueError, KeyError, TypeError):
        return {'state': 'error', 'reason': 'local archive capture failed; retain output and retry archive enqueue'}


def rebuild(files, repository, output: Path):
    records = validate(files, repository, anchored='ARCHIVE.json' in files)
    output = safe_path(output)
    require(not output.exists(), 'derived database output must be new')
    # Reserve the destination exclusively; callers keep it outside archive/state trees.
    fd = os.open(output, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    os.close(fd)
    try:
        with closing(sqlite3.connect(output)) as db, db:
            db.executescript('''
                CREATE TABLE executions (execution_id TEXT PRIMARY KEY, finished_at TEXT,
                    repository TEXT, pr INTEGER, head TEXT, metadata_json TEXT);
                CREATE TABLE runs (execution_id TEXT, run_id TEXT, provider TEXT, model TEXT,
                    rubric TEXT, prompt_policy TEXT, usage_json TEXT, cost_usd REAL,
                    facts_json TEXT, PRIMARY KEY (execution_id, run_id));
                CREATE TABLE records (archive_id TEXT PRIMARY KEY, execution_id TEXT, text_blob TEXT);
            ''')
            seen = set()
            for record in records:
                key = digest(encode(record))
                execution = record['execution_id']
                db.execute('INSERT INTO records VALUES (?,?,?)', (key, execution, record['text_blob']))
                if execution in seen:
                    continue
                seen.add(execution)
                review = record['review']
                db.execute('INSERT INTO executions VALUES (?,?,?,?,?,?)', (execution,
                           record['finished_at'], repository, review['pr'], review['head'], canonical(record)))
                for run in record['runs']:
                    db.execute('INSERT INTO runs VALUES (?,?,?,?,?,?,?,?,?)', (execution, run['run_id'], run['provider'],
                               run['model'], run['rubric'], run['prompt_policy'],
                               canonical(run.get('usage')), run.get('cost_usd'), canonical(run)))
    except Exception:
        output.unlink(missing_ok=True)
        raise
    return {'state': 'rebuilt', 'records': len(records), 'database': str(output)}
