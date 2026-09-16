"""Offline costs, controlled shadow pairs and local human labels; never review authority.

Adapts TauCetiProject/TauCetiReview@afb424eda89e8ac96d9eb69f6a88972055a4cd1b:
runner/costs.py, pricing.py, prices.json, cli.py and review.py (Apache-2.0, upstream
contributors). SphereCeti's schemas and label interface are original; no TauCetiData code.
"""
from __future__ import annotations

from datetime import date
from decimal import Decimal, InvalidOperation, localcontext
import gzip
import json
from pathlib import Path
import re

from .archive_store import (ArchiveError, RECORD_V2, TOKEN_FIELDS, digest, encode, immutable,
                            locked, read, require, snapshot, validate)
from .review_records import BINDINGS, parse_json

PAIR_SCHEMA = 'sphereceti.evaluation-pair/v1'
LABEL_SCHEMA = 'sphereceti.evaluation-label/v1'
ID = re.compile(r'[0-9a-f]{64}\Z')


def decimal(value):
    require(type(value) in (str, int, float) and len(str(value)) <= 40, 'invalid decimal rate')
    try:
        value = Decimal(str(value))
    except InvalidOperation as error:
        raise ArchiveError('invalid decimal rate') from error
    require(value.is_finite() and 0 <= value <= 1_000_000, 'rate must be finite and nonnegative')
    require(value.as_tuple().exponent >= -12, 'rate precision exceeds 12 decimal places')
    return value


def money(value):
    return format(value, 'f')


def prices(body):
    """Explicit dated inputs only; never fetch current prices or substitute an unpriced model."""
    data = parse_json(body.decode())
    require(isinstance(data, dict) and set(data) == {'schema_version', 'models'} and
            type(data['schema_version']) is int and data['schema_version'] == 1, 'invalid pricing schema')
    require(isinstance(data['models'], dict) and 0 < len(data['models']) <= 100, 'invalid pricing models')
    for model, windows in data['models'].items():
        require(isinstance(model, str) and re.fullmatch(r'[A-Za-z0-9_./+-]{1,160}', model), 'invalid priced model')
        require(isinstance(windows, list) and 0 < len(windows) <= 100, 'invalid price windows')
        previous = ''
        for window in windows:
            required = {'effective', 'input', 'output', 'cache_read', 'input_convention'}
            require(isinstance(window, dict) and required <= set(window) <= required | {'cache_write', 'long_context'},
                    'invalid dated rate fields')
            stamp = window['effective']
            require(isinstance(stamp, str) and re.fullmatch(r'\d{4}-\d\d-\d\d', stamp), 'invalid effective date')
            date.fromisoformat(stamp)
            require(stamp > previous, 'price windows must be strictly increasing')
            previous = stamp
            require(window['input_convention'] in ('total', 'uncached'), 'declare how input tokens count cache reads')
            for key in ('input', 'output', 'cache_read', 'cache_write'):
                if key in window:
                    decimal(window[key])
            if 'long_context' in window:
                tier = window['long_context']
                require(isinstance(tier, dict) and {'threshold', 'input', 'output', 'cache_read'} <= set(tier)
                        <= {'threshold', 'input', 'output', 'cache_read', 'cache_write'}, 'invalid long-context tier')
                require(type(tier['threshold']) is int and 0 < tier['threshold'] <= 2**63-1, 'invalid tier threshold')
                for key in set(tier) - {'threshold'}:
                    decimal(tier[key])
    return data['models']


def execution_facts(record):
    return {k: v for k, v in record.items() if k != 'text_blob'}


def executions(files, repository):
    records = validate(files, repository, anchored='ARCHIVE.json' in files)
    grouped = {}
    for record in records:
        key = record['execution_id']
        item = grouped.setdefault(key, {'facts': execution_facts(record), 'texts': set()})
        if record['text_blob']:
            item['texts'].add(record['text_blob'])
    for item in grouped.values():
        require(len(item['texts']) <= 1, 'conflicting text variants for one execution')
    return grouped


def reprice(run, history, *, as_of=None):
    """One dispatch only: retries may mix models and dates, so do not price their last usage as the total."""
    if 'started_at' not in run:
        return None, 'missing_run_time', None
    if len(run['attempts']) != 1 or run['attempts'][0].get('model') != run['model']:
        return None, 'retry_or_missing_attempt_provenance', None
    day = as_of or run['started_at'][:10]
    windows = [w for w in history.get(run['model'], []) if w['effective'] <= day]
    if not windows:
        return None, 'no_effective_price', None
    window = windows[-1]
    usage = run.get('usage') or {}
    if not {'input_tokens', 'output_tokens'} <= set(usage):
        return None, 'missing_token_counts', window['effective']
    cached = [usage[k] for k in ('cached_input_tokens', 'cache_read_input_tokens') if k in usage]
    if not cached or len(set(cached)) != 1:
        return None, 'unknown_or_conflicting_cache_counts', window['effective']
    inp, out, cache = usage['input_tokens'], usage['output_tokens'], cached[0]
    write = usage.get('cache_creation_input_tokens', 0)
    if window['input_convention'] == 'total':
        if cache > inp or write:
            return None, 'incompatible_total_input_counts', window['effective']
        uncached, full = inp - cache, inp
    else:
        if 'cache_creation_input_tokens' not in usage:
            return None, 'unknown_cache_write_count', window['effective']
        uncached, full = inp, inp + cache + write
    tier = window.get('long_context')
    rates = tier if tier and full > tier['threshold'] else window
    if write and 'cache_write' not in rates:
        return None, 'missing_cache_write_price', window['effective']
    cost = (uncached * decimal(rates['input']) + cache * decimal(rates['cache_read']) +
            out * decimal(rates['output']) + write * decimal(rates.get('cache_write', 0))) / Decimal(1_000_000)
    return cost, 'derived_estimate', window['effective']


def cost_report(files, repository, *, price_bytes=None, as_of=None):
    require(as_of is None or price_bytes is not None, '--as-of requires a price snapshot')
    if as_of is not None:
        require(re.fullmatch(r'\d{4}-\d\d-\d\d', as_of), 'invalid forecast date')
        date.fromisoformat(as_of)
    history = prices(price_bytes) if price_bytes is not None else None
    groups = executions(files, repository)
    rows = []
    with localcontext() as ctx:
        ctx.prec = 60
        for execution, item in sorted(groups.items()):
            record = item['facts']
            for run in sorted(record['runs'], key=lambda r: r['run_id']):
                derived, state, window = reprice(run, history, as_of=as_of) if history is not None else (None, 'not_requested', None)
                rows.append({'execution_id': execution, 'run_id': run['run_id'], 'pr': record['review']['pr'],
                             'head': record['review']['head'], 'mode': record['review']['execution_mode'],
                             'provider': run['provider'], 'model': run['model'], 'rubric': run['rubric'],
                             'prompt_policy': run['prompt_policy'], 'started_at': run.get('started_at'),
                             'usage': run.get('usage'), 'attempts': run['attempts'],
                             'recorded_usd': money(Decimal(str(run['cost_usd']))) if 'cost_usd' in run else None,
                             'cost_estimated': run.get('cost_estimated'), 'recorded_prices_id': run.get('prices_sha'),
                             'repriced_usd': money(derived) if derived is not None else None,
                             'repricing_state': state, 'effective_price_date': window})
        def aggregate(selected):
            result = {'runs': len(selected),
                      'runs_with_retry_or_unknown_attempts': sum(len(r['attempts']) != 1 for r in selected)}
            for key in ('recorded_usd', 'repriced_usd'):
                known = [Decimal(r[key]) for r in selected if r[key] is not None]
                result[key] = {'sum_known': money(sum(known, Decimal(0))), 'known_runs': len(known),
                               'unknown_runs': len(selected) - len(known)}
            result['tokens'] = {k: {'sum_known': sum(r['usage'][k] for r in selected if k in (r['usage'] or {})),
                                  'known_runs': sum(k in (r['usage'] or {}) for r in selected),
                                  'unknown_runs': sum(k not in (r['usage'] or {}) for r in selected)}
                               for k in sorted(TOKEN_FIELDS)}
            return result
        modes = {mode: aggregate([r for r in rows if r['mode'] == mode]) for mode in sorted({r['mode'] for r in rows})}
        return {'schema': 'sphereceti.evaluation-costs/v1', 'repository': repository,
                'input_digest': digest(encode({k: v['facts'] for k, v in sorted(groups.items())})),
                'prices_sha256': digest(price_bytes) if price_bytes is not None else None,
                'price_basis': 'forecast:' + as_of if as_of else 'run_start_date',
                'token_basis': 'run_reported_usage; retries may contain only final-attempt usage',
                'executions': len(groups), 'executions_without_runs': sum(not v['facts']['runs'] for v in groups.values()),
                'totals': aggregate(rows), 'by_mode': modes, 'rows': rows,
                'advisory': True, 'merge_eligible': False}


def comparison(left, right):
    require(left['execution_id'] != right['execution_id'], 'choose two distinct executions')
    for record in (left, right):
        require(record['schema'] == RECORD_V2, 'legacy archive lacks explicit comparison context')
        request, review = record['request'], record['review']
        require(review['execution_mode'] == 'shadow' and request['context'] == 'fresh_shadow',
                'only fresh shadow executions can form a controlled pair')
        require(review['completion'] != 'error' and review['advisory'], 'errored/non-advisory shadow execution')
        rubrics = request['rubrics']
        require(sorted(r['rubric'] for r in record['runs']) == sorted(rubrics), 'missing, duplicate or unrequested rubric run')
        for run in record['runs']:
            require(run['prompt_policy'] == 'fresh', 'prior-case/reactivation runs cannot be paired with fresh shadows')
            require(review['verdicts'][run['rubric']] in ('approve', 'request_changes', 'block'), 'missing valid rubric verdict')
            attempts = run['attempts']
            require(len(attempts) == 1 and attempts[0].get('returncode') == 0
                    and attempts[0].get('model') == run['model'], 'retried, failed or ambiguous dispatch')
    for field in (*BINDINGS, 'tooling_revision'):
        require(left['review'][field] == right['review'][field], 'pair evidence differs: ' + field)
    for field in ('auth', 'rubrics', 'context'):
        require(left['request'][field] == right['request'][field], 'pair request differs: ' + field)
    require(left['request']['shadow'] != right['request']['shadow'], 'pair requires distinct named arms')
    ordered = sorted((left, right), key=lambda r: r['execution_id'])
    # Stable, order-independent presentation. This is pseudorandom counterbalancing, not a
    # guarantee of blinded prose or a statistical experimental design.
    identity = digest(encode([digest(encode(r)) for r in ordered]))
    if int(identity[0], 16) % 2:
        ordered.reverse()
    case = {'schema': PAIR_SCHEMA, 'repository': left['review']['repository'],
            'A': {'execution_id': ordered[0]['execution_id'], 'facts_sha256': digest(encode(ordered[0]))},
            'B': {'execution_id': ordered[1]['execution_id'], 'facts_sha256': digest(encode(ordered[1]))},
            'rubrics': left['request']['rubrics'], 'advisory': True, 'merge_eligible': False}
    return case


def case_from_source(files, repository, case):
    require(isinstance(case, dict) and set(case) == {'schema', 'repository', 'A', 'B', 'rubrics', 'advisory', 'merge_eligible'}
            and case['schema'] == PAIR_SCHEMA and case['repository'] == repository, 'invalid evaluation pair')
    groups = executions(files, repository)
    records = []
    for side in ('A', 'B'):
        require(isinstance(case[side], dict) and set(case[side]) == {'execution_id', 'facts_sha256'}, 'invalid pair side')
        key = case[side]['execution_id']
        require(isinstance(key, str) and key in groups, 'pair execution missing from source')
        record = groups[key]['facts']
        require(digest(encode(record)) == case[side]['facts_sha256'], 'pair source facts changed')
        records.append(record)
    require(comparison(*records) == case, 'pair has changed or incompatible evidence')
    return groups


def save_pair(files, repository, store, left, right):
    groups = executions(files, repository)
    require(left in groups and right in groups, 'selected execution missing')
    case = comparison(groups[left]['facts'], groups[right]['facts'])
    body = encode(case)
    key = digest(body)
    with locked(store):
        immutable(store / 'pairs' / (key + '.json'), body)
    return {'state': 'paired', 'pair_id': key, 'pair': case}


def load_pair(store, key):
    require(isinstance(key, str) and ID.fullmatch(key), 'invalid pair ID')
    body = read(store / 'pairs' / (key + '.json'))
    require(digest(body) == key, 'pair file integrity mismatch')
    case = parse_json(body.decode())
    require(encode(case) == body, 'pair JSON must be canonical')
    return case


def show_pair(files, repository, store, key):
    case = load_pair(store, key)
    groups = case_from_source(files, repository, case)
    display = {'pair_id': key, 'rubrics': case['rubrics'], 'advisory': True, 'merge_eligible': False}
    for side in ('A', 'B'):
        texts = groups[case[side]['execution_id']]['texts']
        require(len(texts) == 1, 'pair display requires explicitly archived review text for both executions')
        blob = next(iter(texts))
        display[side] = gzip.decompress(files[f'blobs/{blob[:2]}/{blob}.gz']).decode()
    return display


def labels(store, case, key):
    require(isinstance(key, str) and ID.fullmatch(key) and digest(encode(case)) == key, 'invalid pair identity')
    root = store / 'labels' / key
    values = []
    if not root.exists():
        return values
    for path, body in sorted(snapshot(root).items()):
        require(re.fullmatch(r'[0-9a-f]{64}\.json', path) and digest(body) == path[:-5], 'invalid label path/hash')
        label = parse_json(body.decode())
        require(encode(label) == body, 'label JSON must be canonical')
        require(isinstance(label, dict) and set(label) ==
                {'schema', 'pair_id', 'reviewer', 'choice', 'supersedes', 'advisory', 'merge_eligible'}, 'invalid label fields')
        require(label['schema'] == LABEL_SCHEMA and label['pair_id'] == key and label['advisory'] is True
                and label['merge_eligible'] is False, 'label cannot supply review authority')
        require(isinstance(label['reviewer'], str) and re.fullmatch(r'[A-Za-z0-9_-]{1,80}', label['reviewer']), 'invalid local reviewer name')
        require(label['choice'] in ('A', 'B', 'tie', 'neither', 'unsure'), 'invalid label choice')
        require(label['supersedes'] is None or (isinstance(label['supersedes'], str) and ID.fullmatch(label['supersedes'])), 'invalid label predecessor')
        values.append({'id': path[:-5], **label})
    by_id = {v['id']: v for v in values}
    successors = {}
    for value in values:
        previous = value['supersedes']
        if previous is not None:
            require(previous in by_id and by_id[previous]['reviewer'] == value['reviewer'], 'label predecessor missing or belongs to another reviewer')
            require(previous not in successors, 'branched label history')
            successors[previous] = value['id']
    heads = [v for v in values if v['id'] not in successors]
    require(len({v['reviewer'] for v in heads}) == len(heads), 'conflicting labels by one reviewer')
    for value in values:
        seen = set()
        current = value
        while current['supersedes'] is not None:
            require(current['id'] not in seen, 'cyclic label history')
            seen.add(current['id'])
            current = by_id[current['supersedes']]
    return heads


def label_pair(files, repository, store, key, reviewer, choice, supersedes=None):
    case = load_pair(store, key)
    case_from_source(files, repository, case)
    require(isinstance(reviewer, str) and re.fullmatch(r'[A-Za-z0-9_-]{1,80}', reviewer), 'use a simple local reviewer name')
    require(choice in ('A', 'B', 'tie', 'neither', 'unsure'), 'invalid choice')
    value = {'schema': LABEL_SCHEMA, 'pair_id': key, 'reviewer': reviewer, 'choice': choice,
             'supersedes': supersedes, 'advisory': True, 'merge_eligible': False}
    body = encode(value)
    identity = digest(body)
    with locked(store):
        heads = labels(store, case, key)
        current = next((v for v in heads if v['reviewer'] == reviewer), None)
        if current and current['id'] == identity:
            return {'state': 'recorded', 'label_id': identity, 'label': value}
        require((current is None and supersedes is None) or (current is not None and supersedes == current['id']),
                'label already exists; corrections must explicitly supersede its current ID')
        immutable(store / 'labels' / key / (identity + '.json'), body)
    return {'state': 'recorded', 'label_id': identity, 'label': value}
