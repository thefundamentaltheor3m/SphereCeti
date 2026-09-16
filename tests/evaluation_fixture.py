"""Synthetic archive/price inputs and installed provider-free evaluation smoke."""
import copy
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools/project'))
from sphereceti.archive_store import RECORD_V2, compress, digest, encode
from sphereceti.local_review import RUBRICS
from sphereceti.review_records import BINDINGS, canonical, make_record, sha

REPO = 'thefundamentaltheor3m/SphereCeti'


def record(execution='a', arm='first', model='model-one', day='2026-09-10'):
    result = {k: 'a'*64 for k in BINDINGS}
    result.update(repository=REPO, pr=1, head='2'*40, base='3'*40, diff_base='3'*40, tooling='1'*40,
                  completion='partial', execution_mode='shadow', tooling_approved=False,
                  installed_tooling_matches_T=False, missing_context=[], config_differences=[],
                  verdicts={r: 'approve' if r == 'correctness' else 'absent' for r in RUBRICS}, reviews={})
    review, _ = make_record(result)
    run = {'run_id': 'run-' + execution, 'provider': 'codex', 'model': model, 'rubric': 'correctness',
           'prompt_policy': 'fresh', 'prompt_sha256': 'f'*64, 'prices_sha': 'abcdef123456',
           'started_at': day + 'T00:00:00Z', 'usage': {'input_tokens': 100, 'cached_input_tokens': 20,
                                                   'output_tokens': 10, 'reasoning_output_tokens': 4},
           'cost_usd': 0.3, 'cost_estimated': False,
           'attempts': [{'model': model, 'returncode': 0, 'cost_usd': 0.3, 'usage': {'input_tokens': 100}}]}
    return {'schema': RECORD_V2, 'execution_id': execution*32, 'finished_at': day + 'T01:00:00+00:00',
            'review': review, 'runs': [run], 'text_blob': None,
            'request': {'auth': 'api', 'shadow': arm, 'rubrics': ['correctness'], 'context': 'fresh_shadow', 'daily_budget_usd': 5, 'shadow_budget_usd': 1}}


def rehash(record):
    review = record['review']
    review['record_id'] = sha(canonical({k: v for k, v in review.items() if k != 'record_id'}))
    return record


def archive(*records, text=False):
    files = {}
    for original in records:
        value = copy.deepcopy(original)
        if text:
            plain = ('Rendered review ' + value['execution_id'][:1]).encode()
            key = digest(plain)
            value['text_blob'] = key
            files[f'blobs/{key[:2]}/{key}.gz'] = compress(plain)
        body = encode(value)
        files[f'records/{digest(body)}.json'] = body
    return files


def price_file():
    return encode({'schema_version': 1, 'models': {name: [
        {'effective': '2026-09-01', 'input': '2', 'output': '4', 'cache_read': '0.5', 'input_convention': 'total'},
        {'effective': '2026-09-11', 'input': '3', 'output': '6', 'cache_read': '1', 'input_convention': 'total',
         'long_context': {'threshold': 100, 'input': '5', 'output': '10', 'cache_read': '2'}}]
        for name in ('model-one', 'model-two')}})


def installed_evaluation_smoke(executable, root):
    source = root / 'source'
    source.mkdir(parents=True)
    for path, body in archive(record(), record('b', 'second', 'model-two'), text=True).items():
        target = source / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(body)
    operator = root / 'operator.toml'
    operator.write_text('storage = ' + json.dumps(str(root / 'state')) + '\n')
    prices = root / 'prices.json'
    prices.write_bytes(price_file())
    def run(action, *args):
        process = subprocess.run([str(executable), 'evaluation', action, '--source', str(source),
                                  '--operator-config', str(operator), '--json', *args],
                                 cwd=root, capture_output=True, text=True, timeout=30)
        assert process.returncode == 0, process.stderr
        return json.loads(process.stdout)
    costs = run('costs', '--prices', str(prices))
    assert costs['totals']['recorded_usd']['sum_known'] == '0.6'
    assert costs['totals']['repriced_usd']['sum_known'] == '0.00042'
    pair = run('pair', '--left', 'a'*32, '--right', 'b'*32)['pair_id']
    shown = run('show', '--pair', pair)
    assert 'Rendered review' in shown['A'] and 'model-one' not in json.dumps(shown)
    label = run('label', '--pair', pair, '--reviewer', 'human', '--choice', 'tie')
    assert run('label', '--pair', pair, '--reviewer', 'human', '--choice', 'tie') == label
    assert len(run('labels', '--pair', pair)['labels']) == 1
