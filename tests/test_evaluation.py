"""Reproducible cost facts, strict pairing and append-only human labels; no paid inference."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from evaluation_fixture import archive, installed_evaluation_smoke, price_file, record, rehash, REPO
from sphereceti.archive_store import ArchiveError, SCHEMA, encode, digest, immutable, snapshot, validate
from sphereceti.evaluation import (case_from_source, cost_report, execution_facts, label_pair, labels,
                                  load_pair, prices, save_pair, show_pair)


class EvaluationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.left = record()
        self.right = record('b', 'second', 'model-two')
        self.store = self.root / 'evaluation'

    def test_worker_text_output_keeps_its_own_renderer(self):
        from contextlib import redirect_stdout
        from io import StringIO
        from sphereceti import cli
        output=StringIO()
        with redirect_stdout(output):
            self.assertEqual(cli.main(['worker','run','--execute']),0)
        self.assertIn('SphereCeti worker: disabled',output.getvalue())

    def pair(self, files=None):
        return save_pair(files or archive(self.left, self.right), REPO, self.store, 'a'*32, 'b'*32)

    def test_dated_repricing_keeps_recorded_cost_and_immutable_tokens(self):
        files = archive(self.left, self.right)
        original = copy.deepcopy(files)
        report = cost_report(files, REPO, price_bytes=price_file())
        self.assertEqual(report['totals']['recorded_usd']['sum_known'], '0.6')
        self.assertEqual(report['totals']['repriced_usd']['sum_known'], '0.00042')
        self.assertEqual(report['rows'][0]['recorded_usd'], '0.3')
        self.assertEqual(report['rows'][0]['effective_price_date'], '2026-09-01')
        self.assertEqual(report['rows'][0]['usage']['reasoning_output_tokens'], 4)
        self.assertEqual(files, original)
        self.assertFalse(report['merge_eligible'])

    def test_explicit_forecast_and_date_boundary_use_named_price_snapshot(self):
        files = archive(self.left)
        past = cost_report(files, REPO, price_bytes=price_file())
        forecast = cost_report(files, REPO, price_bytes=price_file(), as_of='2026-09-11')
        self.assertEqual(past['rows'][0]['repriced_usd'], '0.00021')
        self.assertEqual(forecast['rows'][0]['repriced_usd'], '0.00032')
        self.assertEqual(past['prices_sha256'], forecast['prices_sha256'])
        self.assertEqual(past['input_digest'], forecast['input_digest'])
        with self.assertRaises(ValueError):
            cost_report(files, REPO, as_of='2026-09-11')

    def test_no_backdating_or_unknown_model_fallback(self):
        for changes in ({'model': 'unknown'}, {'started_at': '2026-08-31T00:00:00Z'}):
            value = copy.deepcopy(self.left)
            value['runs'][0].update(changes)
            value['runs'][0]['attempts'][0]['model'] = value['runs'][0]['model']
            row = cost_report(archive(value), REPO, price_bytes=price_file())['rows'][0]
            self.assertIsNone(row['repriced_usd'])
            self.assertEqual(row['repricing_state'], 'no_effective_price')

    def test_unknown_cost_and_tokens_have_explicit_coverage(self):
        del self.left['runs'][0]['cost_usd']
        del self.left['runs'][0]['usage']
        report = cost_report(archive(self.left, self.right), REPO, price_bytes=price_file())
        self.assertEqual(report['totals']['recorded_usd'], {'sum_known': '0.3', 'known_runs': 1, 'unknown_runs': 1})
        self.assertEqual(report['totals']['tokens']['input_tokens'], {'sum_known': 100, 'known_runs': 1, 'unknown_runs': 1})
        self.assertIsNone(report['rows'][0]['usage'])

    def test_retries_are_not_double_counted_or_repriced_from_last_attempt(self):
        self.left['runs'][0]['attempts'].append({'model': 'another-model', 'cost_usd': .9, 'returncode': 0})
        report = cost_report(archive(self.left), REPO, price_bytes=price_file())
        self.assertEqual(report['totals']['recorded_usd']['sum_known'], '0.3')
        self.assertIsNone(report['rows'][0]['repriced_usd'])
        self.assertEqual(report['rows'][0]['repricing_state'], 'retry_or_missing_attempt_provenance')

    def test_legacy_records_are_readable_but_not_given_invented_dates(self):
        self.left['schema'] = SCHEMA
        del self.left['request']
        del self.left['runs'][0]['started_at']
        files = archive(self.left)
        validate(files, REPO)
        report = cost_report(files, REPO, price_bytes=price_file())
        self.assertEqual(report['rows'][0]['repricing_state'], 'missing_run_time')
        with self.assertRaisesRegex(ArchiveError, 'legacy'):
            self.pair(archive(self.left, self.right))

    def test_text_variants_do_not_duplicate_costs_or_change_pair_identity(self):
        plain = archive(self.left, self.right)
        with_text = {**plain, **archive(self.left, self.right, text=True)}
        self.assertEqual(cost_report(plain, REPO), cost_report(with_text, REPO))
        self.assertEqual(self.pair(plain), self.pair(with_text))
        self.assertEqual(self.pair(plain), save_pair(plain, REPO, self.store, 'b'*32, 'a'*32))

    def test_price_windows_and_decimal_rates_fail_closed(self):
        base = json.loads(price_file())
        mutations = []
        duplicate = copy.deepcopy(base)
        duplicate['models']['model-one'].reverse()
        mutations.append(duplicate)
        for field, value in [('input', '-1'), ('output', 'NaN'), ('cache_read', True),
                             ('input_convention', 'guess'), ('effective', '2026-02-30')]:
            data = copy.deepcopy(base)
            data['models']['model-one'][0][field] = value
            mutations.append(data)
        for data in mutations:
            with self.subTest(data=data), self.assertRaises(ValueError):
                prices(encode(data))
        with self.assertRaises(ValueError):
            prices(b'{"schema_version":1,"schema_version":1,"models":{}}')

    def test_cache_semantics_and_whole_request_long_context_tier(self):
        self.left['runs'][0]['started_at'] = '2026-09-11T00:00:00Z'
        self.left['finished_at'] = '2026-09-11T01:00:00+00:00'
        row = cost_report(archive(self.left), REPO, price_bytes=price_file())['rows'][0]
        self.assertEqual(row['repriced_usd'], '0.00032')  # At threshold, ordinary tier.
        self.left['runs'][0]['usage']['input_tokens'] = 101
        row = cost_report(archive(self.left), REPO, price_bytes=price_file())['rows'][0]
        self.assertEqual(row['repriced_usd'], '0.000545')
        self.left['runs'][0]['usage']['cached_input_tokens'] = 102
        row = cost_report(archive(self.left), REPO, price_bytes=price_file())['rows'][0]
        self.assertIsNone(row['repriced_usd'])

    def test_missing_and_conflicting_cache_fields_are_not_assumed_zero(self):
        del self.left['runs'][0]['usage']['cached_input_tokens']
        self.assertIsNone(cost_report(archive(self.left), REPO, price_bytes=price_file())['rows'][0]['repriced_usd'])
        self.left['runs'][0]['usage'].update(cached_input_tokens=20, cache_read_input_tokens=21)
        self.assertIsNone(cost_report(archive(self.left), REPO, price_bytes=price_file())['rows'][0]['repriced_usd'])

    def test_every_source_binding_and_request_constraint_is_checked(self):
        from sphereceti.review_records import BINDINGS
        for field in (*BINDINGS, 'tooling_revision'):
            if field == 'repository':
                continue  # Whole archive validation already fixes repository.
            value = copy.deepcopy(self.right)
            value['review'][field] = 2 if field == 'pr' else 'c' * len(value['review'][field])
            rehash(value)
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.pair(archive(self.left, value))
        value = copy.deepcopy(self.right)
        value['request']['auth'] = 'subscription'
        with self.assertRaisesRegex(ArchiveError, 'auth'):
            self.pair(archive(self.left, value))

    def test_partial_retried_reactivation_and_repeated_arms_do_not_pair(self):
        variants = []
        value = copy.deepcopy(self.right); value['runs'] = []; variants.append(value)
        value = copy.deepcopy(self.right); value['runs'].append(copy.deepcopy(value['runs'][0])); variants.append(value)
        value = copy.deepcopy(self.right); value['runs'][0]['prompt_policy'] = 'reactivation'; variants.append(value)
        value = copy.deepcopy(self.right); value['request']['shadow'] = 'first'; variants.append(value)
        value = copy.deepcopy(self.right); value['runs'][0]['attempts'][0]['returncode'] = 1; variants.append(value)
        value = copy.deepcopy(self.right); value['runs'][0]['attempts'].append({'model': 'other'}); variants.append(value)
        value = copy.deepcopy(self.right); value['review']['completion'] = 'error'; rehash(value); variants.append(value)
        for value in variants:
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.pair(archive(self.left, value))

    def test_live_prior_case_reviews_never_get_classified_as_fresh(self):
        value = copy.deepcopy(self.right)
        value['request'].update(shadow=None, context='prior_case_possible', shadow_budget_usd=None)
        value['review']['execution_mode'] = 'manual'
        rehash(value)
        with self.assertRaisesRegex(ArchiveError, 'fresh shadow'):
            self.pair(archive(self.left, value))

    def test_show_requires_opt_in_text_and_hides_model_metadata(self):
        pair = self.pair()['pair_id']
        with self.assertRaisesRegex(ArchiveError, 'archived review text'):
            show_pair(archive(self.left, self.right), REPO, self.store, pair)
        shown = show_pair(archive(self.left, self.right, text=True), REPO, self.store, pair)
        self.assertNotIn('model-one', json.dumps(shown))
        self.assertIn('Rendered review', shown['A'])
        self.assertFalse(shown['merge_eligible'])

    def test_pair_cannot_be_replayed_against_changed_facts(self):
        pair = self.pair()['pair_id']
        self.right['runs'][0]['cost_usd'] = 1
        with self.assertRaisesRegex(ArchiveError, 'facts changed'):
            case_from_source(archive(self.left, self.right), REPO, load_pair(self.store, pair))

    def test_labels_are_idempotent_local_and_allow_explicit_corrections(self):
        files = archive(self.left, self.right)
        pair = self.pair(files)['pair_id']
        first = label_pair(files, REPO, self.store, pair, 'alice', 'tie')
        self.assertEqual(first, label_pair(files, REPO, self.store, pair, 'alice', 'tie'))
        with self.assertRaisesRegex(ArchiveError, 'supersede'):
            label_pair(files, REPO, self.store, pair, 'alice', 'A')
        corrected = label_pair(files, REPO, self.store, pair, 'alice', 'A', first['label_id'])
        self.assertNotEqual(corrected['label_id'], first['label_id'])
        self.assertEqual(corrected, label_pair(files, REPO, self.store, pair, 'alice', 'A', first['label_id']))
        label_pair(files, REPO, self.store, pair, 'bob', 'B')
        current = labels(self.store, load_pair(self.store, pair), pair)
        self.assertEqual(len(current), 2)
        self.assertTrue(all(r['advisory'] and not r['merge_eligible'] for r in current))
        self.assertEqual(len(snapshot(self.store / 'labels' / pair)), 3)

    def test_correction_cannot_replace_another_reviewer_or_stale_head(self):
        files = archive(self.left, self.right)
        pair = self.pair(files)['pair_id']
        first = label_pair(files, REPO, self.store, pair, 'alice', 'tie')
        for reviewer, previous in [('bob', first['label_id']), ('alice', '0'*64)]:
            with self.assertRaises(ArchiveError):
                label_pair(files, REPO, self.store, pair, reviewer, 'B', previous)

    def test_label_tampering_and_paths_fail_closed(self):
        files = archive(self.left, self.right)
        pair = self.pair(files)['pair_id']
        value = label_pair(files, REPO, self.store, pair, 'alice', 'A')
        path = self.store / 'labels' / pair / (value['label_id'] + '.json')
        path.write_bytes(path.read_bytes() + b'changed')
        with self.assertRaises(ArchiveError):
            labels(self.store, load_pair(self.store, pair), pair)
        with self.assertRaises(ArchiveError):
            load_pair(self.store, '../escape')

    def test_branched_label_history_is_not_silently_resolved(self):
        files = archive(self.left, self.right)
        pair = self.pair(files)['pair_id']
        first = label_pair(files, REPO, self.store, pair, 'alice', 'tie')
        label_pair(files, REPO, self.store, pair, 'alice', 'A', first['label_id'])
        fork = {**first['label'], 'choice': 'B', 'supersedes': first['label_id']}
        body = encode(fork)
        immutable(self.store / 'labels' / pair / (digest(body) + '.json'), body)
        with self.assertRaisesRegex(ArchiveError, 'branched'):
            labels(self.store, load_pair(self.store, pair), pair)

    def test_label_and_cost_outputs_cannot_enter_archive_or_review_acceptance(self):
        from sphereceti.review_records import parse_record
        files = archive(self.left, self.right)
        pair = self.pair(files)
        label = label_pair(files, REPO, self.store, pair['pair_id'], 'human', 'A')
        for report in (pair['pair'], label['label'], cost_report(files, REPO)):
            with self.assertRaises(ValueError):
                parse_record(json.dumps(report))
            body = encode(report)
            with self.assertRaises(ValueError):
                validate({f'records/{digest(body)}.json': body}, REPO)

    def test_installed_front_door_is_provider_and_network_free(self):
        import sys
        launcher = self.root / 'sphereceti'
        launcher.write_text(f'#!{sys.executable}\nimport sys\nsys.path.insert(0, {str(Path(__file__).resolve().parents[1] / "tools/project")!r})\n'
                           'def guard(event, args):\n'
                           '    if event.startswith("socket.") or event == "subprocess.Popen": raise RuntimeError("external call forbidden")\n'
                           'sys.addaudithook(guard)\nfrom sphereceti.cli import main\nsys.exit(main())\n')
        launcher.chmod(0o755)
        installed_evaluation_smoke(launcher, self.root / 'smoke')

    def test_uncached_input_prices_cache_reads_and_writes_as_separate_buckets(self):
        table = json.loads(price_file())
        window = table['models']['model-one'][0]
        window.update(input_convention='uncached', cache_write='3')
        usage = self.left['runs'][0]['usage']
        row = cost_report(archive(self.left), REPO, price_bytes=encode(table))['rows'][0]
        self.assertEqual(row['repricing_state'], 'unknown_cache_write_count')
        usage['cache_creation_input_tokens'] = 10
        row = cost_report(archive(self.left), REPO, price_bytes=encode(table))['rows'][0]
        self.assertEqual(row['repriced_usd'], '0.00028')
        del window['cache_write']
        row = cost_report(archive(self.left), REPO, price_bytes=encode(table))['rows'][0]
        self.assertEqual(row['repricing_state'], 'missing_cache_write_price')

    def test_v2_request_and_timestamp_forgery_is_rejected(self):
        variants = []
        value = copy.deepcopy(self.left); del value['request']; variants.append(value)
        value = copy.deepcopy(self.left); value['request']['context'] = 'prior_case_possible'; variants.append(value)
        value = copy.deepcopy(self.left); value['runs'][0]['started_at'] = '2026-09-11T00:00:00Z'; variants.append(value)
        value = copy.deepcopy(self.left); value['request']['daily_budget_usd'] = True; variants.append(value)
        value = copy.deepcopy(self.left); value['request']['rubrics'] *= 2; variants.append(value)
        for value in variants:
            with self.subTest(value=value), self.assertRaises(ValueError):
                validate(archive(value), REPO)

    def test_source_producer_must_match_v2_authentication_arm_and_mode(self):
        from sphereceti.archive_store import project_run
        source = {'schema': 'tauceti.run/v1', 'repo': REPO, 'pr': 1, 'head_sha': '2'*40,
                  'base_ref_oid': '3'*40, 'merge_base_sha': '3'*40, 'auth': 'api',
                  'mode': 'manual', 'arm': 'shadow:first', **self.left['runs'][0]}
        self.assertEqual(project_run(source, self.left['review'], self.left['request']), self.left['runs'][0])
        for field, replacement in [('auth', 'subscription'), ('arm', 'production'), ('mode', 'commit')]:
            with self.assertRaises(ArchiveError):
                project_run({**source, field: replacement}, self.left['review'], self.left['request'])

    def test_shadow_budget_uses_engine_selected_day_and_never_raises_global_cap(self):
        from types import SimpleNamespace
        from sphereceti.review_bridge import bound_shadow_budget
        for day, global_cap, expected in [('old-day', 10, 9), ('new-day', 10, 2), ('old-day', 8.5, 8.5)]:
            class Parser:
                def parse_args(self):
                    return SimpleNamespace(daily_budget=global_cap)
            class Ledger:
                def __init__(self, path):
                    self.data = {'days': {'old-day': 7, 'new-day': 0}}
            engine = SimpleNamespace(argparse=SimpleNamespace(ArgumentParser=Parser), Ledger=Ledger)
            bound_shadow_budget(engine, 2)
            args = engine.argparse.ArgumentParser().parse_args()
            ledger = engine.Ledger(None)
            ledger.data['days'].get(day, 0)
            self.assertEqual(args.daily_budget, expected)
            ledger.data['days'][day] += 1
            ledger.data['days'].get(day, 0)
            self.assertEqual(args.daily_budget, expected)


class ShadowExecutionTests(unittest.TestCase):
    def setUp(self):
        from review_fixture import ReviewFixture
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.fixture = ReviewFixture(self.root)

    def test_shadow_requires_separate_allowance_and_forbids_publication_before_dispatch(self):
        for index, args in enumerate((('--shadow', 'arm'), ('--shadow', 'arm', '--shadow-budget-usd', 'nan'),
                                      ('--shadow', 'arm', '--shadow-budget-usd', '1', '--post'),
                                      ('--shadow-budget-usd', '1'), ('--shadow', 'arm', '--read-records'),
                                      ('--shadow', 'arm', '--replies-json', str(self.root / 'contests.json')))):
            result = self.fixture.run(output='denied' + str(index), extra=args)
            self.assertEqual(result.returncode, 2, result.stdout)
            self.assertEqual(self.fixture.calls(), [])

    def test_shadow_allowance_limits_dispatch_and_shared_daily_spend_survives(self):
        normal = self.fixture.run(output='normal')
        self.assertEqual(normal.returncode, 0, normal.stderr)
        before = self.fixture.ledger()
        calls = len(self.fixture.calls())
        result = self.fixture.run(output='shadow', extra=('--shadow', 'budgeted', '--shadow-budget-usd', '.025', '--max-call-cost', '.01'))
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        after = self.fixture.ledger()
        self.assertGreater(len(self.fixture.calls()), calls)
        self.assertLessEqual(len(self.fixture.calls()) - calls, 2)
        self.assertEqual(before['prs'], after['prs'])
        self.assertGreater(sum(after['days'].values()), sum(before['days'].values()))
        self.assertEqual(report['archive']['state'], 'queued', report['archive'])
        records = validate(snapshot(self.root / 'state/thefundamentaltheor3m__SphereCeti/archive/journal'), REPO)
        shadow = next(r for r in records if r['review']['execution_mode'] == 'shadow')
        self.assertEqual(shadow['request']['context'], 'fresh_shadow')
        self.assertEqual(shadow['request']['shadow'], 'budgeted')
        self.assertTrue(all('started_at' in r for r in shadow['runs']))
        self.assertFalse(report['merge_eligible'])

    def test_two_real_fake_provider_shadows_pair_and_live_record_never_does(self):
        from sphereceti.evaluation import executions
        for arm in ('first', 'second'):
            result = self.fixture.run(output=arm, extra=('--shadow', arm, '--shadow-budget-usd', '1', '--max-call-cost', '.01'))
            self.assertEqual(result.returncode, 0, result.stderr)
        files = snapshot(self.root / 'state/thefundamentaltheor3m__SphereCeti/archive/journal')
        groups = executions(files, REPO)
        self.assertEqual(len(groups), 2)
        selected = sorted(groups)
        pair = save_pair(files, REPO, self.root / 'pairs', *selected)
        self.assertEqual(pair['state'], 'paired')
