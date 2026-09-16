"""Archive integrity, numeric facts, publication isolation and real Git concurrency tests."""
import copy
import json
from pathlib import Path
import sqlite3
import tempfile
import unittest
from unittest.mock import patch

from archive_fixture import GitAPI, REPO, enabled
from test_review_records import result
from sphereceti.archive_store import (ArchiveError, SCHEMA, capture, compress, digest, encode, enqueue,
                                     immutable, rebuild, snapshot, validate)
from sphereceti.archive_sync import sync
from sphereceti.review_records import make_record


class ArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.output = self.root / 'output'
        self.output.mkdir()
        self.store = self.root / 'archive'
        self.review_result = result()
        self.review_result.update(execution_id='a'*32, finished_at='2026-09-12T00:00:00+00:00')
        self.review_result['reviews'] = {'correctness': {'summary': 'ghp_abcdefgh12345678 /home/private/name TOKEN_SECRET=abc'}}
        self.record, self.rendered = make_record(self.review_result)
        for name, value in (('result.json', self.review_result), ('record.json', self.record)):
            (self.output / name).write_text(json.dumps(value))
        (self.output / 'record.md').write_text(self.rendered)
        self.run = {'schema': 'tauceti.run/v1', 'repo': REPO, 'pr': 1, 'head_sha': '2'*40,
                    'base_ref_oid': '3'*40, 'merge_base_sha': '3'*40,
                    'run_id': 'r-1', 'provider': 'claude', 'model': 'claude-model', 'rubric': 'correctness',
                    'prompt_policy': 'fresh', 'usage': {'input_tokens': 123, 'output_tokens': 9},
                    'cost_usd': 0.03, 'cost_estimated': False, 'prices_sha': '123456abcdef',
                    'session_id': 'SECRET SESSION', 'summary': 'SECRET SUMMARY', 'stderr': 'SECRET STDERR',
                    'attempts': [{'model': 'claude-model', 'usage': {'input_tokens': 120},
                                  'returncode': 1, 'cost_usd': 0.02, 'parse_error': 'SECRET ERROR',
                                  'session_id': 'SECRET SESSION'}]}
        self.producer = self.output / 'engine-archive/records/runs/1/r-1.json'
        self.producer.parent.mkdir(parents=True)
        self.producer.write_text(json.dumps(self.run))

    def queue(self, text=False):
        return enqueue(self.output, self.store, REPO, include_text=text)

    def files(self):
        return snapshot(self.store / 'outbox')

    def api(self):
        api_root = self.root / 'api'
        api_root.mkdir()
        return GitAPI(api_root)

    def test_capture_preserves_numeric_usage_and_attempts_but_omits_private_text(self):
        self.queue()
        files = self.files()
        self.assertNotIn(b'SECRET', b''.join(files.values()))
        self.assertNotIn(b'ghp_', b''.join(files.values()))
        run = validate(files, REPO)[0]['runs'][0]
        self.assertEqual(run['usage']['input_tokens'], 123)
        self.assertEqual(run['attempts'][0]['usage']['input_tokens'], 120)
        self.assertEqual(run['cost_usd'], 0.03)
        self.assertEqual(run['prices_sha'], '123456abcdef')
        self.assertIsNone(validate(files, REPO)[0]['text_blob'])

    def test_enqueue_is_idempotent_and_keeps_journal(self):
        self.assertEqual(self.queue(), self.queue())
        self.assertEqual(self.files(), snapshot(self.store / 'journal'))
        self.assertEqual(len(self.files()), 1)

    def test_opt_in_text_is_redacted_and_cannot_double_count_execution(self):
        self.queue()
        self.queue(True)
        files = self.files()
        self.assertEqual(len(files), 3)
        record = next(r for r in validate(files, REPO) if r['text_blob'])
        import gzip
        plain = gzip.decompress(files[f"blobs/{record['text_blob'][:2]}/{record['text_blob']}.gz"])
        self.assertNotIn(b'ghp_', plain)
        self.assertNotIn(b'/home/private', plain)
        self.assertNotIn(b'TOKEN_SECRET=abc', plain)
        self.assertIn(b'[REDACTED]', plain)
        database = self.root / 'derived.sqlite'
        rebuild(files, REPO, database)
        with sqlite3.connect(database) as db:
            self.assertEqual(db.execute('SELECT COUNT(*) FROM records').fetchone()[0], 2)
            self.assertEqual(db.execute('SELECT COUNT(*) FROM executions').fetchone()[0], 1)
            self.assertEqual(db.execute('SELECT SUM(cost_usd) FROM runs').fetchone()[0], .03)

    def test_missing_usage_stays_unknown_and_no_inference_is_fabricated(self):
        del self.run['usage']
        del self.run['cost_usd']
        self.producer.write_text(json.dumps(self.run))
        self.queue()
        rebuild(self.files(), REPO, self.root / 'db')
        with sqlite3.connect(self.root / 'db') as db:
            self.assertEqual(db.execute('SELECT usage_json,cost_usd FROM runs').fetchone(), ('null', None))

    def test_producer_source_binding_and_numeric_facts_fail_closed(self):
        for key, value in [('head_sha', 'f'*40), ('pr', 2), ('usage', {'input_tokens': True}),
                           ('usage', {'input_tokens': -1}), ('cost_usd', float('nan'))]:
            with self.subTest(key=key, value=value):
                run = {**self.run, key: value}
                self.producer.write_text(json.dumps(run))
                with self.assertRaises(ValueError):
                    self.queue()
        self.assertFalse((self.store / 'outbox').exists())

    def test_record_prose_tampering_and_duplicate_json_rejected(self):
        (self.output / 'record.md').write_text(self.rendered + 'tampered')
        with self.assertRaises(ValueError):
            self.queue()
        (self.output / 'record.md').write_text(self.rendered)
        self.producer.write_text('{"schema":"tauceti.run/v1","schema":"other"}')
        with self.assertRaises(ValueError):
            self.queue()

    def test_archive_capture_failure_does_not_change_review_publication(self):
        before = (self.output / 'result.json').read_bytes()
        with patch('sphereceti.archive_store.immutable', side_effect=OSError('disk full')):
            self.assertEqual(capture(self.output, self.store, REPO)['state'], 'error')
        self.assertEqual((self.output / 'result.json').read_bytes(), before)
        self.queue()  # Recover from original output.

    def test_immutable_collision_and_symlink_are_rejected(self):
        path = self.root / 'immutable'
        immutable(path, b'one')
        with self.assertRaises(ArchiveError):
            immutable(path, b'two')
        (self.root / 'link').symlink_to(path)
        with self.assertRaises(ArchiveError):
            immutable(self.root / 'link', b'one')
        self.producer.unlink()
        self.producer.symlink_to(path)
        with self.assertRaises(ArchiveError):
            self.queue()

    def test_unknown_paths_digests_and_missing_blobs_rejected(self):
        self.queue(True)
        files = self.files()
        for mutated in ({**files, 'code.py': b'print(1)'},
                        {n: b for n, b in files.items() if n.startswith('records/')},
                        {n: b + b'changed' for n, b in files.items()},
                        {**files, 'derived.sqlite': b'SQLite'}):
            with self.assertRaises(ValueError):
                validate(mutated, REPO)
        with self.assertRaises(ValueError):
            validate(files, 'wrong/repo')

    def test_gzip_bomb_rejected_before_database_output(self):
        self.queue(True)
        files = self.files()
        name = next(n for n in files if n.startswith('blobs/'))
        files[name] = compress(b'x' * (1024*1024+1))
        with self.assertRaises(ValueError):
            rebuild(files, REPO, self.root / 'database')
        self.assertFalse((self.root / 'database').exists())

    def test_execution_conflicts_do_not_silently_change_cost(self):
        self.queue()
        files = self.files()
        record = copy.deepcopy(validate(files, REPO)[0])
        record['runs'][0]['cost_usd'] = 999
        body = encode(record)
        files[f'records/{digest(body)}.json'] = body
        with self.assertRaises(ArchiveError):
            validate(files, REPO)

    def test_sync_confirms_real_git_objects_and_keeps_local_journal(self):
        self.queue()
        original = self.files()
        with enabled():
            api = self.api()
            outcome = sync(self.store, REPO, api.transport)
            self.assertEqual(outcome['state'], 'confirmed')
            self.assertEqual(self.files(), {})
            _, remote = api.transport.fetch()
            self.assertTrue(all(remote[n] == b for n, b in original.items()))
            self.assertEqual(snapshot(self.store / 'journal'), original)
            calls = len(api.calls)
            self.assertEqual(sync(self.store, REPO, api.transport)['state'], 'empty')
            self.assertEqual(len(api.calls), calls)
            self.queue()
            writes = sum(p is not None for _, p, _ in api.calls)
            sync(self.store, REPO, api.transport)
            self.assertEqual(sum(p is not None for _, p, _ in api.calls), writes)

    def test_upload_outage_retains_every_outbox_file(self):
        self.queue()
        original = self.files()
        with enabled():
            api = self.api()
            api.outage = True
            with self.assertRaises(ArchiveError):
                sync(self.store, REPO, api.transport)
        self.assertEqual(self.files(), original)

    def test_uncertain_success_adopts_readback_without_second_ref_write(self):
        self.queue()
        with enabled():
            api = self.api()
            def timeout():
                raise ArchiveError('lost response')
            api.after_update = timeout
            self.assertEqual(sync(self.store, REPO, api.transport)['state'], 'confirmed')
            self.assertEqual(sum(m == 'PATCH' for _, _, m in api.calls), 1)

    def test_concurrent_branch_advance_retries_and_preserves_both_writers(self):
        self.queue()
        other = copy.deepcopy(validate(self.files(), REPO)[0])
        other['execution_id'] = 'b'*32
        body = encode(other)
        name = f'records/{digest(body)}.json'
        with enabled():
            api = self.api()
            def race():
                api.before_update = None
                parent = api.git('rev-parse', 'refs/heads/review-data').decode().strip()
                api.commit_branch('review-data', {name: body}, parent)
            api.before_update = race
            self.assertEqual(sync(self.store, REPO, api.transport)['attempts'], 2)
            self.assertEqual(len(validate(api.transport.fetch()[1], REPO, anchored=True)), 2)

    def test_concurrently_queued_new_files_are_not_drained(self):
        self.queue()
        other = copy.deepcopy(validate(self.files(), REPO)[0])
        other['execution_id'] = 'c'*32
        body = encode(other)
        name = f'records/{digest(body)}.json'
        with enabled():
            api = self.api()
            api.before_update = lambda: immutable(self.store / 'outbox' / name, body)
            sync(self.store, REPO, api.transport)
        self.assertEqual(self.files(), {name: body})

    def test_concurrent_record_reusing_a_blob_keeps_that_blob_pending(self):
        self.queue(True)
        original = self.files()
        other = copy.deepcopy(validate(original, REPO)[0])
        other['execution_id'] = 'd'*32
        body = encode(other)
        name = f'records/{digest(body)}.json'
        class Transport:
            def __init__(inner):
                inner.remote = {'ARCHIVE.json': encode({'schema': SCHEMA, 'repository': REPO, 'branch': 'review-data'})}
            def fetch(inner):
                return 'a'*40, inner.remote
            def append(inner, parent, additions):
                inner.remote.update(additions)
                immutable(self.store / 'outbox' / name, body)
        sync(self.store, REPO, Transport())
        remaining = self.files()
        self.assertIn(name, remaining)
        self.assertEqual(len(remaining), 2)
        validate(remaining, REPO)

    def test_remote_collision_or_source_code_never_gets_overwritten(self):
        self.queue()
        name = next(iter(self.files()))
        with enabled():
            api = self.api()
            parent = api.git('rev-parse', 'refs/heads/review-data').decode().strip()
            api.commit_branch('review-data', {name: b'wrong'}, parent)
            with self.assertRaises(ArchiveError):
                sync(self.store, REPO, api.transport)
            self.assertFalse(any(p is not None for _, p, _ in api.calls))
        self.assertEqual(len(self.files()), 1)

    def test_missing_state_branch_is_not_automatically_created(self):
        self.queue()
        with enabled():
            api = self.api()
            api.git('update-ref', '-d', 'refs/heads/review-data')
            with self.assertRaises(ArchiveError):
                sync(self.store, REPO, api.transport)
            self.assertFalse(any(p is not None for _, p, _ in api.calls))

    def test_policy_revocation_before_ref_update_leaves_outbox(self):
        self.queue()
        with enabled():
            api = self.api()
            original = api.transport.authorize
            checks = 0
            def revoke():
                nonlocal checks
                checks += 1
                if checks >= 2:
                    raise ArchiveError('revoked')
                original()
            api.transport.authorize = revoke
            with self.assertRaises(ArchiveError):
                sync(self.store, REPO, api.transport)
            self.assertFalse(any(m == 'PATCH' for _, _, m in api.calls))
        self.assertEqual(len(self.files()), 1)

    def test_mismatched_installed_main_and_text_policy_deny_writes(self):
        self.queue(True)
        with enabled():
            api = self.api()
            with self.assertRaises(ArchiveError):
                sync(self.store, REPO, api.transport)
            self.assertFalse(any(p is not None for _, p, _ in api.calls))
            parent = api.git('rev-parse', 'refs/heads/main').decode().strip()
            api.commit_branch('main', {'tools/project/sphereceti/archive_sync.py': b'changed'}, parent)
            with self.assertRaises(ArchiveError):
                api.transport.authorize()

    def test_truncated_api_inventory_and_symlink_mode_are_rejected(self):
        with enabled():
            api = self.api()
            original = api.transport.call
            def truncated(endpoint, **kwargs):
                value = original(endpoint, **kwargs)
                if '/trees/' in endpoint:
                    value['truncated'] = True
                return value
            api.transport.call = truncated
            with self.assertRaises(ArchiveError):
                api.transport.fetch()
            with self.assertRaises(ArchiveError):
                api.transport.blob({'type': 'blob', 'mode': '120000', 'size': 0, 'sha': 'a'*40})

    def test_explicitly_approved_text_upload_uses_same_data_only_protocol(self):
        self.queue(True)
        with enabled(text=True):
            api = self.api()
            self.assertEqual(sync(self.store, REPO, api.transport)['state'], 'confirmed')
            records = validate(api.transport.fetch()[1], REPO, anchored=True)
            self.assertIsNotNone(records[0]['text_blob'])

    def test_failed_updates_stop_after_three_attempts_and_keep_outbox(self):
        self.queue()
        with enabled():
            api = self.api()
            def fail():
                raise ArchiveError('update rejected')
            api.before_update = fail
            with self.assertRaises(ArchiveError):
                sync(self.store, REPO, api.transport)
            self.assertEqual(sum(m == 'PATCH' for _, _, m in api.calls), 3)
        self.assertEqual(len(self.files()), 1)

    def test_failed_readback_keeps_outbox_even_after_actual_remote_success(self):
        self.queue()
        with enabled():
            api = self.api()
            api.after_update = lambda: setattr(api, 'outage', True)
            with self.assertRaises(ArchiveError):
                sync(self.store, REPO, api.transport)
            self.assertEqual(len(self.files()), 1)
            api.outage = False
            api.after_update = None
            writes = sum(m == 'PATCH' for _, _, m in api.calls)
            self.assertEqual(sync(self.store, REPO, api.transport)['state'], 'confirmed')
            self.assertEqual(sum(m == 'PATCH' for _, _, m in api.calls), writes)

    def test_wrong_branch_anchor_is_not_repaired_by_the_publisher(self):
        self.queue()
        with enabled():
            api = self.api()
            parent = api.git('rev-parse', 'refs/heads/review-data').decode().strip()
            api.commit_branch('review-data', {'ARCHIVE.json': b'{}'}, parent)
            with self.assertRaises(ArchiveError):
                sync(self.store, REPO, api.transport)
            self.assertFalse(any(p is not None for _, p, _ in api.calls))

    def test_rebuild_refuses_existing_database_and_unreferenced_blob(self):
        self.queue()
        output = self.root / 'existing'
        output.write_bytes(b'preserve')
        with self.assertRaises(ArchiveError):
            rebuild(self.files(), REPO, output)
        self.assertEqual(output.read_bytes(), b'preserve')
        files = self.files()
        key = digest(b'orphan')
        files[f'blobs/{key[:2]}/{key}.gz'] = compress(b'orphan')
        with self.assertRaises(ArchiveError):
            validate(files, REPO)


class ArchiveCLITests(unittest.TestCase):
    def test_fake_provider_completion_queues_numeric_runs_and_disabled_sync_makes_no_call(self):
        from archive_fixture import installed_archive_smoke
        from review_fixture import ReviewFixture
        import subprocess
        import sys
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture = ReviewFixture(root)
            process = fixture.run()
            self.assertEqual(process.returncode, 0, process.stderr)
            report = json.loads(process.stdout)
            self.assertEqual(report['archive']['state'], 'queued', report.get('archive'))
            self.assertEqual(report['archive']['runs'], 10)
            store = root / 'state/thefundamentaltheor3m__SphereCeti/archive'
            record = validate(snapshot(store / 'outbox'), REPO)[0]
            self.assertEqual(len(record['runs']), 10)
            self.assertTrue(all(r['usage']['input_tokens'] == 100 for r in record['runs']))
            launcher = fixture.bin / 'sphereceti'
            launcher.write_text(f'#!{sys.executable}\nimport sys\nsys.path.insert(0, {str(Path(__file__).resolve().parents[1] / "tools/project")!r})\nfrom sphereceti.cli import main\nsys.exit(main())\n')
            launcher.chmod(0o755)
            gh = fixture.bin / 'gh'
            gh.write_text('#!/bin/sh\necho invoked > ' + str(root / 'unexpected-gh') + '\nexit 1\n')
            gh.chmod(0o755)
            installed_archive_smoke(launcher, fixture)
            self.assertFalse((root / 'unexpected-gh').exists())
            denied = subprocess.run([str(launcher), 'archive', 'rebuild', '--operator-config', str(fixture.operator),
                                     '--output', str(store / 'journal/database.sqlite')],
                                    env=fixture.env, cwd=fixture.foreign, capture_output=True, text=True)
            self.assertEqual(denied.returncode, 2)
            self.assertFalse((store / 'journal/database.sqlite').exists())
