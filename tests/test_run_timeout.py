# SPDX-License-Identifier: Apache-2.0
"""--run-timeout / SPHERECETI_RUN_TIMEOUT: the whole-run deadline, its bounds, the claim TTL and the receipt."""
from argparse import Namespace
from datetime import datetime, timedelta
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.config import OperatorPreferences
from sphereceti.local_review import RUN_TIMEOUT, ReviewError, run_timeout
from sphereceti.review_claims import MARKER, live, run_claimed
from review_fixture import ReviewFixture
from test_review_claims import BASE, HEAD, POLICY, PROJECT, REPO, FakeGitHub, FakeReview, arguments, claim_comment


def stamp(value):
    return datetime.fromisoformat(value.replace('Z', '+00:00'))


class RunTimeoutTest(unittest.TestCase):
    def test_flag_then_environment_then_default_within_bounds(self):
        with patch.dict(os.environ, {}, clear=False):
            os.environ.pop('SPHERECETI_RUN_TIMEOUT', None)
            self.assertEqual(run_timeout(Namespace()), RUN_TIMEOUT)
            self.assertEqual(run_timeout(Namespace(run_timeout=None)), 1800)
            self.assertEqual(run_timeout(Namespace(run_timeout=3600)), 3600)
            os.environ['SPHERECETI_RUN_TIMEOUT'] = ' 5400 '
            self.assertEqual(run_timeout(Namespace(run_timeout=None)), 5400)
            self.assertEqual(run_timeout(Namespace(run_timeout=600)), 600)  # the flag wins
            for value in (59, 7201, 0, -5):
                with self.subTest(flag=value), self.assertRaisesRegex(ReviewError, r'--run-timeout must be whole '
                                                                                    r'seconds from 60 to 7200'):
                    run_timeout(Namespace(run_timeout=value))
            for text in ('59', '7201', 'thirty', '1800.5'):
                os.environ['SPHERECETI_RUN_TIMEOUT'] = text
                with self.subTest(env=text), self.assertRaisesRegex(ReviewError, r'SPHERECETI_RUN_TIMEOUT must be '
                                                                                  r'whole seconds from 60 to 7200'):
                    run_timeout(Namespace(run_timeout=None))
            self.assertEqual(run_timeout(Namespace(run_timeout=60)), 60)
            self.assertEqual(run_timeout(Namespace(run_timeout=7200)), 7200)

    def test_the_claim_lasts_as_long_as_the_run_may(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-run-timeout-')
        self.addCleanup(temp.cleanup)
        prefs = OperatorPreferences(budget_usd=5, storage=temp.name)
        for flag, expected in ((None, RUN_TIMEOUT), (5400, 5400)):
            with self.subTest(flag=flag):
                hub, seen = FakeGitHub(), []

                class Watch(FakeReview):
                    def __call__(inner, args, project, prefs, guard):
                        report = {'repository': REPO, 'pr': 1, 'head': HEAD, 'base': BASE}
                        with guard(args, report, POLICY, inner.client):
                            seen.extend(c['body'] for c in hub.store.get(1, []))
                        return {**report, 'completion': 'complete',
                                'publication': {'state': 'confirmed', 'comment_id': 555}}
                with patch.dict(os.environ, {'SPHERECETI_RUN_TIMEOUT': ''}):
                    run_claimed(arguments(provider='codex', run_timeout=flag), PROJECT, prefs, run=Watch(hub.client(7)))
                [body] = seen
                data = json.loads(body[len(MARKER):body.index('-->')])
                self.assertEqual((stamp(data['expires_at']) - stamp(data['started_at'])).total_seconds(), expected)

    def test_liveness_admits_the_longest_allowed_claim_and_nothing_longer(self):
        now = datetime.fromisoformat('2026-11-26T12:00:00+00:00')
        with patch('test_review_claims.utcnow', return_value=now - timedelta(minutes=1)):
            long = claim_comment(11, ttl=7200)
            too_long = claim_comment(12, ttl=7200 + 61 + 60)
        claims = live([long, too_long], {'repository': REPO, 'pr': 1, 'head': HEAD}, now)
        self.assertEqual([c['comment_id'] for c in claims], [11])


class RunTimeoutCliTest(unittest.TestCase):
    def test_the_receipt_records_the_timeout_and_bad_values_stop_before_any_work(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-run-timeout-cli-')
        self.addCleanup(temp.cleanup)
        fixture = ReviewFixture(Path(temp.name))
        flagged = fixture.run(output='flagged', extra=('--run-timeout', '900'))
        self.assertEqual(flagged.returncode, 0, flagged.stderr)
        self.assertEqual(json.loads((Path(temp.name) / 'flagged/result.json').read_text())['run_timeout_s'], 900)
        fixture.env['SPHERECETI_RUN_TIMEOUT'] = '2400'
        env = fixture.run(output='env')
        self.assertEqual(env.returncode, 0, env.stderr)
        self.assertEqual(json.loads((Path(temp.name) / 'env/result.json').read_text())['run_timeout_s'], 2400)
        calls = len(fixture.calls())
        bad = fixture.run(output='bad', extra=('--run-timeout', '30'))
        self.assertEqual(bad.returncode, 2)
        self.assertIn('--run-timeout must be whole seconds from 60 to 7200', bad.stderr)
        self.assertEqual(len(fixture.calls()), calls)  # no model call
        self.assertFalse((Path(temp.name) / 'bad').exists())


if __name__ == '__main__':
    unittest.main()
