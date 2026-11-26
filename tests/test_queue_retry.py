# SPDX-License-Identifier: Apache-2.0
"""A PR merging while the queue is read is routine: the survey reads it again, then gives up."""
import io
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.bulk import CHANGED, QueueChanged
from sphereceti.feedback import Progress, current, install
from sphereceti.worker import WorkerError
from sphereceti.worker_cli import survey
from test_fast_queue import PROJECT, SurveyReader, world


class Shifting(SurveyReader):
    """The queue's count moves between the first and second page of the first `changes` reads."""

    def __init__(self, hub, changes, **kwargs):
        super().__init__(hub, bulk=True, page=4, **kwargs)
        self.changes, self.pages = changes, 0

    def read(self, args, limit=None):
        value = super().read(args, limit)
        if args[:2] == ['api', 'graphql']:
            self.pages += 1
            if self.changes and self.pages % 2 == 0:  # the second page of a pass: a PR merged meanwhile
                self.changes -= 1
                value['data']['repository']['pullRequests']['totalCount'] += 1
        return value


class QueueRetryTest(unittest.TestCase):
    def setUp(self):
        self.stream = io.StringIO()
        previous = current()
        install(Progress(self.stream, tty=False))
        self.addCleanup(install, previous)

    def test_one_change_mid_survey_reads_again_and_succeeds(self):
        reader = Shifting(world(), changes=1)
        with patch('time.sleep') as sleep:
            result = survey(PROJECT, None, api=reader)
        self.assertEqual(len(result['pull_requests']), 10)
        sleep.assert_called_once_with(5)
        self.assertIn('queue changed during the survey (a PR merged or moved); re-reading…', self.stream.getvalue())

    def test_a_queue_that_keeps_changing_stops_after_three_retries_with_the_old_message(self):
        reader = Shifting(world(), changes=99)
        with patch('time.sleep') as sleep, self.assertRaises(QueueChanged) as raised:
            survey(PROJECT, None, api=reader)
        self.assertEqual(str(raised.exception), CHANGED)
        self.assertEqual([c.args[0] for c in sleep.call_args_list], [5, 15, 30])
        self.assertTrue(isinstance(raised.exception, WorkerError))  # batches still report a lookup failure

    def test_other_failures_stop_at_once(self):
        reader = SurveyReader(world(), bulk=True)
        reader.read = lambda args, limit=None: {'errors': [{'message': 'Bad credentials'}]}
        with patch('time.sleep') as sleep, self.assertRaises(WorkerError) as raised:
            survey(PROJECT, None, api=reader)
        self.assertNotIsInstance(raised.exception, QueueChanged)
        sleep.assert_not_called()

    def test_a_batch_survives_a_merge_during_its_survey(self):
        from sphereceti.config import OperatorPreferences
        from sphereceti.review_queue import queue
        from test_fast_queue import POLICY, RestClient
        import tempfile
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-retry-')
        self.addCleanup(temp.cleanup)
        prefs = OperatorPreferences(storage=temp.name)
        steady = queue(PROJECT, POLICY, prefs, api=Shifting(world(), changes=0), client=RestClient(world()),
                       use_cache=False)
        hub = world()
        with patch('time.sleep'):
            report = queue(PROJECT, POLICY, prefs, api=Shifting(hub, changes=2), client=RestClient(hub),
                           use_cache=False)
        for value in (steady, report):
            value.pop('observed_at')
            for section in value['sections'].values():
                for item in section:
                    item.pop('waiting_seconds', None)
        self.assertEqual(report, steady)


if __name__ == '__main__':
    unittest.main()
