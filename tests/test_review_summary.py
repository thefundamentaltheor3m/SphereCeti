# SPDX-License-Identifier: Apache-2.0
"""The terminal's answer to "what will happen?" and "what happened, and what next?"."""
from argparse import Namespace
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.config import OperatorPreferences
from sphereceti.local_review import RUBRICS
from sphereceti.review_summary import announcing, engine_defaults, plan, summarize

REPO = 'thefundamentaltheor3m/SphereCeti'
HEAD, BASE = '8cdec1b' + 'a' * 33, '5db3655' + 'b' * 33


def arguments(**updates):
    values = dict(provider=None, codex_model=None, claude_model=None, kiro_model=None, dry_run=False,
                  post=True, no_post=False, post_default=True)
    values.update(updates)
    return Namespace(**values)


class PlanTest(unittest.TestCase):
    def report(self):
        return {'pr': 54, 'head': HEAD, 'base': BASE}

    def test_line_names_pr_revisions_effective_model_and_posting(self):
        defaults = engine_defaults()
        codex = OperatorPreferences(provider='codex', budget_usd=5)
        self.assertEqual(plan(arguments(), codex, self.report())['line'],
                         f"Review #54: head 8cdec1b, base 5db3655 · codex {defaults['CODEX_MODEL']} "
                         f"(falls back to {defaults['CODEX_FALLBACK_MODEL']}) · will post")
        pinned = plan(arguments(codex_model='gpt-6.1-sol', post=False, no_post=True), codex, self.report())
        self.assertTrue(pinned['line'].endswith('· codex gpt-6.1-sol · will not post (--no-post)'))
        claude = plan(arguments(provider='claude', dry_run=True, post=False), codex, self.report())
        self.assertTrue(claude['line'].endswith(f"· claude {defaults['CLAUDE_MODEL']} · "
                                                'dry run: no model call, nothing posted'))
        degraded = plan(arguments(post=False), codex, self.report())
        self.assertTrue(degraded['line'].endswith('· will not post (approved policy disables posting)'))

    def test_codex_model_comes_from_the_arguments_the_review_passes_to_the_engine(self):
        # The plan reads args.codex_model, the same value run_review forwards as --codex-model, and
        # otherwise the engine's own default. A CLI default (gpt-6.2-sol) shows through, with the
        # reasoning effort that every Codex call now passes explicitly.
        import argparse
        from sphereceti.local_review import add_parser
        parser = argparse.ArgumentParser()
        add_parser(parser.add_subparsers(dest='command'))
        args = parser.parse_args(['review', '54'])
        args.post_default = True
        codex = OperatorPreferences(provider='codex', budget_usd=5)
        expected = args.codex_model or engine_defaults()['CODEX_MODEL']
        self.assertIn(f'· codex {expected} (medium) ·', plan(args, codex, self.report())['line'])
        self.assertEqual(expected, 'gpt-6.2-sol')
        self.assertEqual(plan(args, codex, self.report())['codex_effort'], 'medium')
        args = parser.parse_args(['review', '54', '--codex-effort', 'xhigh'])
        args.post_default = True
        self.assertIn('· codex gpt-6.2-sol (xhigh) ·', plan(args, codex, self.report())['line'])
        sub = parser._subparsers._group_actions[0].choices['review']
        sub.set_defaults(codex_model='gpt-6.1-sol')
        args = parser.parse_args(['review', '54'])
        self.assertIn('· codex gpt-6.1-sol (medium) ·', plan(args, codex, self.report())['line'])

    def test_guard_announces_before_the_provider_and_keeps_the_inner_guard(self):
        from contextlib import contextmanager
        events, sink = [], {}

        @contextmanager
        def inner(args, report, policy, client):
            events.append('inner')
            yield None
        guard = announcing(OperatorPreferences(provider='codex'), events.append, sink, inner=inner)
        with guard(arguments(), self.report(), None, None):
            events.append('provider')
        self.assertEqual(events[0], 'inner')
        self.assertTrue(events[1].startswith('Review #54: head 8cdec1b'))
        self.assertEqual(events[2], 'provider')
        self.assertEqual(sink['providers'], ['codex'])


class SummaryTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-summary-')
        self.addCleanup(temp.cleanup)
        self.output = Path(temp.name) / 'runs' / 'run-1234'

    def report(self, verdicts=None, *, completion='complete', posted='official', stop=None, runs=(), **evidence):
        verdicts = {r: 'approve' for r in RUBRICS} | (verdicts or {})
        publication = ({'state': 'confirmed', 'comment_id': 77, 'authorized': posted == 'official'}
                       if posted in ('official', 'advisory') else
                       {'state': 'unconfirmed', 'reason': 'timeout'} if posted == 'interrupted' else None)
        root = self.output / 'engine-archive/records/runs/54'
        root.mkdir(parents=True, exist_ok=True)
        for i, run in enumerate(runs):
            (root / f'{i}.json').write_text(json.dumps({'head_sha': HEAD, **run}))
        return {'repository': REPO, 'pr': 54, 'head': HEAD, 'output': str(self.output), 'completion': completion,
                'requested_rubrics': list(RUBRICS), 'verdicts': verdicts, 'stop_reason': stop,
                'engine_exit_code': 0, **({'publication': publication} if publication else {}),
                'execution_mode': 'commit', 'tooling_approved': True, 'installed_tooling_matches_T': True,
                'missing_context': [], 'config_differences': [], **evidence}

    def summary(self, report, **updates):
        return summarize(arguments(provider='codex', **updates), report,
                         posting='Not posted: posting is disabled by approved repository policy.')

    def test_all_green_official_and_advisory(self):
        url = f'https://github.com/{REPO}/pull/54#issuecomment-77'
        result = self.summary(self.report())
        self.assertEqual(result['line'], f'10/10 approve · posted {url} · official')
        self.assertEqual(result['next_action'], 'none: every rubric approves')
        self.assertEqual((result['reviewed'], result['total'], result['first_blocking'], result['stop']),
                         (10, 10, None, None))
        self.assertTrue(self.summary(self.report(posted='advisory'))['line'].endswith(
            '· advisory (not an authorized reviewer)'))

    def test_an_advisory_record_by_an_authorized_reviewer_is_never_called_official(self):
        # #113, comment 7176701797: installed at e676d23 while approved main was 4939635. The
        # publisher is authorized, but the record itself says advisory: true.
        url = f'https://github.com/{REPO}/pull/54#issuecomment-77'
        report = self.report(installed_tooling_matches_T=False)
        from sphereceti.review_records import is_advisory
        self.assertTrue(is_advisory(report))
        result = self.summary(report)
        self.assertEqual(result['line'], f'10/10 approve · posted {url} · advisory (installed tooling is not '
                                         'approved main; reinstall)')
        self.assertEqual((result['official'], result['advisory_reasons']),
                         (False, ['installed tooling is not approved main; reinstall']))
        official = self.summary(self.report())
        self.assertEqual((official['official'], official['advisory_reasons']), (True, []))
        self.assertTrue(official['line'].endswith('· official'))

    def test_stopped_early_on_a_blocking_rubric(self):
        absent = {r: 'absent' for r in RUBRICS[4:]}
        result = self.summary(self.report({'attribution': 'block', **absent}, completion='partial',
                                          posted='advisory'))
        self.assertEqual(result['line'], f'4/10 reviewed · stopped: blocked on attribution · posted '
                         f'https://github.com/{REPO}/pull/54#issuecomment-77 · advisory (partial; not an '
                         'authorized reviewer)')
        self.assertEqual(result['first_blocking'], 'attribution')
        self.assertEqual(result['next_action'], 'author: address attribution (see record); rerun after the head changes')

    def test_changes_requested_on_a_complete_review(self):
        result = self.summary(self.report({'naming': 'request_changes'}))
        self.assertTrue(result['line'].startswith('10/10 reviewed · changes requested: naming · posted '))
        self.assertEqual(result['next_action'], 'author: address naming (see record); rerun after the head changes')

    def test_a_block_and_requested_changes_are_all_named_on_the_line_and_in_the_next_action(self):
        # Run 598e04f8 (#75 at 79f2f36, posted, official): scope blocked, and api-design and
        # documentation requested changes. The line used to list only the requested changes, while
        # the next action named only the first finding (the block): "address scope".
        url = f'https://github.com/{REPO}/pull/54#issuecomment-77'
        result = self.summary(self.report({'scope': 'block', 'api-design': 'request_changes',
                                           'documentation': 'request_changes'}))
        self.assertEqual(result['line'], f'10/10 reviewed · blocked: scope · changes requested: api-design, '
                                         f'documentation · posted {url} · official')
        self.assertEqual(result['next_action'], 'author: address scope, api-design, documentation (see record); '
                                                'rerun after the head changes')
        self.assertEqual(result['findings'], ['scope', 'api-design', 'documentation'])
        self.assertEqual(result['first_blocking'], 'scope')
        # Requested changes alone, several of them: every one is named, in rubric order.
        result = self.summary(self.report({'documentation': 'request_changes', 'api-design': 'request_changes'}))
        self.assertTrue(result['line'].startswith('10/10 reviewed · changes requested: api-design, documentation · '))
        self.assertEqual(result['next_action'], 'author: address api-design, documentation (see record); '
                                                'rerun after the head changes')

    def test_stop_reason_from_the_receipt(self):
        absent = {r: 'absent' for r in RUBRICS[3:]}
        result = self.summary(self.report(absent, completion='partial', posted=None, stop='usage_unknown'))
        self.assertEqual(result['line'], '3/10 reviewed · stopped: usage unknown · not posted: '
                                         'posting is disabled by approved repository policy')
        self.assertEqual(result['next_action'], "check the provider's usage for the unreported attempt, then rerun")

    def test_provider_startup_failure_points_to_the_sandbox_check(self):
        failed = {'verdict': 'error', 'tool_trace': None, 'attempts': [{'error_kind': 'unknown_error'}]}
        report = self.report({r: 'error' for r in RUBRICS}, completion='error', posted=None, runs=[failed, failed])
        result = self.summary(report)
        self.assertEqual(result['line'], '0/10 reviewed · stopped: provider failed to start · not posted: '
                                         'posting is disabled by approved repository policy')
        self.assertEqual(result['next_action'], 'run `sphereceti review-check-sandbox --compare-path --compare-tmpdir`')
        # A model that read files before failing is not a startup failure.
        traced = dict(failed, tool_trace=[{'tool': 'Read', 'path': 'code/README.md'}])
        report = self.report({r: 'error' for r in RUBRICS}, completion='error', posted=None, runs=[traced])
        self.assertNotIn('sandbox', self.summary(report)['next_action'])

    def test_provider_down_names_the_cause(self):
        down = {'verdict': 'error', 'attempts': [{'error_kind': 'not_authenticated'}]}
        report = self.report({r: 'absent' for r in RUBRICS}, completion='error', posted=None, runs=[down])
        result = self.summary(report)
        self.assertIn('stopped: provider unavailable (not authenticated)', result['line'])
        self.assertEqual(result['next_action'], 'sign in to codex again (e.g. `codex login`), then rerun')

    def test_interrupted_publication_names_the_recovery_command(self):
        result = self.summary(self.report(posted='interrupted'))
        self.assertIn('publication interrupted', result['line'])
        self.assertEqual(result['next_action'], 'publication was interrupted; run `sphereceti review-publish run-1234`')
        # A run saved with --output outside the store is named by its directory, as #82 accepts.
        elsewhere = dict(self.report(posted='interrupted'), output='/tmp/my-review')
        self.assertEqual(self.summary(elsewhere)['next_action'],
                         'publication was interrupted; run `sphereceti review-publish /tmp/my-review`')

    def test_dry_run_and_no_post(self):
        dry_report = {k: v for k, v in self.report(completion='dry_run', posted=None).items()
                      if k not in ('verdicts', 'requested_rubrics', 'stop_reason', 'engine_exit_code')}
        dry = self.summary(dry_report, dry_run=True)
        self.assertEqual((dry['line'], dry['next_action']), ('dry run · not posted: dry run',
                                                              'run again without --dry-run to review'))
        local = summarize(arguments(provider='codex', post=False, no_post=True), self.report(posted=None),
                          posting='Not posted: --no-post.')
        self.assertEqual(local['line'], '10/10 approve · not posted: --no-post')
        self.assertEqual(local['next_action'], 'rerun without --no-post to publish the record')


if __name__ == '__main__':
    unittest.main()
