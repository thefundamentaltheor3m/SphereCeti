"""Adversarial record, identity, supersession, contest, and publication tests; no external calls."""
import base64
from copy import deepcopy
from dataclasses import replace
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools/project'))
from sphereceti.config import parse_policy, resource_text
from sphereceti.local_review import RUBRICS
from sphereceti.review_records import (BINDINGS, CONTEST, FIELDS, MARKER, SIZE_LIMIT, RecordError,
                                      assess_records, canonical, identity, make_record, parse_record, sha)
from sphereceti.review_post import GitHub, publish

REPO = 'thefundamentaltheor3m/SphereCeti'


def result():
    r = {k: 'a' * 64 for k in BINDINGS}
    r.update(repository=REPO, pr=1, tooling='1'*40, head='2'*40, base='3'*40, diff_base='3'*40,
             completion='complete', execution_mode='commit', tooling_approved=True,
             installed_tooling_matches_T=True, missing_context=[], config_differences=[],
             verdicts={r:'approve' for r in RUBRICS}, reviews={})
    return r


def comment(r=None, *, number=10, actor=7):
    record, body = make_record(r or result())
    stamp = '2026-09-11T00:00:00Z'
    return {'id':number, 'body':body, 'user':{'type':'User','id':actor,'login':'irrelevant'},
            'created_at':stamp, 'updated_at':stamp,
            'issue_url':f'https://api.github.com/repos/{REPO}/issues/1'}, record


class ReviewRecordTests(unittest.TestCase):
    def setUp(self):
        self.context = result()
        self.policy = replace(parse_policy(resource_text('automation.toml')), posting=True,
                              authorized_reviewers=('user:7','user:8','app:17'))

    def assess(self, comments, **kwargs):
        return assess_records(comments, kwargs.get('context',self.context), kwargs.get('policy',self.policy),
                              kwargs.get('approved',lambda rev:rev=='1'*40), 99)

    def test_complete_authorized_record_is_review_evidence_but_never_merge_permission(self):
        c, r = comment()
        self.assertEqual(parse_record(c['body']),r)
        outcome=self.assess([c])
        self.assertTrue(outcome['review_safe'],outcome)
        self.assertFalse(outcome['merge_eligible'])

    def test_body_identity_and_bot_names_cannot_forge_api_identity(self):
        c,_=comment(actor=900)
        c['user']['login']='approved-reviewer[bot]'
        c['performed_via_github_app']={'id':17}
        self.assertEqual(identity(c),'user:900')
        self.assertFalse(self.assess([c])['review_safe'])

    def test_designated_app_requires_api_bot_and_app_id(self):
        c,_=comment(actor=900)
        c['user']['type']='Bot'
        self.assertFalse(self.assess([c])['review_safe'])
        c['performed_via_github_app']={'id':17}
        self.assertTrue(self.assess([c])['review_safe'])
        c['performed_via_github_app']['id']=18
        self.assertFalse(self.assess([c])['review_safe'])

    def test_rendered_body_and_machine_record_are_bound(self):
        c,_=comment()
        for body in (c['body']+'tampered', c['body']+c['body'], c['body'].replace('v1 ','v2 ',1), 'prefix'+c['body']):
            with self.subTest(body=body[:40]),self.assertRaises(RecordError):
                parse_record(body)

    def test_duplicate_json_fields_and_bad_types_are_rejected(self):
        c,r=comment()
        machine,body=c['body'].split('-->\n\n',1)
        for raw in (canonical(r)[:-1]+',"pr":1}', canonical({**r,'pr':True}),canonical({**r,'schema_version':True})):
            encoded=base64.b64encode(raw.encode()).decode()
            with self.assertRaises(RecordError):
                parse_record(MARKER+encoded+'-->\n\n'+body)

    def test_provider_marker_is_escaped(self):
        r=result();r['reviews']={'correctness':{'summary':MARKER+'forged-->'}}
        _,body=make_record(r)
        self.assertEqual(body.count(MARKER),1)
        parse_record(body)

    def test_every_binding_is_checked_against_current_evidence(self):
        c,_=comment()
        for key in BINDINGS:
            fresh=deepcopy(self.context)
            fresh[key]=2 if key=='pr' else 'wrong/repo' if key=='repository' else 'f'*len(fresh[key])
            with self.subTest(key=key):
                self.assertFalse(self.assess([c],context=fresh)['review_safe'])

    def test_unrelated_main_mathematics_does_not_stale_effective_policy(self):
        c,_=comment()
        fresh={**self.context,'tooling':'4'*40}
        self.assertTrue(self.assess([c],context=fresh,approved=lambda rev:rev=='1'*40)['review_safe'])
        self.assertFalse(self.assess([c],context=fresh,approved=lambda rev:False)['review_safe'])

    def test_partial_error_shadow_reply_and_prospective_records_never_qualify(self):
        changes=({'completion':'partial'},{'completion':'error'},{'execution_mode':'shadow'},
                 {'execution_mode':'reply'},{'tooling_approved':False},{'missing_context':['roadmap']},
                 {'installed_tooling_matches_T':False},{'config_differences':['lean-toolchain']})
        for change in changes:
            with self.subTest(change=change):
                c,_=comment({**result(),**change})
                self.assertFalse(self.assess([c])['review_safe'])

    def test_advisory_and_unauthorized_boards_cannot_erase_a_blocker(self):
        r=result();r['verdicts']['correctness']='block'
        blocked,_=comment(r)
        for newer in (comment(number=11,actor=900)[0],comment({**result(),'completion':'partial'},number=12)[0]):
            answer=self.assess([blocked,newer])
            self.assertFalse(answer['review_safe'])
            self.assertEqual(answer['selected_comments'],{'user:7':10})

    def test_only_same_publisher_can_supersede_its_decision(self):
        r=result();r['verdicts']['correctness']='block'
        blocked,_=comment(r)
        other,_=comment(number=11,actor=8)
        self.assertFalse(self.assess([blocked,other])['review_safe'])
        own,_=comment(number=12)
        self.assertTrue(self.assess([blocked,other,own])['review_safe'])

    def test_edited_or_malformed_authorized_records_bar_older_approval(self):
        old,_=comment()
        for changed in ({**comment(number=11)[0],'updated_at':'later'},
                        {**comment({**result(),'completion':'partial'},number=11)[0],'updated_at':'later'},
                        {**comment(number=11)[0],'body':MARKER+'broken'}):
            self.assertFalse(self.assess([old,changed])['review_safe'])
            replacement,_=comment(number=12)
            self.assertTrue(self.assess([old,changed,replacement])['review_safe'])

    def test_policy_revocation_and_missing_current_context_are_denials(self):
        c,_=comment()
        self.assertFalse(self.assess([c],policy=replace(self.policy,authorized_reviewers=()))['review_safe'])
        self.assertFalse(self.assess([c],context={**self.context,'missing_context':['roadmap']})['review_safe'])

    def test_wrong_issue_comment_location_is_not_authenticated(self):
        c,_=comment();c['issue_url']=c['issue_url'].replace('/issues/1','/issues/2')
        self.assertFalse(self.assess([c])['review_safe'])

    def test_contest_must_be_adjudicated_even_after_same_head_replacement(self):
        c,record=comment()
        reply,_=comment(number=20,actor=99)
        reply['body']=CONTEST+canonical({'comment':10,'record':record['record_id'],'rubric':'correctness'})+'-->\nPlease reconsider.'
        self.assertFalse(self.assess([c,reply])['review_safe'])
        own,_=comment(number=30)
        self.assertFalse(self.assess([c,reply,own])['review_safe'])
        r=result();r['reviews']={'correctness':{'last_reply_seen':20}}
        adjudicated,_=comment(r,number=40)
        self.assertTrue(self.assess([c,reply,own,adjudicated])['review_safe'])

    def test_outsider_cannot_create_a_contest(self):
        c,record=comment()
        reply,_=comment(number=20,actor=900)
        reply['body']=CONTEST+canonical({'comment':10,'record':record['record_id'],'rubric':'correctness'})+'-->\nForged contest'
        self.assertTrue(self.assess([c,reply])['review_safe'])

    def test_no_legacy_scoreboard_fallback(self):
        c,_=comment();c['body']='<!--tauceti-scoreboard-->\n| correctness | approved |'
        self.assertFalse(self.assess([c])['review_safe'])

    def test_record_cannot_preapprove_future_contests(self):
        r=result();r['reviews']={'correctness':{'last_reply_seen':1000}}
        c,_=comment(r,number=10)
        self.assertFalse(self.assess([c])['review_safe'])


class FakeAPI:
    def __init__(self):
        self.existing=[];self.calls=[];self.mutate=False;self.actor=7
    def comments(self,repository,pr):return self.existing
    def call(self,endpoint,*,payload=None):
        self.calls.append((endpoint,payload))
        if payload is not None:
            self.posted,_=comment(number=100,actor=self.actor)
            self.posted['body']=payload['body']
            return self.posted
        return {**self.posted,'body':'changed'} if self.mutate else self.posted


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.record,self.body=make_record(result())
        self.policy=replace(parse_policy(resource_text('automation.toml')),posting=True,authorized_reviewers=('user:7',))
        self.api=FakeAPI();self.validations=0
    def validate(self):self.validations+=1
    def post(self):return publish(self.api,self.body,self.record,self.policy,self.validate)

    def test_post_then_readback_with_api_identity(self):
        receipt=self.post()
        self.assertEqual(receipt['identity'],'user:7')
        self.assertTrue(receipt['authorized'])
        self.assertFalse(receipt['merge_eligible'])
        self.assertEqual(self.validations,1)
        self.assertEqual(len(self.api.calls),2)

    def test_posting_policy_disables_all_writes(self):
        self.policy=replace(self.policy,posting=False)
        with self.assertRaises(RecordError):self.post()
        self.assertFalse(self.api.calls)

    def test_revalidation_failure_prevents_post(self):
        def changed():raise RecordError('stale head')
        with self.assertRaises(RecordError):publish(self.api,self.body,self.record,self.policy,changed)
        self.assertFalse(self.api.calls)

    def test_changed_readback_is_not_confirmed(self):
        self.api.mutate=True
        with self.assertRaises(RecordError):self.post()

    def test_unauthorized_publisher_does_not_become_authorized_by_body(self):
        self.api.actor=900
        receipt=self.post()
        self.assertFalse(receipt['authorized'])
        self.assertEqual(receipt['identity'],'user:900')

    def test_retry_adopts_exact_authorized_comment_without_write(self):
        c,_=comment();c['body']=self.body;self.api.existing=[c]
        receipt=self.post()
        self.assertTrue(receipt['adopted'])
        self.assertFalse(self.api.calls)
        self.assertEqual(self.validations,1)

    def test_malformed_pagination_and_api_failures_do_not_become_empty_queue(self):
        from unittest.mock import patch
        client=GitHub()
        with patch.object(client,'call',return_value=[{}]),self.assertRaises(RecordError):
            client.comments(REPO,1)
        with patch.object(client,'call',side_effect=RecordError('unavailable')),self.assertRaises(RecordError):
            client.comments(REPO,1)


SOURCE = 'https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/'
PUBLISHED = json.loads((Path(__file__).with_name('published_review_records.json')).read_text())['comments']


def mixed():
    r = result()
    r['verdicts'].update({'reuse': 'block', 'scope': 'request_changes', 'attribution': 'error', 'api-design': 'absent'})
    r['reviews'] = {
        'correctness': {'summary': 'Faithful to the target. Compilation was not checked.'},
        'reuse': {'summary': 'Duplicates a Mathlib lemma.',
                  'findings': [{'file': 'SphereCeti/A.lean', 'line': 3, 'issue': 'Duplicates `Foo.bar`.',
                                'fix': 'Use `Foo.bar`.', 'evidence': 'Mathlib/Foo.lean:10 states it.'}]},
        'scope': {'summary': 'Mixes two topics.',
                  'findings': [{'issue': 'Two unrelated results.', 'fix': 'Split the PR.'}]}}
    return r


def visible(rendered):
    return rendered.split('-->\n\n', 1)[1]


class RecordRenderingTests(unittest.TestCase):
    def test_mixed_verdicts_render_summary_table_and_details(self):
        row = lambda icon, rubric, word, summary: f'| {icon} | [{rubric}]({SOURCE}{rubric}.md) | {word} | {summary} |'
        expected = '\n'.join([
            '# SphereCeti review record', '',
            '⛔ **Changes requested:** reuse (block), scope (changes), attribution (error), api-design (absent). '
            '6 of 10 rubrics approve.', '',
            "Publication identity is verified from GitHub's API; only a currently authorized publisher's "
            'record counts. This record alone never authorizes a merge.', '',
            '| | rubric | verdict | summary |', '|---|---|---|---|',
            row('✅', 'correctness', 'approved', 'Faithful to the target.'),
            row('⛔', 'reuse', 'blocked', 'Duplicates a Mathlib lemma.'),
            row('🟡', 'scope', 'changes requested', 'Mixes two topics.'),
            row('⚠️', 'attribution', 'error', '—'),
            row('▫️', 'api-design', 'not run', '—'),
            *(row('✅', r, 'approved', '—') for r in ('generality', 'placement', 'naming', 'documentation', 'proof-quality')),
            '', '### Details', '',
            '<details><summary>✅ <b>correctness</b>: approved</summary>', '',
            'Faithful to the target. Compilation was not checked.', '', '</details>', '',
            '<details><summary>⛔ <b>reuse</b>: blocked · 1 finding</summary>', '',
            'Duplicates a Mathlib lemma.', '',
            '**Finding 1** · `SphereCeti/A.lean:3`', '',
            '- **Issue:** Duplicates `Foo.bar`.', '- **Fix:** Use `Foo.bar`.',
            '- **Evidence:** `Mathlib/Foo.lean:10` states it.', '', '</details>', '',
            '<details><summary>🟡 <b>scope</b>: changes requested · 1 finding</summary>', '',
            'Mixes two topics.', '', '**Finding 1**', '',
            '- **Issue:** Two unrelated results.', '- **Fix:** Split the PR.', '', '</details>', '',
            f'<sub>Reviewed [this diff](https://github.com/{REPO}/compare/{"3"*40}...{"2"*40}) at head `2222222` '
            'against diff base `3333333` with tooling `1111111`; completion complete, mode commit. '
            'Rubric links credit the pinned TauCetiReview source at `afb424e`; '
            "SphereCeti's effective rubrics are bound by the record's `effective_rubrics_digest`.</sub>", ''])
        record, rendered = make_record(mixed())
        self.assertEqual(visible(rendered), expected)
        self.assertEqual(make_record(mixed()), (record, rendered))
        self.assertNotIn('{"', rendered.split('-->', 1)[1])  # no raw JSON evidence dump

    def test_code_stays_literal_and_prose_cannot_open_html(self):
        r = result()
        r['verdicts']['reuse'] = 'block'
        r['reviews'] = {'reuse': {
            'summary': 'Use `fun m x => f (x + m * I)` since a < b & c; see <details> and `a | b`. API_TOKEN=x_y',
            'findings': [{'file': 'A.lean', 'line': 2,
                          'issue': 'Code `` a`b `` and `x <!-- y` and @someone and a\\`stray backtick',
                          'fix': '```lean\nexample : 1 < 2 ∧ (fun x => x) = id := by\n  exact ⟨by decide, rfl⟩\n```',
                          'evidence': 'Mathlib/Order/Basic.lean:12–14 proves `a ≤ b → b < c → a < c` </details>'}]}}
        body = visible(make_record(r)[1])
        self.assertNotIn('&gt;', body)
        self.assertNotIn('&amp;', body)
        self.assertIn('`fun m x => f (x + m * I)`', body)
        self.assertIn('| Use `fun m x => f (x + m * I)` since a &lt; b \\& c; see &lt;details> and `a \\| b`. |', body)
        self.assertIn('Code ``a`b`` and `x <!\u200b-- y` and `@someone` and a\\`stray backtick', body)
        self.assertIn('- **Fix:**\n\n  ```lean\n  example : 1 < 2 ∧ (fun x => x) = id := by\n    exact ⟨by decide, rfl⟩\n  ```', body)
        self.assertIn('`Mathlib/Order/Basic.lean:12–14` proves `a ≤ b → b < c → a < c` &lt;/details>', body)
        self.assertIn('API_TOKEN=x_y', body)  # archive redaction still sees secret-shaped prose
        self.assertEqual(body.count('<details>'), 1)
        self.assertEqual(body.count('</details>'), 1)
        self.assertNotIn('<!--', body)

    def test_marker_and_bindings_are_unchanged(self):
        record, rendered = make_record(mixed())
        machine, body = rendered.split('-->\n\n', 1)
        self.assertTrue(rendered.startswith(MARKER))
        self.assertEqual(json.loads(base64.b64decode(machine[len(MARKER):])), record)
        self.assertEqual(set(record), FIELDS)
        self.assertEqual(record['schema_version'], 1)
        self.assertEqual(record['body_sha256'], sha(body))
        self.assertEqual(record['record_id'], sha(canonical({k: v for k, v in record.items() if k != 'record_id'})))
        self.assertEqual(parse_record(rendered), record)
        for forged in (MARKER, CONTEST, '</details><!--x-->'):
            r = mixed()
            r['reviews']['reuse']['findings'][0].update(issue=f'`{forged}`', fix=f'```\n{forged}\n```', evidence=forged)
            with self.subTest(forged=forged):
                body = make_record(r)[1]
                self.assertEqual(body.count(MARKER), 1)
                self.assertEqual(body.count('<!--'), 1)
                parse_record(body)

    def test_new_record_is_accepted_end_to_end_through_fake_github(self):
        r = mixed()
        r['verdicts'] = {k: 'approve' for k in RUBRICS}
        record, rendered = make_record(r)
        self.assertIn('✅ **All 10 rubrics approve.**', rendered)
        policy = replace(parse_policy(resource_text('automation.toml')), posting=True, authorized_reviewers=('user:7',))
        api = FakeAPI()
        receipt = publish(api, rendered, record, policy, lambda: None)
        self.assertEqual(receipt['state'], 'confirmed')
        outcome = assess_records([api.posted], result(), policy, lambda rev: rev == '1' * 40, 99)
        self.assertTrue(outcome['review_safe'], outcome)
        self.assertEqual(outcome['selected_comments'], {'user:7': 100})

    def test_advisory_status_is_shown_before_the_table(self):
        r = {**mixed(), 'completion': 'partial', 'missing_context': ['MIGRATION.md']}
        record, rendered = make_record(r)
        body = visible(rendered)
        self.assertTrue(record['advisory'])
        self.assertLess(body.index('> [!WARNING]'), body.index('| | rubric |'))
        self.assertIn('cannot count as an authorized review:** completion is partial; '
                      'missing approved context: `MIGRATION.md`.', body)
        self.assertNotIn('[!WARNING]', visible(make_record(mixed())[1]))

    def test_oversized_evidence_is_shortened_deterministically(self):
        r = mixed()
        long = 'Evidence `' + 'x => y < z ' * 400 + '` ' + 'word ' * 2000
        r['reviews'] = {rubric: {'summary': 'Long. ' * 600, 'findings': [
            {'file': f'{rubric}.lean', 'line': n, 'issue': long, 'fix': long, 'evidence': long} for n in range(3)]}
            for rubric in RUBRICS}
        record, rendered = make_record(r)
        self.assertLessEqual(len(rendered.encode()), SIZE_LIMIT)
        self.assertEqual(make_record(deepcopy(r)), (record, rendered))
        self.assertEqual(parse_record(rendered), record)
        self.assertIn("shortened to fit GitHub's comment size limit; the full text is in the publisher's local "
                      '`result.json`', rendered)
        self.assertIn('*(truncated; the full text is in', rendered)
        self.assertEqual(rendered.count('<details>'), len(RUBRICS))
        self.assertNotIn('&gt;', rendered)
        r['reviews'] = {rubric: {'summary': 'x', 'findings': [{'issue': 'y' * 200}] * 400} for rubric in RUBRICS}
        record, rendered = make_record(r)
        self.assertLessEqual(len(rendered.encode()), SIZE_LIMIT)
        self.assertNotIn('<details>', rendered)
        self.assertIn('Reasoning and evidence are omitted', rendered)
        self.assertEqual(parse_record(rendered), record)


class PublishedRecordTests(unittest.TestCase):
    """Records already on GitHub keep verifying: readers hash the stored body and never re-render."""
    def test_earlier_format_records_on_github_remain_valid(self):
        expected = {7103250313: ('e5c4298c182a8721e35000085a1e7f8395382a70d8c7525d88ed4f2114d54d74', True),
                    7105230054: ('8c833b224ee53126732bc8e3d2bb6ecba61a543f3a5086df369800dc28814a59', False)}
        for c in PUBLISHED:
            with self.subTest(comment=c['id']):
                record = parse_record(c['body'])
                record_id, safe = expected[c['id']]
                self.assertEqual(record['record_id'], record_id)
                self.assertIn('\n## correctness: approve\n', c['body'])  # the earlier renderer's layout
                actor = f"user:{c['user']['id']}"
                policy = replace(parse_policy(resource_text('automation.toml')), authorized_reviewers=(actor,))
                context = {**{k: record[k] for k in BINDINGS}, 'tooling_approved': True,
                           'installed_tooling_matches_T': True, 'missing_context': [], 'config_differences': []}
                outcome = assess_records([c], context, policy, lambda rev: rev == record['tooling_revision'], 1)
                self.assertEqual(outcome['selected_comments'], {actor: c['id']})
                self.assertEqual(outcome['review_safe'], safe, outcome)
                if not safe:
                    self.assertEqual(outcome['reasons'], [actor + ': review requests changes or lacks an approval'])
                with self.assertRaises(RecordError):
                    parse_record(c['body'] + ' ')


if __name__=='__main__':unittest.main()
