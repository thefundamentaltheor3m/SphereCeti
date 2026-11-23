"""GitHub ruleset responses for SphereCeti `main`, captured read-only on 2026-11-23.

Sources: `gh api repos/thefundamentaltheor3m/SphereCeti/rulesets/21449770`,
`.../rules/branches/main?per_page=100` and `.../rulesets?includes_parents=true&per_page=100`,
read by a write-role account. Node IDs, links and timestamps are removed. The detail lacks
`bypass_actors` because GitHub shows them only to readers with administration access.
Classic protection for `main` returned HTTP 404, and `branches/main` reported it disabled.
"""
from copy import deepcopy

REPO = 'thefundamentaltheor3m/SphereCeti'
GITHUB_ACTIONS_APP = 15368  # `gh api apps/github-actions`

LIVE_DETAIL = {'id': 21449770,
 'name': 'main',
 'target': 'branch',
 'source_type': 'Repository',
 'source': 'thefundamentaltheor3m/SphereCeti',
 'enforcement': 'active',
 'conditions': {'ref_name': {'exclude': [], 'include': ['refs/heads/main']}},
 'rules': [{'type': 'deletion'},
           {'type': 'non_fast_forward'},
           {'type': 'pull_request',
            'parameters': {'required_approving_review_count': 1,
                           'dismiss_stale_reviews_on_push': False,
                           'required_reviewers': [],
                           'require_code_owner_review': False,
                           'require_last_push_approval': False,
                           'required_review_thread_resolution': True,
                           'require_extra_approval_for_unattributed_changes': False,
                           'allowed_merge_methods': ['squash']}},
           {'type': 'required_status_checks',
            'parameters': {'strict_required_status_checks_policy': False,
                           'do_not_enforce_on_create': False,
                           'required_status_checks': [{'context': 'build',
                                                       'integration_id': 15368}]}}],
 'current_user_can_bypass': 'never'}

LIVE_EFFECTIVE = [{'type': 'deletion',
  'ruleset_source_type': 'Repository',
  'ruleset_source': 'thefundamentaltheor3m/SphereCeti',
  'ruleset_id': 21449770},
 {'type': 'non_fast_forward',
  'ruleset_source_type': 'Repository',
  'ruleset_source': 'thefundamentaltheor3m/SphereCeti',
  'ruleset_id': 21449770},
 {'type': 'pull_request',
  'parameters': {'required_approving_review_count': 1,
                 'dismiss_stale_reviews_on_push': False,
                 'required_reviewers': [],
                 'require_code_owner_review': False,
                 'require_last_push_approval': False,
                 'required_review_thread_resolution': True,
                 'require_extra_approval_for_unattributed_changes': False,
                 'allowed_merge_methods': ['squash']},
  'ruleset_source_type': 'Repository',
  'ruleset_source': 'thefundamentaltheor3m/SphereCeti',
  'ruleset_id': 21449770},
 {'type': 'required_status_checks',
  'parameters': {'strict_required_status_checks_policy': False,
                 'do_not_enforce_on_create': False,
                 'required_status_checks': [{'context': 'build', 'integration_id': 15368}]},
  'ruleset_source_type': 'Repository',
  'ruleset_source': 'thefundamentaltheor3m/SphereCeti',
  'ruleset_id': 21449770}]

LIVE_LISTING = [{'id': 21449770,
  'name': 'main',
  'target': 'branch',
  'source_type': 'Repository',
  'source': 'thefundamentaltheor3m/SphereCeti',
  'enforcement': 'active'}]

LIVE_BRANCH = {'name': 'main', 'protected': True,
               'protection': {'enabled': False,
                              'required_status_checks': {'checks': [], 'contexts': [], 'enforcement_level': 'off'}}}


def live():
    """Fresh copies: branch summary, effective-rule pages, ruleset listing pages and detail."""
    return deepcopy(LIVE_BRANCH), [deepcopy(LIVE_EFFECTIVE)], [deepcopy(LIVE_LISTING)], deepcopy(LIVE_DETAIL)
