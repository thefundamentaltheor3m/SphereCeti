"""Carry a review, or a formal approval, on head H1 over to an "Update branch" head H2.

Decision 2 on #100, approved by the maintainer. GitHub's "Update branch" makes a merge commit of
main into the PR, so the head changes while the PR's own change does not. A review record or APPROVE
on H1 stays current for H2 only when ALL of these hold, and any doubt means no carry-over:

1. H2 descends from H1 only through update-branch merges: every commit from H2 back to H1 has
   exactly two parents, the previous head first and a commit on current main's first-parent
   history second. No other commit may appear, and the chain is bounded.
2. The PR's own change is identical: merge-base(M, H1)..H1 and merge-base(main, H2)..H2 agree path
   by path in mode and blob ID, where M is the newest merged main commit. A conflict resolution, a
   main change to a file the PR changes, or any extra change in a merge commit makes them differ.
3. No review input changed on main between the review's tooling_revision and current main (which
   contains M), by option 2's classification; a SphereCeti.lean-only change is measured and still
   blocks.

The rule is evaluated from Git objects (the decision) or from GET-only GitHub API reads (selection,
the queue, record inspection, the controller's approval check). Both answer with the same result.
"""
from __future__ import annotations

import hashlib
import json

from .gate import CONFIG, GateError, git, tree as git_tree
from .local_review import DOCUMENTS
from .review_records import MARKER, RecordError, intact, parse_record

ROOT_MODULE = 'SphereCeti.lean'
SPEC_DOCUMENTS = {'README.md', 'CONVENTIONS.md', 'MIGRATION.md', 'PROVENANCE.md', 'UPSTREAM.md',
                  'VALIDATION.md', 'AGENTS.md', 'CONTRIBUTING.md', 'INFRASTRUCTURE-PLAN.md',
                  'SphereCetiRoadmap.lean', 'sphereceti.toml'}
# Option 2: paths outside these prefixes are review inputs. The merged-tree trusted build at current
# main covers build and CI tooling, and reviewers are not shown tests or infrastructure docs.
NOT_REVIEW_INPUTS = ('tests/', 'docs/infrastructure/', 'scripts/', '.github/')
MAX_MERGES = 20          # update-branch merges between a reviewed head and the current head
MAIN_HISTORY = 500       # first-parent commits of main searched for each merged main commit


def input_category(path):
    """Which review input a path changed on main belongs to, or None when it is not an input."""
    if path == ROOT_MODULE:
        return 'library root'  # Measured separately: independent proofs each add an import here.
    if path.startswith('SphereCeti/'):
        return 'library'  # Imports are not traced; any library change on main forces re-review.
    if path.startswith('policy/') or path == 'sphereceti.toml':
        return 'policy'
    if path.startswith('SphereCetiRoadmap/') or path in SPEC_DOCUMENTS or path in DOCUMENTS:
        return 'specification'
    if path in CONFIG or path in ('uv.lock', 'pyproject.toml'):
        return 'dependencies'
    if path.startswith('tools/'):
        return 'review tooling'
    if path.startswith(NOT_REVIEW_INPUTS):
        return None
    return 'other'


def rows(source, base, head):
    """The change from `base` to `head`: each differing path with both modes and object IDs."""
    before, after = source.tree(base), source.tree(head)
    return [[p, *before.get(p, ('', '')), *after.get(p, ('', ''))]
            for p in sorted(before.keys() | after.keys()) if before.get(p) != after.get(p)]


def digest(change_rows):
    return hashlib.sha256(json.dumps(change_rows).encode()).hexdigest()


def changed_inputs(source, revision, main):
    """Paths changed on main since `revision`, by review-input category; unrelated paths separately."""
    changed = {}
    for row in rows(source, revision, main):
        changed.setdefault(input_category(row[0]) or 'not a review input', set()).add(row[0])
    inputs = {k: sorted(v) for k, v in sorted(changed.items()) if k != 'not a review input'}
    return inputs, sorted(changed.get('not a review input', ()))


class GitSource:
    """Exact Git objects already fetched for the decision."""

    def __init__(self, repo):
        self.repo, self._trees = repo, {}

    def tree(self, revision):
        if revision not in self._trees:
            self._trees[revision] = {p: (e.mode, e.oid) for p, e in git_tree(self.repo, revision).items()}
        return self._trees[revision]

    def parents(self, revision):
        return git(self.repo, 'rev-list', '--parents', '-n', '1', revision).decode().split()[1:]

    def merge_base(self, a, b):
        bases = git(self.repo, 'merge-base', '--all', a, b).decode().split()
        if len(bases) != 1:
            raise RecordError('no unambiguous merge base')
        return bases[0]

    def first_parent(self, main, limit=MAIN_HISTORY):
        return git(self.repo, 'rev-list', '--first-parent', f'--max-count={limit}', main).decode().split()


class ApiSource:
    """The same reads through GET-only GitHub API calls (trees, commits, compare); never a write."""

    def __init__(self, client, repository):
        self.client, self.repository, self._trees, self._parents = client, repository, {}, {}

    def _commit(self, revision):
        value = self.client.call(f'repos/{self.repository}/git/commits/{revision}')
        if not isinstance(value, dict) or value.get('sha') != revision or not isinstance(value.get('parents'), list):
            raise RecordError('incomplete commit response')
        self._parents[revision] = [p.get('sha') for p in value['parents']]
        return value

    def tree(self, revision):
        if revision not in self._trees:
            root = ((self._commit(revision).get('tree') or {}).get('sha'))
            value = self.client.call(f'repos/{self.repository}/git/trees/{root}?recursive=1')
            if not isinstance(value, dict) or value.get('truncated') is not False or not isinstance(value.get('tree'), list):
                raise RecordError('the tree listing is incomplete; carry-over cannot be decided')
            self._trees[revision] = {e['path']: (e['mode'], e['sha']) for e in value['tree']
                                     if isinstance(e, dict) and e.get('type') in ('blob', 'commit')}
        return self._trees[revision]

    def parents(self, revision):
        if revision not in self._parents:
            self._commit(revision)
        return self._parents[revision]

    def merge_base(self, a, b):
        value = self.client.call(f'repos/{self.repository}/compare/{a}...{b}')
        base = (value.get('merge_base_commit') or {}).get('sha') if isinstance(value, dict) else None
        if not isinstance(base, str):
            raise RecordError('no merge base reported')
        return base

    def first_parent(self, main, limit=MAIN_HISTORY):
        chain, current = [], main
        while current and len(chain) < limit:
            chain.append(current)
            parents = self.parents(current)
            current = parents[0] if parents else None
        return chain


def carry(source, h1, h2, main, tooling_revisions):
    """Can a review (or approval) of H1, made at `tooling_revisions`, stand for the current head H2?

    Returns the decision with precise reasons; never raises for an ordinary "no".
    """
    result = {'carried': False, 'from': h1, 'to': h2, 'via': [], 'reason': None,
              'changed_inputs': {}, 'library_root_only': False, 'unrelated_changes': []}
    if h1 == h2:
        result['reason'] = 'the record is for the current head; nothing to carry over'
        return result
    try:
        mainline = set(source.first_parent(main))
        current = h2
        while current != h1:
            if len(result['via']) >= MAX_MERGES:
                result['reason'] = f'more than {MAX_MERGES} commits separate {h1[:12]} from {h2[:12]}'
                return result
            parents = source.parents(current)
            if len(parents) != 2:
                result['reason'] = (f'{current[:12]} is not an update-branch merge ({len(parents)} parent'
                                    f"{'' if len(parents) == 1 else 's'}); only update merges may follow the reviewed head")
                return result
            if parents[1] not in mainline:
                result['reason'] = (f'{current[:12]} merges {parents[1][:12]}, which is not on main\'s '
                                    'first-parent history')
                return result
            result['via'].append({'merge': current, 'main': parents[1]})
            current = parents[0]
        newest = result['via'][0]['main']
        reviewed = rows(source, source.merge_base(newest, h1), h1)
        now = rows(source, source.merge_base(main, h2), h2)
        if reviewed != now:
            before, after = {r[0]: r for r in reviewed}, {r[0]: r for r in now}
            differing = sorted(p for p in before.keys() | after.keys() if before.get(p) != after.get(p))
            result['reason'] = ('the PR\'s own change differs after the update (a conflict resolution, a main change '
                                'to a file the PR changes, or an extra change): ' + ', '.join(differing[:5]))
            return result
        inputs, unrelated = {}, set()
        for revision in sorted(set(tooling_revisions)):
            found, other = changed_inputs(source, revision, main)
            for name, paths in found.items():
                inputs[name] = sorted(set(inputs.get(name, [])) | set(paths))
            unrelated |= set(other)
        result.update(changed_inputs=inputs, library_root_only=set(inputs) == {'library root'},
                      unrelated_changes=sorted(unrelated))
        if not tooling_revisions:
            result['reason'] = 'the review revision is unknown'
        elif inputs:
            result['reason'] = 'review inputs changed on main since the review: ' + '; '.join(
                f"{name}: {', '.join(paths[:3])}" for name, paths in inputs.items()) + (
                ' (measurement: only SphereCeti.lean changed; it still forces re-review for now)'
                if result['library_root_only'] else '')
        else:
            result['carried'] = True
        return result
    except (RecordError, GateError, ValueError, KeyError, TypeError, AttributeError) as error:
        result['reason'] = f'carry-over could not be decided ({error})'
        return result


def describe(result):
    """One line for selection, the queue and record inspection."""
    if result.get('carried'):
        merges = len(result['via'])
        return (f"current (carried over from {result['from'][:7]} via update-branch"
                + (f", {merges} merges" if merges > 1 else '') + ')')
    return f"not carried over from {result['from'][:7]}: {result['reason']}"


def older_records(comments, repository, number, head):
    """Complete, non-advisory commit/manual records on other heads of this PR, by head, newest first."""
    found = {}
    for c in sorted(comments, key=lambda c: c.get('id', 0), reverse=True):
        body = c.get('body')
        if not isinstance(body, str) or MARKER not in body or not intact(c, repository, number):
            continue
        try:
            r = parse_record(body)
        except (ValueError, TypeError):
            continue
        if (r['repository'] == repository and r['pr'] == number and r['head'] != head and not r['advisory']
                and r['completion'] == 'complete' and r['execution_mode'] in ('commit', 'manual')):
            found.setdefault(r['head'], []).append((c, r))
    return found


def carried_records(client, comments, repository, number, head, main=None):
    """(records, result) for the newest older head whose records carry over to `head`, read through the
    GET-only API; (None, last result or None) otherwise. Record acceptance itself stays with the caller.
    Main is read only when an older record exists."""
    source, last = ApiSource(client, repository), None
    older = older_records(comments, repository, number, head)
    if older and main is None:
        try:
            main = client.call(f'repos/{repository}/commits/main').get('sha')
        except (RecordError, AttributeError):
            return None, None  # Unknown main: no carry-over, so a fresh review is asked for.
    for older_head, items in older.items():
        last = carry(source, older_head, head, main, [r['tooling_revision'] for _, r in items])
        if last['carried']:
            return items, last
    return None, last
