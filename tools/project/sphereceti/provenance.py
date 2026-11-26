# SPDX-License-Identifier: Apache-2.0
"""Which sphereceti build is running, and is it current approved main?

The installed commit comes from the distribution's PEP 610 `direct_url.json` (`vcs_info.commit_id`
and `requested_revision`), which uv and pip write for Git installs. A local, path or editable
install, or a source tree on `sys.path`, is a "local build"; when its package directory sits in a
Git checkout, `git rev-parse` names the checkout's commit (read-only). Nothing here fails when
metadata is missing.

"Current" means what the review path means by `installed_tooling_matches_T`: every installed
tooling file (`review_resources.tooling_files`) has the same Git blob ID at approved main T, which
is resolved as `local_review.revisions` does (`repos/{repo}/commits/{default_branch}`). doctor
reads T's tree through the API instead of fetching objects; the compare API only counts commits.
"""
from __future__ import annotations

import hashlib
import json
from importlib import metadata
from pathlib import Path
import subprocess
from urllib.parse import quote

from . import __version__

UPDATE = 'uv tool install --force --refresh git+https://github.com/{repository}@main'


def _git_head(directory: Path) -> str | None:
    try:
        result = subprocess.run(['git', '-C', str(directory), 'rev-parse', 'HEAD'], capture_output=True,
                                text=True, timeout=5, check=False)
    except (OSError, subprocess.SubprocessError):
        return None
    head = result.stdout.strip()
    return head if result.returncode == 0 and len(head) == 40 else None


def installed(*, distribution=None, package_dir: Path | None = None) -> dict:
    """Where the running package came from: {'kind', 'commit', 'requested_revision', 'label', ...}."""
    package_dir = package_dir or Path(__file__).resolve().parent
    direct = None
    try:
        dist = distribution or metadata.distribution('sphereceti')
        # The metadata must describe the code actually imported, not another copy on sys.path.
        located = Path(dist.locate_file('sphereceti/__init__.py')).resolve()
        if located.parent == package_dir:
            text = dist.read_text('direct_url.json')
            direct = json.loads(text) if text else None
    except (metadata.PackageNotFoundError, OSError, ValueError, TypeError, AttributeError):
        direct = None
    vcs = direct.get('vcs_info') if isinstance(direct, dict) else None
    commit = vcs.get('commit_id') if isinstance(vcs, dict) else None
    if isinstance(commit, str) and len(commit) == 40 and all(c in '0123456789abcdef' for c in commit):
        revision = vcs.get('requested_revision') if isinstance(vcs.get('requested_revision'), str) else None
        return {'kind': 'vcs', 'commit': commit, 'requested_revision': revision,
                'url': direct.get('url'), 'label': f"{revision or 'commit'}@{commit[:7]}"}
    checkout = _git_head(package_dir)
    editable = isinstance(direct, dict) and bool((direct.get('dir_info') or {}).get('editable'))
    return {'kind': 'local', 'commit': None, 'requested_revision': None, 'checkout_commit': checkout,
            'editable': editable,
            'label': 'local build' + (f', checkout {checkout[:7]}' if checkout else '')}


def version_string(**kwargs) -> str:
    try:
        label = installed(**kwargs)['label']
    except Exception:  # --version must never fail
        label = 'local build'
    return f'{__version__} ({label})'


def blob_id(body: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(body)).encode() + b'\0' + body).hexdigest()


def tooling_matches(tree: dict[str, str], files: dict[str, bytes]) -> bool:
    """The review path's installed_tooling_matches_T, over a {path: blob id} listing of T."""
    return all(tree.get(path) == blob_id(body) for path, body in files.items())


def compare(project, call, *, info=None, files=None) -> dict:
    """Installed build against approved main T. `call(endpoint)` is a GET returning JSON."""
    info = info or installed()
    if files is None:
        from .review_resources import tooling_files
        files = tooling_files()
    branch = quote(project.default_branch, safe='')
    approved = call(f'repos/{project.repository}/commits/{branch}')['sha']
    listing = call(f'repos/{project.repository}/git/trees/{approved}?recursive=1')
    if listing.get('truncated'):
        raise ValueError('approved main tree listing is truncated')
    tree = {e['path']: e['sha'] for e in listing['tree'] if e.get('type') == 'blob'}
    matches = tooling_matches(tree, files)
    behind = status = None
    if info.get('commit'):
        # compare/BASE...HEAD with the install as BASE: `ahead_by` counts main's commits the install
        # lacks, and `status` describes main, so it is restated from the install's side.
        relation = call(f"repos/{project.repository}/compare/{info['commit']}...{approved}")
        behind = relation.get('ahead_by')
        status = {'identical': 'identical', 'ahead': 'behind', 'behind': 'ahead',
                  'diverged': 'diverged'}.get(relation.get('status'))
    return {'installed_commit': info.get('commit'), 'installed_label': info['label'],
            'approved_main': approved, 'behind_by': behind, 'relation': status,
            'up_to_date': matches, 'update': UPDATE.format(repository=project.repository)}


def doctor_line(result: dict) -> str:
    label = result.get('installed_label') or 'local build'
    if result.get('approved_main') is None:
        return f'installed: {label}'
    approved, behind = result['approved_main'][:7], result.get('behind_by')
    source = (result.get('installed_commit') or '')[:7]
    if result['up_to_date']:
        if behind:
            return (f'installed: {label} · {behind} commits behind approved main ({source} → {approved}), '
                    'but its tooling is unchanged: reviews are official')
        return f'installed: {label} · up to date with approved main'
    if result.get('relation') == 'diverged':
        where = f'diverged from approved main ({source} → {approved})'
    elif behind:
        where = f'{behind} commits behind approved main ({source} → {approved})'
    elif result.get('relation') == 'ahead':
        where = f'ahead of approved main {approved}'
    else:
        where = f'not current approved main {approved}'
    return f"installed: {label} · {where}; update with: {result['update']}"


def review_notice(report: dict, repository: str, *, info=None) -> str | None:
    """Printed before any model call when the installed tooling is not approved main."""
    if report.get('installed_tooling_matches_T') is not False:
        return None
    info = info or installed()
    target = f"approved main {report['tooling'][:7]}" if report.get('tooling_approved') else \
        f"tooling {report['tooling'][:7]}"
    return (f"Your sphereceti is not current main (installed {info['label']}, {target}): this review will be "
            f"advisory, not official. Update with: {UPDATE.format(repository=repository)}")
