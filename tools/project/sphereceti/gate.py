"""Immutable candidate/configuration gate adapted from TauCeti's PR build design.

Source: TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5,
.github/workflows/pr-build.yml and scripts/attest-pr-config.sh (Apache-2.0;
TauCeti contributors). SphereCeti uses full Git trees and unchanged config only.
No candidate scripts are executed by this module.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

from .config import parse_policy, parse_project
from .sandbox import emit_candidate_output

SHA = re.compile(r"[0-9a-f]{40}\Z")
CONFIG = ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain")
# These are generated locations, never candidate sources, even when force-added to Git.
RESERVED = {".git", ".lake", ".venv", "lake-packages"}


class GateError(ValueError):
    pass


@dataclass(frozen=True)
class Entry:
    mode: str
    oid: str


def git(repo: Path, *args: str) -> bytes:
    try:
        return subprocess.check_output(["git", "-C", str(repo), *args], stderr=subprocess.PIPE)
    except subprocess.CalledProcessError as error:
        raise GateError(f"git {args[0]} failed: {error.stderr.decode(errors='replace').strip()}") from error


def exact_commit(repo: Path, revision: str) -> str:
    if not SHA.fullmatch(revision):
        raise GateError("expected an exact full commit SHA")
    actual = git(repo, "rev-parse", "--verify", f"{revision}^{{commit}}").decode().strip()
    if actual != revision:
        raise GateError("revision is not the named commit")
    return actual


def tree(repo: Path, revision: str) -> dict[str, Entry]:
    result = {}
    for record in git(repo, "ls-tree", "-rz", "--full-tree", revision).split(b"\0"):
        if not record:
            continue
        meta, path_bytes = record.split(b"\t", 1)
        mode, kind, oid = meta.decode("ascii").split()
        path = path_bytes.decode("utf-8")
        parts = PurePosixPath(path).parts
        if not parts or path.startswith('/') or any(p in ('..', '.') for p in parts) or '\\' in path:
            raise GateError(f"invalid source path: {path!r}")
        if any(ord(c) < 32 or ord(c) == 127 for c in path):
            raise GateError("control character in source path")
        if any(p.lower() == '.git' for p in parts) or parts[0] in RESERVED:
            raise GateError(f"reserved source path: {path}")
        if mode not in ("100644", "100755") or kind != "blob":
            raise GateError(f"non-ordinary source (symlink/submodule): {path}")
        if path in result:
            raise GateError(f"duplicate source path: {path}")
        result[path] = Entry(mode, oid)
    if not result:
        raise GateError("empty Git tree")
    return result


def blob(repo: Path, entry: Entry) -> bytes:
    return git(repo, "cat-file", "blob", entry.oid)


def path_class(path: str) -> str:
    if path in ('SphereCeti/Basic.lean', 'SphereCeti/Pinned.lean', 'SphereCeti/Suggested.lean'):
        return 'protected'
    if path.startswith('SphereCeti/') and path.endswith('.lean'):
        return 'library'
    if path in ('STATUS.md', 'PROGRESS.md'):
        return 'report'
    # Roadmap, library aggregators, infrastructure, config, and unknown paths all need humans.
    return 'protected'


def evaluate(repo: Path, tooling: str, base: str, head: str) -> dict:
    for revision in (tooling, base, head):
        exact_commit(repo, revision)
    bases = git(repo, 'merge-base', '--all', base, head).decode().splitlines()
    if len(bases) != 1 or not SHA.fullmatch(bases[0]):
        raise GateError('candidate needs one unambiguous merge base')
    merge_base = bases[0]
    approved, ancestor, candidate = tree(repo, tooling), tree(repo, merge_base), tree(repo, head)
    project = parse_project(blob(repo, approved['sphereceti.toml']).decode())
    policy = parse_policy(blob(repo, approved['policy/automation.toml']).decode())
    paths = sorted(path for path in ancestor.keys() | candidate.keys()
                   if ancestor.get(path) != candidate.get(path))
    if not paths:
        raise GateError('empty candidate diff; refusing an ambiguous scope verdict')
    differences = [path for path in CONFIG if approved.get(path) != candidate.get(path)]
    for required in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
        if required not in candidate or required not in approved:
            differences.append(required)
    permitted = lambda path: any(path == prefix or path.startswith(prefix.rstrip('/') + '/')
                                 for prefix in policy.mathematical_paths)
    automatic_scope = all(path_class(path) == 'library' and permitted(path) for path in paths)
    # An empty mathematical allowlist is deliberate: SphereCeti is still a roadmap package.
    return {
        'schema_version': 1, 'repository': project.repository,
        'tooling': tooling, 'base': base, 'diff_base': merge_base, 'head': head,
        'dependency_digest': hashlib.sha256(blob(repo, approved['lake-manifest.json'])).hexdigest(),
        'changes': [{'path': path, 'class': path_class(path)} for path in paths],
        'config_attested': not differences, 'config_differences': sorted(set(differences)),
        'scope': 'mathematical' if automatic_scope and not differences else 'human_review',
        'reason': ('Approved mathematics paths only' if automatic_scope and not differences
                   else 'Protected/unknown paths, unapproved mathematics, or changed dependency configuration'),
    }


def prepare(repo: Path, tooling: str, base: str, head: str, destination: Path) -> dict:
    report = evaluate(repo, tooling, base, head)
    if not report['config_attested']:
        return report
    if destination.exists() or destination.is_symlink():
        raise GateError('candidate destination must be new')
    entries = tree(repo, head)
    # Metadata is created by Git without checkout; candidate attributes/filters/hooks never run.
    git(repo, 'clone', '--quiet', '--shared', '--no-checkout', str(repo.resolve()), str(destination))
    git(destination, 'update-ref', 'HEAD', head)
    for path, entry in entries.items():
        target = destination / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(blob(repo, entry))
        target.chmod(0o755 if entry.mode == '100755' else 0o644)
    # No candidate .lake survived tree validation. Create the only writable build mount here.
    (destination / '.lake').mkdir()
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--tooling', required=True)
    parser.add_argument('--base', required=True)
    parser.add_argument('--head', required=True)
    parser.add_argument('--destination', type=Path)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    try:
        report = (prepare(args.repo.resolve(), args.tooling, args.base, args.head,
                          args.destination.absolute()) if args.destination else
                  evaluate(args.repo.resolve(), args.tooling, args.base, args.head))
        args.report.write_text(json.dumps(report, indent=2) + '\n')
        return 0
    except (GateError, ValueError, OSError, KeyError) as error:
        emit_candidate_output(f'trusted gate: {error}')
        return 1


if __name__ == '__main__':
    sys.exit(main())
