# SPDX-License-Identifier: Apache-2.0
"""A small cache in the operator store for read-only queue facts that cannot change under a key.

Used only by `sphereceti reviews`, bare `review` and batches (never by the worker's explicit
targets, `--read-records`, posting, auto-approval or the merge controller, which read fresh).
`--no-cache` bypasses it. Entries:

- `scope`: the trusted-scope verdict of `worker_checks.human_review_scope`, keyed by repository,
  PR, head, base, head repository, current main, every status and check in the PR's rollup (so a
  new or changed status or run changes the key), and the digest of the packaged merge-checks
  settings. Its inputs beyond the key are a completed run attempt and its jobs, which GitHub does
  not change.
- `commit`: a commit's SHA, tree SHA and parents (`git/commits/SHA`), for carry-over checks.
- `compare`: `compare/OLD...NEW` (`status`, `ahead_by`, `behind_by`, merge base) for two exact commits.
- `merged`: a base branch some merged PR headed (a merged PR stays merged).

A failed read is never cached; a corrupt or foreign cache file is ignored and rewritten.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import tempfile
import threading

VERSION = 1
KINDS = ("scope", "commit", "compare", "merged")
LIMIT = 2000  # entries kept per kind (scope keeps only this run's keys)


class QueueCache:
    def __init__(self, path: Path):
        self.path = Path(path)
        self.lock = threading.Lock()
        self.data = {kind: {} for kind in KINDS}
        self.used = {kind: set() for kind in KINDS}
        self.hits = self.misses = 0
        try:
            loaded = json.loads(self.path.read_text())
            if isinstance(loaded, dict) and loaded.get("version") == VERSION:
                self.data = {kind: dict(loaded.get(kind) or {}) for kind in KINDS}
        except (OSError, ValueError):
            pass

    @staticmethod
    def key(*parts) -> str:
        return hashlib.sha256(json.dumps(parts, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

    def scope_key(self, project, pr, checks, settings_text):
        from .worker_checks import main_sha
        return self.key("scope", project.repository, pr.get("number"), pr.get("headRefOid"), pr.get("baseRefOid"),
                        (pr.get("headRepository") or {}).get("nameWithOwner"), main_sha(self.api, project),
                        sorted(json.dumps(c, sort_keys=True) for c in checks),
                        hashlib.sha256(settings_text.encode()).hexdigest())

    def has(self, kind, key) -> bool:
        with self.lock:
            found = key in self.data[kind]
            self.hits += found
            self.misses += not found
            if found:
                self.used[kind].add(key)
            return found

    def get(self, kind, key):
        with self.lock:
            return self.data[kind][key]

    def put(self, kind, key, value):
        with self.lock:
            self.data[kind][key] = value
            self.used[kind].add(key)

    def save(self):
        with self.lock:
            out = {"version": VERSION}
            for kind in KINDS:
                entries = self.data[kind]
                if kind == "scope":
                    entries = {k: v for k, v in entries.items() if k in self.used[kind]}
                elif len(entries) > LIMIT:
                    keep = [k for k in entries if k in self.used[kind]] + [k for k in entries if k not in self.used[kind]]
                    entries = {k: entries[k] for k in keep[:LIMIT]}
                out[kind] = entries
        try:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            handle, temporary = tempfile.mkstemp(prefix=".queue-cache-", dir=self.path.parent)
            with os.fdopen(handle, "w") as stream:
                json.dump(out, stream)
            os.replace(temporary, self.path)
        except OSError:
            pass  # a cache that cannot be written only costs the next run its reads


def attach(api, prefs, project, *, enabled=True):
    """The operator store's queue cache on this survey reader, or None with --no-cache."""
    if not enabled:
        return None
    storage = Path(prefs.storage).expanduser().resolve() / project.repository.replace("/", "__")
    cache = QueueCache(storage / "queue-cache.json")
    cache.api = api
    api.scope_cache = cache
    return cache
