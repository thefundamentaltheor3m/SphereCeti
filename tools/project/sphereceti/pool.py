# SPDX-License-Identifier: Apache-2.0
"""Bounded concurrency for read-only per-PR GitHub work, with results in input order.

Every task here only reads (GETs, or a read-only GraphQL query), so running several at once
cannot change what is decided; `ordered` returns results in the order of its inputs, and the
first failure (in input order) is raised, as the sequential loop would have raised it.
"""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import os

WORKERS = 8


def workers() -> int:
    """SPHERECETI_READ_WORKERS=1 runs sequentially (used by tests to compare outputs)."""
    try:
        value = int(os.environ.get("SPHERECETI_READ_WORKERS", WORKERS))
    except ValueError:
        value = WORKERS
    return max(1, min(value, 16))


def concurrent(*readers) -> bool:
    """Only the real GitHub readers opt in; test fakes that answer in call order stay sequential."""
    return all(getattr(reader, "concurrent", False) for reader in readers)


def ordered(fn, items, *, on_done=None, parallel=True):
    """[fn(item) for item in items], computed concurrently; `on_done(count)` after each one."""
    items = list(items)
    count = workers() if parallel else 1
    if count == 1 or len(items) < 2:
        results = []
        for index, item in enumerate(items, 1):
            results.append(fn(item))
            if on_done:
                on_done(index)
        return results
    finished = 0
    with ThreadPoolExecutor(max_workers=min(count, len(items)), thread_name_prefix="sphereceti-read") as pool:
        futures = [pool.submit(fn, item) for item in items]
        from concurrent.futures import as_completed
        for _ in as_completed(futures):
            finished += 1
            if on_done:
                on_done(finished)
        return [future.result() for future in futures]  # the first failure in input order raises
