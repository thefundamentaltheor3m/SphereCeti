# SPDX-License-Identifier: Apache-2.0
"""Progress lines on stderr during long CLI phases; stdout (and --json) is never touched.

The CLI turns this on for `review` and `reviews` unless `--quiet`; library callers and tests get
a silent reporter unless they install one. Every line starts with the wall-clock time. Counters
(`scope 23/49`) overwrite one line on a terminal, at most every couple of seconds; elsewhere they
print every tenth item and the last, so logs get no carriage returns.
"""
from __future__ import annotations

from contextlib import contextmanager
import json
from pathlib import Path
import sys
import threading
import time

COUNTER_EVERY = 10        # non-terminal: one counter line per this many items
COUNTER_SECONDS = 2.0     # terminal: at most one counter update per this many seconds


def duration(seconds: float) -> str:
    seconds = max(0, int(round(seconds)))
    if seconds < 60:
        return f"{seconds}s"
    if seconds < 3600:
        return f"{seconds // 60}m{seconds % 60:02d}s"
    return f"{seconds // 3600}h{seconds // 60 % 60:02d}m"


class Progress:
    def __init__(self, stream=None, *, enabled=True, tty=None, clock=time.monotonic, now=time.localtime,
                 verbose=True):
        self.stream = stream if stream is not None else sys.stderr
        self.enabled = enabled
        # Not verbose: per-phase lines and counters are dropped; only `summary` speaks.
        self.verbose = verbose
        self.total = None
        self.tty = self.stream.isatty() if tty is None and hasattr(self.stream, "isatty") else bool(tty)
        self.clock, self.now = clock, now
        self.lock = threading.Lock()
        self.pending = False      # a terminal counter line is open (no newline yet)
        self.last_counter = None

    def stamp(self) -> str:
        return time.strftime("%H:%M:%S", self.now())

    def summary(self, text: str, *, final=False) -> None:
        """One status line for a whole command: overwritten in place on a terminal; elsewhere only
        the final version is printed."""
        if not self.enabled:
            return
        with self.lock:
            if self.tty:
                self.stream.write(f"\r\033[K{text}" + ("\n" if final else ""))
                self.pending = not final
            elif final:
                self.stream.write(text + "\n")
            self.stream.flush()

    def line(self, text: str) -> None:
        if not self.enabled or not self.verbose:
            return
        with self.lock:
            if self.pending:
                self.stream.write("\r\033[K")
                self.pending = False
            self.stream.write(f"[{self.stamp()}] {text}\n")
            self.stream.flush()

    @contextmanager
    def phase(self, start: str, done: str, failed: str | None = None):
        """The `start` line now; `done in 12s` when the block ends, or `failed after 12s`."""
        began = self.clock()
        self.line(start)
        try:
            yield
        except BaseException:
            self.line(f"{failed or done + ': failed'} after {duration(self.clock() - began)}")
            raise
        self.line(f"{done} in {duration(self.clock() - began)}")

    def counter(self, label: str, done: int, total: int) -> None:
        """`label done/total`: overwritten in place on a terminal, every tenth line elsewhere."""
        if not self.enabled or not self.verbose or total <= 0:
            return
        final = done >= total
        if self.tty:
            moment = self.clock()
            if not final and self.last_counter is not None and moment - self.last_counter < COUNTER_SECONDS:
                return
            self.last_counter = moment
            with self.lock:
                self.stream.write(f"\r\033[K[{self.stamp()}]   {label} {done}/{total}")
                self.pending = not final
                if final:
                    self.stream.write("\n")
                self.stream.flush()
            if final:
                self.last_counter = None
        elif final or done % COUNTER_EVERY == 0:
            self.line(f"  {label} {done}/{total}")


_current = Progress(enabled=False)


def current() -> Progress:
    return _current


def install(progress: Progress) -> Progress:
    global _current
    _current = progress
    return progress


class RubricWatch:
    """Follows the engine's ledger while it runs: one line when a rubric starts, one when it ends.

    The engine (runner/review.py, SphereCeti's write-ahead marker) records `in_flight` with the
    rubric and model before each provider attempt, and folds each finished rubric into the PR's
    case file with its verdict, duration and cost. Polling that file needs no engine change. A
    rubric whose case was already current at this head before the run is reported as reused.
    """

    def __init__(self, progress, ledger: Path, pr: str, head: str, rubrics, providers, interval=0.25):
        self.progress, self.ledger, self.pr, self.head = progress, ledger, pr, head
        self.rubrics, self.providers, self.interval = list(rubrics), list(providers), interval
        self.started, self.finished = set(), set()
        self.before = self.cases()
        self.stop = threading.Event()
        self.thread = None

    def read(self):
        try:
            return json.loads(self.ledger.read_text())
        except (OSError, ValueError):
            return None  # absent, or mid-write (the engine rewrites it in place): next poll

    def cases(self, data=None):
        data = data if data is not None else self.read()
        state = (((data or {}).get("prs") or {}).get(self.pr) or {}).get("state") or {}
        return {r: dict(state[r]) for r in self.rubrics if isinstance(state.get(r), dict)}

    def label(self, rubric):
        return f"Rubric {self.rubrics.index(rubric) + 1}/{len(self.rubrics)} {rubric}"

    def poll(self):
        data = self.read()
        if data is None:
            return
        # Endings first: one poll can see a rubric finish and the next one start.
        for rubric, case in self.cases(data).items():
            if rubric in self.finished or case.get("reviewed_sha") != self.head:
                continue
            if case == self.before.get(rubric):
                continue  # unchanged since the run began
            self.finished.add(rubric)
            self.progress.line(f"{self.label(rubric)}: {self.outcome(case)}")
        flight = data.get("in_flight")
        rubric = flight.get("rubric") if isinstance(flight, dict) else None
        if rubric in self.rubrics and rubric not in self.started and rubric not in self.finished:
            self.started.add(rubric)
            who = " ".join(x for x in (self.providers[0] if len(self.providers) == 1 else None,
                                       flight.get("model")) if x)
            self.progress.line(f"{self.label(rubric)}: running ({who or 'provider'})…")

    @staticmethod
    def outcome(case):
        parts = []
        if isinstance(case.get("duration_s"), (int, float)):
            parts.append(duration(case["duration_s"]))
        if isinstance(case.get("cost_usd"), (int, float)):
            parts.append(("est. " if case.get("cost_estimated") else "") + f"${case['cost_usd']:.2f}")
        return f"{case.get('verdict', 'error')}" + (f" ({', '.join(parts)})" if parts else "")

    def run(self):
        while not self.stop.wait(self.interval):
            self.poll()

    def __enter__(self):
        if self.progress.enabled:
            self.thread = threading.Thread(target=self.run, name="sphereceti-rubrics", daemon=True)
            self.thread.start()
        return self

    def __exit__(self, *exc):
        if self.thread:
            self.stop.set()
            self.thread.join()
        self.finish()
        return False

    def finish(self):
        """The final ledger: rubrics that ended after the last poll, then those reused unchanged."""
        if not self.progress.enabled:
            return
        self.poll()
        for rubric, case in self.cases().items():
            if (rubric not in self.finished and case.get("reviewed_sha") == self.head
                    and case == self.before.get(rubric)):
                self.finished.add(rubric)
                self.progress.line(f"{self.label(rubric)}: {case.get('verdict')} (reused: already current "
                                   "at this head)")
