# SPDX-License-Identifier: Apache-2.0
"""Bounded sequential review work; every round reuses the existing policy and lease guard."""
from __future__ import annotations

import signal
import time

from .worker import require
from .worker_execution import run_round


def run_loop(args, project, policy, prefs, *, round_runner=None, sleep=None):
    """Survey afresh between rounds and assess each PR head/base at most once per invocation."""
    require(type(args.max_rounds) is int and 1 <= args.max_rounds <= 20,
            '--loop requires --max-rounds between 1 and 20')
    require(type(args.interval_seconds) is int and 10 <= args.interval_seconds <= 3600,
            '--interval-seconds must be between 10 and 3600')
    runner, pause = round_runner or run_round, sleep or time.sleep
    seen, outcomes = set(), []
    def interrupted(signum, frame):
        raise KeyboardInterrupt('worker loop stopped')
    prior = signal.signal(signal.SIGTERM, interrupted)
    try:
        for index in range(args.max_rounds):
            outcome = runner(args, project, policy, prefs, assessed=frozenset(seen))
            outcomes.append(outcome)
            state = outcome['state']
            if not args.execute or state not in ('complete', 'idle'):
                reason = state
                break
            if outcome.get('state_publication', {}).get('state') == 'unconfirmed':
                reason = 'unconfirmed_publication'
                break
            key = (outcome.get('pr'), outcome.get('head'), outcome.get('base'))
            require(type(key[0]) is int and all(isinstance(v, str) and len(v) == 40 for v in key[1:]),
                    'completed round lacks exact PR/head/base bindings')
            require(key not in seen, 'round repeated already assessed evidence')
            seen.add(key)
            if index + 1 < args.max_rounds:
                pause(args.interval_seconds)
        else:
            reason = 'round_limit'
    finally:
        signal.signal(signal.SIGTERM, prior)
    return {'schema': 'sphereceti.worker-loop/v1', 'state': reason,
            'repository': project.repository, 'rounds': outcomes,
            'round_limit': args.max_rounds, 'assessed': len(seen),
            'reason': 'Stopped at the first incomplete/unsupported outcome or configured round limit.'}
