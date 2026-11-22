#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Run one command, such as a worker round, under the repository's child-subreaper supervisor.

    python3 -I scripts/run_supervised.py [--timeout SECONDS] -- COMMAND [ARG ...]

The command runs in the current directory with inherited stdout/stderr. When it ends, the
supervisor stops and reaps every descendant it adopted, including processes in other process
groups or sessions, then this script prints smoke_process.run_owned's JSON report as its last
line. The exit status is the contract a calling script must check:

    0    the command exited 0, cleanup was verified and the timeout did not fire
    N    the command's own nonzero status (128 + signal number if a signal ended it);
         cleanup was verified
    124  the supervisor timeout (default 2100 seconds) fired; descendants were stopped
    125  cleanup is unverified, including when the supervisor itself failed or this
         script was interrupted; check for leftover processes before continuing
    126  the command could not be started
    130  the supervisor was terminated before the command finished; descendants were stopped
    2    usage error; nothing was run

A report `reason` alongside status 0 or N says the command left descendants that were stopped.
Codes 124-126 and 130 can also be a command's own status; the report's `exit_code` tells
them apart.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import sys

# -I drops the script directory from sys.path; add it explicitly, never the current directory.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from smoke_process import run_owned  # noqa: E402

TIMEOUT = 2100
SUPERVISOR_TIMEOUT = 124
CLEANUP_UNVERIFIED = 125
NOT_STARTED = 126
SUPERVISOR_INTERRUPTED = 130
# The reasons smoke_process reports when no command status exists.
TIMEOUT_REASON = 'stage timeout; owned descendants stopped'
INTERRUPTED_REASON = 'stage interrupted; owned descendants stopped'


def status(report):
    """The shell exit status for a run_owned report (see the module docstring)."""
    if report.get('cleanup_verified') is not True:
        return CLEANUP_UNVERIFIED
    code = report.get('exit_code')
    if type(code) is int:
        return code if code >= 0 else 128 - code
    return {TIMEOUT_REASON: SUPERVISOR_TIMEOUT,
            INTERRUPTED_REASON: SUPERVISOR_INTERRUPTED}.get(report.get('reason'), NOT_STARTED)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--timeout', type=float, default=TIMEOUT,
                        help=f'seconds before the command and its descendants are stopped (default {TIMEOUT})')
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command or not 0 < args.timeout < float('inf'):
        parser.error('give a positive finite --timeout and a command after --')
    try:
        report = run_owned(command, cwd=os.getcwd(), stdout=None, timeout=args.timeout)
    except (Exception, KeyboardInterrupt) as error:
        report = {'cleanup_verified': False,
                  'reason': f'{type(error).__name__}: {str(error)[:300]}; cleanup unverified'}
    print(json.dumps(report), flush=True)
    return status(report)


if __name__ == '__main__':
    sys.exit(main())
