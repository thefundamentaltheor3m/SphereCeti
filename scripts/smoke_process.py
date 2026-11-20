# SPDX-License-Identifier: Apache-2.0
"""Linux stage ownership: a private subreaper contains even detached descendants."""
import ctypes
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


class Interrupted(BaseException):
    pass


def _subreaper(value=None):
    libc = ctypes.CDLL(None, use_errno=True)
    prctl = libc.prctl
    prctl.argtypes = [ctypes.c_int, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_ulong]
    current = ctypes.c_int()
    if prctl(37, ctypes.addressof(current), 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), 'cannot read Linux child-subreaper state')
    if value is not None and prctl(36, value, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), 'cannot set Linux child-subreaper state')
    return current.value


def _children():
    # This supervisor has one thread and no children except the stage's descendants.
    return [int(pid) for pid in Path(f'/proc/self/task/{os.getpid()}/children').read_text().split()]


def _cleanup():
    """TERM each adopted child, then KILL/reap it; pidfds prevent PID-reuse mistakes."""
    owned = {}
    deadline = time.monotonic() + 5
    found = False
    try:
        while True:
            while True:
                try:
                    pid, _ = os.waitpid(-1, os.WNOHANG)
                except ChildProcessError:
                    break
                if pid == 0:
                    break
                if pid in owned:
                    os.close(owned.pop(pid)[0])
            children = _children()
            if not children:
                return found
            now = time.monotonic()
            for pid in children:
                if pid not in owned:
                    # An exited child remains our zombie until reaped, so this PID cannot
                    # be reassigned between the children read and pidfd_open.
                    fd = os.pidfd_open(pid)
                    owned[pid] = (fd, now + 0.3)
                    found = True
                    try:
                        signal.pidfd_send_signal(fd, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                elif now >= owned[pid][1]:
                    try:
                        signal.pidfd_send_signal(owned[pid][0], signal.SIGKILL)
                    except ProcessLookupError:
                        pass
            if now >= deadline:
                raise RuntimeError('stage descendants could not be reaped; cleanup is unverified')
            time.sleep(0.01)
    finally:
        for fd, _ in owned.values():
            os.close(fd)


def _supervise(command, cwd, stdout, timeout):
    result = {'cleanup_verified': False}
    previous = _subreaper(1)
    try:
        def interrupted(signum, frame):
            raise Interrupted()
        signal.signal(signal.SIGTERM, interrupted)
        signal.signal(signal.SIGINT, interrupted)
        child = None
        try:
            child = subprocess.Popen(command, cwd=cwd, stdout=stdout, stderr=subprocess.STDOUT)
            result['exit_code'] = child.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            result['reason'] = 'stage timeout; owned descendants stopped'
        except Interrupted:
            result['reason'] = 'stage interrupted; owned descendants stopped'
        except (OSError, ValueError) as error:
            result['reason'] = str(error)
        finally:
            signal.signal(signal.SIGTERM, signal.SIG_IGN)
            signal.signal(signal.SIGINT, signal.SIG_IGN)
            leftover = _cleanup()
            if child is not None:
                child.poll()  # Cleanup may already have reaped it; settle Popen's local state.
            result['cleanup_verified'] = True
            if leftover and 'reason' not in result:
                result['reason'] = 'command left descendant processes; owned descendants stopped'
    finally:
        _subreaper(previous)
    return result


def run_owned(command, *, cwd, stdout, timeout):
    """Run a stage in its own supervisor; the caller's children/subreaper state stay untouched."""
    if (sys.platform != 'linux' or not hasattr(os, 'pidfd_open')
            or not hasattr(signal, 'pidfd_send_signal') or not Path('/proc/self/task').is_dir()):
        raise OSError('smoke cleanup requires Linux /proc, child subreapers and pidfds')
    _subreaper()  # Fail before launching any stage if this host cannot support the contract.
    probe = os.pidfd_open(os.getpid())
    os.close(probe)
    reader, writer = os.pipe()
    try:
        supervisor = os.fork()
    except BaseException:
        os.close(reader)
        os.close(writer)
        raise
    if supervisor == 0:
        os.close(reader)
        try:
            os.setsid()
            try:
                result = _supervise(command, cwd, stdout, timeout)
            except BaseException as error:
                result = {'reason': f'stage supervisor failed: {type(error).__name__}: {str(error)[:300]}',
                          'cleanup_verified': False}
            if 'reason' in result:
                result['reason'] = result['reason'][:400]
            packet = json.dumps(result).encode()
            # The parent waits before reading. Stay below Linux PIPE_BUF so diagnostics
            # can never fill that pipe and deadlock supervisor termination.
            if len(packet) >= 4096:
                packet = b'{"reason":"supervisor result exceeds bound","cleanup_verified":false}'
            os.write(writer, packet)
        finally:
            os.close(writer)
            os._exit(0)
    os.close(writer)
    interrupted = None
    supervisor_fd = os.pidfd_open(supervisor)
    try:
        while True:
            try:
                os.waitpid(supervisor, 0)
                break
            except (KeyboardInterrupt, SystemExit) as error:
                if interrupted is None:
                    interrupted = error
                try:
                    signal.pidfd_send_signal(supervisor_fd, signal.SIGTERM)
                except ProcessLookupError:
                    pass
        raw = os.read(reader, 65536)
    finally:
        os.close(reader)
        os.close(supervisor_fd)
    if interrupted is not None:
        raise interrupted
    try:
        result = json.loads(raw)
    except ValueError as error:
        raise RuntimeError('stage supervisor returned no cleanup evidence') from error
    if result.get('cleanup_verified') is not True:
        raise RuntimeError(result.get('reason', 'stage cleanup is unverified'))
    return result
