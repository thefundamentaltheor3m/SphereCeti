# SPDX-License-Identifier: Apache-2.0
"""First-run review preferences and `sphereceti setup`.

Preferences stay within the existing operator schema (provider, budget_usd, storage). Nothing
here reads or changes repository policy, credentials or provider logins.
"""
from __future__ import annotations

import json
import math
import os
from pathlib import Path
import sys

from .config import ConfigError, OperatorPreferences, parse_operator

DEFAULT_PROVIDER = "codex"
DEFAULT_BUDGET = 5
ATTEMPTS = 3
BUDGET_NOTE = ("The budget is a daily threshold in estimated dollars, checked before each rubric; "
               "it is not a cap on subscription usage.")


class SetupError(ValueError):
    pass


def default_path() -> Path:
    return Path.home() / ".config/sphereceti/operator.toml"


def dollars(value) -> str:
    return str(int(value)) if float(value).is_integer() else repr(float(value))


def render(prefs: OperatorPreferences) -> str:
    text = f"provider = {json.dumps(prefs.provider)}\nbudget_usd = {dollars(prefs.budget_usd)}\n"
    if prefs.storage != OperatorPreferences.storage:
        text += f"storage = {json.dumps(prefs.storage)}\n"
    if parse_operator(text) != prefs:  # the file must load back exactly as saved
        raise SetupError("preferences could not be saved faithfully")
    return text


def providers() -> tuple[str, ...]:
    from .local_review import PROVIDERS
    return tuple(PROVIDERS)


def check_provider(value: str) -> str:
    if value not in providers():
        raise SetupError(f"provider must be one of: {', '.join(providers())}")
    return value


def check_budget(value) -> float:
    try:
        budget = float(value)
    except (TypeError, ValueError):
        raise SetupError("budget must be a number of dollars, such as 5") from None
    if not math.isfinite(budget) or budget <= 0:
        raise SetupError("budget must be a positive, finite number of dollars")
    return budget


def interactive(stdin=None, stdout=None) -> bool:
    stdin, stdout = stdin or sys.stdin, stdout or sys.stdout
    try:
        return stdin.isatty() and stdout.isatty()
    except (AttributeError, ValueError):
        return False


def ask(question, default, check, stdin, stderr):
    """Prompts go to stderr so `--json` output stays machine-readable."""
    for _ in range(ATTEMPTS):
        stderr.write(f"{question} [{default}]: ")
        stderr.flush()
        line = stdin.readline()
        if not line:
            raise SetupError("no answer (end of input); no preferences were saved")
        answer = line.strip() or str(default)
        try:
            return check(answer)
        except SetupError as error:
            stderr.write(f"  {error}\n")
    raise SetupError(f"no valid answer after {ATTEMPTS} attempts; no preferences were saved")


def questions(current: OperatorPreferences, stdin, stderr, *, provider=None, budget=None) -> OperatorPreferences:
    """Ask for whichever of provider and budget is not already given; defaults show current values."""
    if provider is None:
        default = current.provider if current.provider in providers() else DEFAULT_PROVIDER
        provider = ask(f"Review provider ({', '.join(providers())})", default, check_provider, stdin, stderr)
    if budget is None:
        stderr.write(BUDGET_NOTE + "\n")
        default = dollars(current.budget_usd) if current.budget_usd > 0 else DEFAULT_BUDGET
        budget = ask("Daily budget threshold in estimated USD", default, check_budget, stdin, stderr)
    return OperatorPreferences(provider=provider, budget_usd=budget, storage=current.storage)


def write_new(path: Path, text: str) -> None:
    """Create the file with mode 0600; an existing file is never overwritten."""
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    try:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError:
        raise SetupError(f"{path} already exists; it was not changed") from None
    with os.fdopen(descriptor, "w") as stream:
        stream.write(text)


def replace(path: Path, text: str) -> None:
    """`setup` rewrites deliberately: atomically, keeping mode 0600."""
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    temporary = path.with_name(path.name + ".tmp")
    temporary.unlink(missing_ok=True)
    descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(descriptor, "w") as stream:
        stream.write(text)
    temporary.replace(path)


def needs_first_run(args, operator_path) -> bool:
    """A review that will call a provider, with no saved or command-line budget."""
    return (args.command == "review" and operator_path is None and args.auth == "subscription"
            and not args.shadow and args.budget_usd is None
            and not args.dry_run and not args.read_records)


def hint() -> str:
    return (f"sphereceti setup --provider {DEFAULT_PROVIDER} --budget-usd {DEFAULT_BUDGET}")


def first_run(*, path=None, provider=None, stdin=None, stdout=None, stderr=None) -> OperatorPreferences:
    """Ask once on a terminal, save, and return the new preferences; never prompt otherwise."""
    path = path or default_path()
    stdin, stdout, stderr = stdin or sys.stdin, stdout or sys.stdout, stderr or sys.stderr
    if not interactive(stdin, stdout):
        raise SetupError(f"no review preferences yet; create them with `{hint()}` "
                         "(or pass --provider and --budget-usd)")
    stderr.write("SphereCeti needs two review preferences before your first review.\n")
    current = OperatorPreferences(provider=provider) if provider in providers() else OperatorPreferences()
    prefs = questions(current, stdin, stderr)
    write_new(path, render(prefs))
    stderr.write(f"Saved review preferences to {path}. Change them with `sphereceti setup`.\n")
    stderr.flush()
    return prefs


def add_parser(commands):
    p = commands.add_parser("setup", help="show and change your review preferences (provider and budget)")
    p.add_argument("--provider", help="review provider; skips its question")
    p.add_argument("--budget-usd", help="daily estimated-dollar threshold; skips its question")
    p.add_argument("--operator-config", type=Path, help="preferences file (default: ~/.config/sphereceti/operator.toml)")
    return p


def run_setup(args, *, stdin=None, stdout=None, stderr=None) -> str:
    """Re-runnable: shows the current values, asks only what flags leave open, rewrites the file."""
    stdin, stdout, stderr = stdin or sys.stdin, stdout or sys.stdout, stderr or sys.stderr
    path = args.operator_config or default_path()
    try:
        current = parse_operator(path.read_text()) if path.is_file() else OperatorPreferences()
    except (ConfigError, OSError, ValueError) as error:
        raise SetupError(f"{path} could not be read ({error}); fix or remove it first") from None
    stderr.write(f"Current preferences ({path if path.is_file() else 'not saved yet'}): "
                 f"provider = {current.provider}, budget_usd = {dollars(current.budget_usd)}\n")
    provider = check_provider(args.provider) if args.provider else None
    budget = check_budget(args.budget_usd) if args.budget_usd is not None else None
    if (provider is None or budget is None) and not interactive(stdin, stdout):
        raise SetupError(f"not a terminal; pass both values, e.g. `{hint()}`")
    prefs = questions(current, stdin, stderr, provider=provider, budget=budget)
    replace(path, render(prefs))
    return (f"Saved review preferences to {path}: provider = {prefs.provider}, "
            f"budget_usd = {dollars(prefs.budget_usd)}.")
