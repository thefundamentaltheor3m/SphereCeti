"""Installed TauCetiReview resources and SphereCeti's explicit project overlays."""
from __future__ import annotations

import hashlib
from importlib import resources
from pathlib import Path

from .config import resource_text


def review_files() -> dict[str, bytes]:
    """Read the installed bundle, or the module-anchored development source."""
    root = resources.files("sphereceti").joinpath("resources", "review")
    if not root.is_dir():
        root = Path(__file__).resolve().parents[3] / "tools" / "review"
    files = {}

    def walk(directory, prefix):
        for entry in sorted(directory.iterdir(), key=lambda p: p.name):
            name = prefix + entry.name
            if entry.name == "__pycache__" or entry.name.endswith(".pyc"):
                continue
            if entry.is_dir():
                walk(entry, name + "/")
            else:
                files[name] = entry.read_bytes()

    for name in ("runner", "rubrics", "project"):
        walk(root.joinpath(name), name + "/")
    for name in ("LICENSE", "import-manifest.json"):
        files[name] = root.joinpath(name).read_bytes()
    return files


def tooling_files() -> dict[str, bytes]:
    """Map executable/package resources to their source paths for comparison with T."""
    files = {"tools/review/" + name: body for name, body in review_files().items()}
    for entry in resources.files("sphereceti").iterdir():
        if entry.name.endswith(".py"):
            files["tools/project/sphereceti/" + entry.name] = entry.read_bytes()
    for name, path in (("sphereceti.toml", "sphereceti.toml"),
                       ("automation.toml", "policy/automation.toml"),
                       ("upstream-lock.toml", "tools/upstream-lock.toml")):
        files[path] = resource_text(name).encode()
    return files


def digest(files: dict[str, bytes]) -> str:
    h = hashlib.sha256()
    for name, body in sorted(files.items()):
        h.update(name.encode() + b"\0" + str(len(body)).encode() + b"\0" + body)
    return h.hexdigest()


def stage_engine(destination: Path) -> dict:
    files = review_files()
    for name, body in files.items():
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(body)
    # Keep the imported originals intact. Only the effective prompt copy uses project policy.
    effective = {name.removeprefix("rubrics/"): body for name, body in files.items()
                 if name.startswith("rubrics/")}
    for name, body in files.items():
        if name.startswith("project/"):
            effective[name.removeprefix("project/")] = body
    for name, body in effective.items():
        target = destination / "effective-rubrics" / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(body)
    return {"engine_digest": digest({n: b for n, b in files.items() if n.startswith("runner/")}),
            "effective_rubrics_digest": digest(effective),
            "installed_tooling_digest": digest(tooling_files())}
