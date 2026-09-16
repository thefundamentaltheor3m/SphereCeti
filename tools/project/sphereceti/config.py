"""Small project profile separating source identity, policy, and operator preferences.

This is SphereCeti's integration layer for the TauCeti components credited in
INFRASTRUCTURE-PLAN.md. It does not import or relicense their implementations.
"""

from __future__ import annotations

from dataclasses import dataclass
from importlib import resources
from pathlib import Path, PurePosixPath
import re
import tomllib


class ConfigError(ValueError):
    """Invalid or unsupported configuration; never silently accept unknown policy."""


REPOSITORY = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]*/[A-Za-z0-9][A-Za-z0-9_.-]*\Z")
COMMIT = re.compile(r"[0-9a-f]{40}\Z")
RESOURCE_PATHS = {
    "archive.toml": "policy/archive.toml",
    "sphereceti.toml": "sphereceti.toml",
    "automation.toml": "policy/automation.toml",
    "upstream-lock.toml": "tools/upstream-lock.toml",
}


def resource_text(name: str) -> str:
    packaged = resources.files("sphereceti").joinpath("resources", name)
    if packaged.is_file():
        return packaged.read_text(encoding="utf-8")
    # Source development only: anchor to this module, never the caller's checkout.
    source_root = Path(__file__).resolve().parents[3]
    return (source_root / RESOURCE_PATHS[name]).read_text(encoding="utf-8")


def fields(data: dict, expected: set[str], context: str) -> None:
    if not isinstance(data, dict) or set(data) != expected:
        raise ConfigError(f"{context}: expected fields {', '.join(sorted(expected))}")


def nonempty(value, context: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ConfigError(f"{context}: expected nonempty text")
    return value


def local_path(value, context: str) -> str:
    value = nonempty(value, context)
    path = PurePosixPath(value)
    if path.is_absolute() or '..' in path.parts or '\\' in value or any(c.isspace() for c in value):
        raise ConfigError(f"{context}: expected a repository-relative path without traversal")
    if path == PurePosixPath('.'):
        raise ConfigError(f"{context}: the repository root is not a source path")
    return value


def version(data: dict, context: str) -> None:
    if type(data.get("schema_version")) is not int or data["schema_version"] != 1:
        raise ConfigError(f"{context}: unsupported schema_version")


@dataclass(frozen=True)
class ProjectConfig:
    repository: str
    default_branch: str
    implementation_repository: str
    phase: str
    library_root: str
    roadmap_root: str
    roadmap_document: str
    roadmap_targets: str
    roadmap_approved: bool
    lean: str
    tauceti: str
    mathlib: str
    sphere_packing_semantics: str
    reviews_branch: str
    archive_branch: str


@dataclass(frozen=True)
class AutomationPolicy:
    review_generation: bool
    posting: bool
    authoring: bool
    reporting: bool
    merging: bool
    mathematical_paths: tuple[str, ...]
    authorized_reviewers: tuple[str, ...]


@dataclass(frozen=True)
class OperatorPreferences:
    provider: str = "none"
    budget_usd: float = 0
    storage: str = "~/.local/state/sphereceti"


def parse_project(text: str) -> ProjectConfig:
    data = tomllib.loads(text)
    fields(data, {"schema_version", "project", "sources", "dependencies", "state"}, "profile")
    version(data, "profile")
    fields(data["project"], {"repository", "default_branch", "implementation_repository", "phase"}, "project")
    fields(data["sources"], {"library_root", "roadmap_root", "roadmap_document", "roadmap_targets", "roadmap_approved"}, "sources")
    fields(data["dependencies"], {"lean", "tauceti", "mathlib", "sphere_packing_semantics"}, "dependencies")
    fields(data["state"], {"reviews_branch", "archive_branch"}, "state")
    values = {key: value for section in ("project", "sources", "dependencies", "state")
              for key, value in data[section].items()}
    for key, value in values.items():
        if key == "roadmap_approved":
            if type(value) is not bool:
                raise ConfigError("roadmap_approved: expected boolean")
        else:
            nonempty(value, key)
    for key in ("repository", "implementation_repository"):
        if not REPOSITORY.fullmatch(values[key]):
            raise ConfigError(f"{key}: expected owner/repository")
    for key in ("tauceti", "mathlib", "sphere_packing_semantics"):
        if not COMMIT.fullmatch(values[key]):
            raise ConfigError(f"{key}: expected an exact full commit")
    for key in ("library_root", "roadmap_root", "roadmap_document", "roadmap_targets"):
        local_path(values[key], key)
    if values["phase"] not in ("scaffold", "roadmap"):
        raise ConfigError("phase: expected scaffold or roadmap")
    if values["roadmap_approved"] != (values["phase"] == "roadmap"):
        raise ConfigError("phase and roadmap_approved disagree")
    return ProjectConfig(**values)


def parse_policy(text: str) -> AutomationPolicy:
    data = tomllib.loads(text)
    names = set(AutomationPolicy.__dataclass_fields__)
    fields(data, {"schema_version"} | names, "policy")
    version(data, "policy")
    for name in names - {"mathematical_paths", "authorized_reviewers"}:
        if type(data[name]) is not bool:
            raise ConfigError(f"{name}: expected boolean")
    for name in ("mathematical_paths", "authorized_reviewers"):
        if not isinstance(data[name], list):
            raise ConfigError(f"{name}: expected a list")
        for item in data[name]:
            local_path(item, name) if name == "mathematical_paths" else nonempty(item, name)
            if name == "authorized_reviewers" and not re.fullmatch(r"(?:user|app):[1-9][0-9]*", item):
                raise ConfigError("authorized_reviewers: use immutable GitHub user:ID or app:ID")
        if len(set(data[name])) != len(data[name]):
            raise ConfigError(f"{name}: duplicate entry")
    if data["merging"] and not data["mathematical_paths"]:
        raise ConfigError("merging requires a separately approved nonempty path policy")
    if data["merging"] and not data["authorized_reviewers"]:
        raise ConfigError("merging requires authorized reviewers")
    return AutomationPolicy(**{name: tuple(data[name]) if isinstance(data[name], list) else data[name]
                              for name in names})


def parse_operator(text: str) -> OperatorPreferences:
    data = tomllib.loads(text)
    if set(data) - {"provider", "budget_usd", "storage"}:
        raise ConfigError("operator preferences permit only provider, budget_usd, and storage; policy cannot be overridden")
    prefs = OperatorPreferences(**data)
    nonempty(prefs.provider, "provider")
    nonempty(prefs.storage, "storage")
    if type(prefs.budget_usd) not in (int, float) or not 0 <= prefs.budget_usd < float("inf"):
        raise ConfigError("budget_usd: expected a finite nonnegative number")
    return prefs


def parse_source_lock(text: str) -> list[dict]:
    data = tomllib.loads(text)
    fields(data, {"schema_version", "components"}, "source lock")
    version(data, "source lock")
    if not isinstance(data["components"], list) or not data["components"]:
        raise ConfigError("source lock: expected components")
    names = set()
    for item in data["components"]:
        fields(item, {"name", "repository", "commit", "source_paths", "destination_paths",
                      "state", "license", "license_status", "adaptation"}, "component")
        for key in ("name", "repository", "commit", "state", "license", "license_status", "adaptation"):
            nonempty(item[key], key)
        if item["name"] in names:
            raise ConfigError("source lock: duplicate component")
        names.add(item["name"])
        if not REPOSITORY.fullmatch(item["repository"]) or not COMMIT.fullmatch(item["commit"]):
            raise ConfigError("source lock: expected repository and exact full commit")
        for key in ("source_paths", "destination_paths"):
            if not isinstance(item[key], list) or not item[key]:
                raise ConfigError(f"{key}: expected a nonempty list")
            for path in item[key]:
                local_path(path, key)
        if item["state"] not in ("planned", "reference-only", "design-adapted", "imported"):
            raise ConfigError("source lock: unknown component state")
        if item["license_status"] not in ("recorded", "unresolved"):
            raise ConfigError("source lock: unknown license status")
        if (item["license"] == "unresolved") != (item["license_status"] == "unresolved"):
            raise ConfigError("source lock: license and status disagree")
        if item["state"] in ("design-adapted", "imported") and item["license_status"] != "recorded":
            raise ConfigError("source lock: reuse terms must be recorded before adaptation/import")
    return data["components"]
