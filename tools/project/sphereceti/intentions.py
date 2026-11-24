# SPDX-License-Identifier: Apache-2.0
"""Work underway on proof targets: `intention` issues beside open proof PRs, and a lookup.

Modelled on TauCetiWorker's intentions board
(https://github.com/TauCetiProject/TauCetiWorker/blob/590c3a2a43a162b2ced728a7288ec84f4bde6ab1/tauceti_worker/intentions.py):
an intention is an open issue labelled `intention`, claimed by its assignees. SphereCeti adds
machine-readable fields and matches them, and the declarations open proof PRs add, precisely.
Independently written; read-only. A failed GitHub read raises, so a target is never reported
free on a guess.
"""
from __future__ import annotations

import base64
from datetime import datetime, timedelta, timezone
import re
from urllib.parse import quote, urlencode

from .review_records import RecordError

SCHEMA = "sphereceti.intentions/v1"
LOOKUP_SCHEMA = "sphereceti.intend/v1"
LABEL = "intention"
TEMPLATE = "intention.yml"
EXPIRY_DAYS = 14  # default claim lifetime for `sphereceti intend --register`; the form asks for a date
# Issue-form field ids (stable; used to prefill the form) and the labels GitHub renders as
# `### <label>` headings in the issue body (used to read it back). Both are part of the format.
FIELDS = {
    "declarations": "Declarations",
    "roadmap_item": "Roadmap item",
    "module": "Module",
    "parent_pr": "Parent PR",
    "expires": "Claim expires",
}
PLACEHOLDER = re.compile(r"^_?no response_?$", re.I)
COMMENT = re.compile(r"<!--.*?-->", re.S)
ITEM = re.compile(r"^[A-N][0-9]{1,2}$")
# A roadmap item named the way proof PRs cite it: "MIGRATION [PR D5]" or a "(Layer 3, D5 ...)" title.
ITEM_IN_TEXT = re.compile(r"\bPR ([A-N][0-9]{1,2})\b|\(Layer [0-9]+, ([A-N][0-9]{1,2})\b")
LAYER_IN_TEXT = re.compile(r"\bLayer ([0-9]+)\b")
DECLARATION = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance|inductive)\b\s*(?:\(priority\s*:=[^)]*\)\s*)?"
    r"([^\s:({\[⦃]+)?")
SCOPE = re.compile(r"^(?:(?:noncomputable|public)\s+)*(namespace|section|end|mutual)\b\s*([^\s]*)")


# --- Lean declarations added by a diff ----------------------------------------------------------

def added_lines(patch: str) -> set[int]:
    """Head-side line numbers of `+` lines in a unified diff."""
    added, line = set(), 0
    for text in patch.splitlines():
        hunk = re.match(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@", text)
        if hunk:
            line = int(hunk.group(1))
            continue
        if text.startswith("+"):
            added.add(line)
            line += 1
        elif text.startswith("-"):
            continue
        else:
            line += 1
    return added


def declarations(source: str, lines: set[int] | None = None) -> list[str]:
    """Fully qualified names of declarations starting on `lines` (all lines when None).

    Namespaces come from `namespace`/`section`/`end` in the whole head file; `_root_.` escapes them.
    Anonymous instances have no name and are skipped.
    """
    stack, found, depth = [], [], 0
    for number, raw in enumerate(source.splitlines(), 1):
        text = raw.strip()
        if text.startswith("--"):
            continue
        if depth or "/-" in text:  # block comments, including docstrings
            depth += text.count("/-") - text.count("-/")
            depth = max(depth, 0)
            if depth or text.endswith("-/"):
                continue
        scope = SCOPE.match(text)
        if scope:
            kind, name = scope.groups()
            if kind == "namespace":
                stack.append(("namespace", name))
            elif kind in ("section", "mutual"):
                stack.append((kind, name))
            elif stack:  # `end`, `end Name`
                stack.pop()
            continue
        match = DECLARATION.match(text)
        if not match or not match.group(2) or (lines is not None and number not in lines):
            continue
        name = match.group(2)
        if name.startswith("_root_."):
            full = name[len("_root_."):]
        else:
            prefix = ".".join(part for kind, scope_name in stack if kind == "namespace"
                              for part in [scope_name] if part)
            full = f"{prefix}.{name}" if prefix else name
        found.append(full)
    return list(dict.fromkeys(found))


def module_of(path: str) -> str:
    return path[:-len(".lean")].replace("/", ".")


# --- GitHub observations -------------------------------------------------------------------------

def pages(client, endpoint):
    value = client.call(endpoint, paginate=True)
    if not isinstance(value, list) or not value or any(not isinstance(p, list) for p in value):
        raise RecordError(f"incomplete GitHub response for {endpoint.split('?')[0]}")
    return [item for page in value for item in page]


def field(body: str, name: str) -> str:
    match = re.search(rf"^###\s+{re.escape(FIELDS[name])}\s*$\n(.*?)(?=^###\s|\Z)", body or "", re.S | re.M | re.I)
    if not match:
        return ""
    text = COMMENT.sub("", match.group(1)).strip()
    return "" if PLACEHOLDER.match(text) else text


def names(text: str) -> list[str]:
    parts = re.split(r"[\n,]+", text)
    return [p.strip().strip("-*` ").strip() for p in parts if p.strip().strip("-*` ").strip()]


def parse_intention(issue, now):
    body = issue.get("body") or ""
    expires_text = field(body, "expires")
    expires = None
    if expires_text:
        try:
            expires = datetime.strptime(expires_text.split()[0], "%Y-%m-%d").replace(
                hour=23, minute=59, second=59, tzinfo=timezone.utc)
        except ValueError:
            expires = None
    holders = [a["login"] for a in issue.get("assignees") or [] if isinstance(a, dict) and a.get("login")]
    state = "unclaimed" if not holders else "expired" if expires and expires < now else "claimed"
    module = field(body, "module")
    item = field(body, "roadmap_item")
    parent = re.search(r"#?([0-9]+)", field(body, "parent_pr") or "")
    return {"kind": "intention", "number": issue["number"], "url": issue.get("html_url") or issue.get("url"),
            "title": issue.get("title") or "", "holders": holders, "state": state,
            "expires": expires_text or None, "declarations": names(field(body, "declarations")),
            "modules": [module_path(module)] if module else [], "items": [item.upper()] if item else [],
            "parent_pr": int(parent.group(1)) if parent else None}


def module_path(value: str) -> str:
    value = value.strip().strip("`")
    if value.endswith(".lean") or "/" in value:
        return value
    return value.replace(".", "/") + ".lean"


def items_in(title: str, body: str = "") -> list[str]:
    """Roadmap items a PR cites: from its title's "(Layer N, X ...)" when present, else its body's
    "PR X" citations (e.g. "MIGRATION [PR D5]")."""
    for text in (title or "", body or ""):
        found = [a or b for a, b in ITEM_IN_TEXT.findall(text)]
        if found:
            return list(dict.fromkeys(found))
    return []


def observe_pr(client, project, pr):
    repo, number, head = project.repository, pr["number"], pr["head"]["sha"]
    files = pages(client, f"repos/{repo}/pulls/{number}/files?per_page=100")
    modules, declared, incomplete = [], [], []
    for f in files:
        path, status = f.get("filename") or "", f.get("status")
        if not (path.startswith(project.library_root + "/") and path.endswith(".lean")) or status == "removed":
            continue
        modules.append(path)
        patch = f.get("patch")
        if patch is None and status != "added":
            incomplete.append(path)  # GitHub omits the patch of very large diffs
            continue
        content = client.call(f"repos/{repo}/contents/{quote(path)}?ref={head}")
        if not isinstance(content, dict) or content.get("encoding") != "base64":
            raise RecordError(f"unreadable head of {path} in PR #{number}")
        source = base64.b64decode(content["content"]).decode("utf-8", "replace")
        lines = None if patch is None else added_lines(patch)
        declared += [{"name": n, "module": path} for n in declarations(source, lines)]
    return {"kind": "pull_request", "number": number, "url": pr.get("html_url"), "title": pr.get("title") or "",
            "author": (pr.get("user") or {}).get("login"), "draft": bool(pr.get("draft")), "head": head,
            "modules": modules, "declarations": [d["name"] for d in declared], "declared": declared,
            "items": items_in(pr.get("title"), pr.get("body")), "layers": list(dict.fromkeys(LAYER_IN_TEXT.findall(pr.get("title") or ""))),
            "incomplete": incomplete}


def observe(project, *, client=None, now=None) -> dict:
    """Open intentions and open proof PRs (those touching library modules)."""
    if client is None:
        from .review_post import GitHub
        client = GitHub()
    now = now or datetime.now(timezone.utc)
    repo = project.repository
    intentions = read_intentions(project, client, now)
    prs = []
    for pr in pages(client, f"repos/{repo}/pulls?state=open&per_page=100"):
        observed = observe_pr(client, project, pr)
        if observed["modules"]:
            prs.append(observed)
    return {"schema": SCHEMA, "repository": repo, "observed_at": now.strftime("%Y-%m-%dT%H:%M:%SZ"),
            "intentions": intentions, "pull_requests": prs, "groups": groups(intentions, prs),
            "register_url": register_url(project)}


def is_intention(issue) -> bool:
    """Labelled `intention`, or carrying the form's headings: a contributor without triage rights
    cannot label an issue it creates through the API, so the body is the shared format."""
    labels = {(l.get("name") if isinstance(l, dict) else str(l)).lower() for l in issue.get("labels") or []}
    body = issue.get("body") or ""
    return LABEL in labels or all(re.search(rf"^###\s+{re.escape(FIELDS[k])}\s*$", body, re.M)
                                  for k in ("declarations", "roadmap_item", "module"))


def read_intentions(project, client, now):
    """Every open intention, whether filed through the issue form or by `sphereceti intend`."""
    issues = pages(client, f"repos/{project.repository}/issues?state=open&per_page=100")
    return [parse_intention(i, now) for i in issues if "pull_request" not in i and is_intention(i)]


def groups(intentions, prs):
    """Group work by roadmap item, else by module; one entry may appear under several keys."""
    keyed = {}
    for work in intentions + prs:
        keys = [("item", i) for i in work["items"]] or [("module", m) for m in work["modules"]] or [("other", "")]
        for key in keys:
            keyed.setdefault(key, []).append((work["kind"], work["number"]))
    order = sorted(keyed, key=lambda k: ({"item": 0, "module": 1, "other": 2}[k[0]], k[1]))
    return [{"kind": kind, "key": key,
             "intentions": [n for k, n in keyed[(kind, key)] if k == "intention"],
             "pull_requests": [n for k, n in keyed[(kind, key)] if k == "pull_request"]} for kind, key in order]


def register_url(project, **prefill) -> str:
    query = {"template": TEMPLATE, "labels": LABEL, **{k: v for k, v in prefill.items() if v}}
    return f"https://github.com/{project.repository}/issues/new?{urlencode(query)}"


# --- The lookup ----------------------------------------------------------------------------------

def classify(target: str, kind: str | None = None) -> str:
    if kind:
        return kind
    if ITEM.match(target) or re.match(r"^Layer [0-9]+$", target):
        return "item"
    if target.endswith(".lean") or "/" in target:
        return "module"
    parts = target.split(".")
    if len(parts) > 1 and parts[0] == "SphereCeti" and all(p[:1].isupper() for p in parts):
        return "module"
    return "declaration"


def same_declaration(a: str, b: str) -> bool:
    """Equal, or equal up to a namespace prefix one side did not spell out."""
    return a == b or a.endswith("." + b) or b.endswith("." + a)


def brief(work) -> dict:
    out = {k: work[k] for k in ("kind", "number", "url", "title", "modules", "items")}
    if work["kind"] == "intention":
        out.update(holders=work["holders"], state=work["state"], expires=work["expires"],
                   declarations=work["declarations"])
    else:
        out.update(author=work["author"], draft=work["draft"], declarations=work["declarations"])
    return out


def exact(work, kind, target, module, item) -> bool:
    """An exact claim: the same declaration, or a whole-module / whole-item intention."""
    if kind == "declaration":
        return any(same_declaration(target, d) for d in work["declarations"])
    if work["kind"] != "intention" or work["declarations"]:
        return False
    if kind == "module":
        return module in work["modules"]
    return not work["modules"] and item in work["items"]


def lookup(project, target, *, observed=None, client=None, kind=None, item=None, module=None) -> dict:
    """Has `target` an exact claim (an open intention or an open PR adding it)? And what is related?

    For callers that must decide before spending model time (the planner, automated authoring).
    "No exact claim" is not "free": a PR from before intentions may prove the same result under
    another name, so related work (same module or roadmap item) is always listed. Raises
    RecordError when GitHub cannot be read: an unknown board never yields "no exact claim".
    """
    observed = observed or observe(project, client=client)
    kind = classify(target, kind)
    item = (item or (target if kind == "item" else "")).upper() or None
    module = module_path(module or target) if (module or kind == "module") else None
    claimed, related = [], []
    for w in observed["intentions"] + observed["pull_requests"]:
        live = not (w["kind"] == "intention" and w["state"] == "expired")
        if exact(w, kind, target, module, item):
            (claimed if live else related).append(brief(w))
        elif (module and module in w["modules"]) or (item and (item in w["items"] or (
                item.startswith("LAYER ") and item[6:] in w.get("layers", [])))):
            related.append(brief(w))
    claimed.sort(key=lambda w: (w["kind"] != "intention", w["number"]))
    prefill = {"declarations": target if kind == "declaration" else None,
               "roadmap_item": item, "module": module, "title": f"Intention: {target}"}
    return {"schema": LOOKUP_SCHEMA, "repository": project.repository, "target": target, "kind": kind,
            "item": item, "module": module,
            "verdict": "claimed" if claimed else "no_exact_claim", "claimed": claimed, "related": related,
            "register_url": register_url(project, **prefill), "observed_at": observed["observed_at"],
            "registration": None}


def issue_body(declarations_text, item, module, parent, expires) -> str:
    """The issue form's rendering, so form-filed and CLI-filed intentions parse the same way."""
    values = {"declarations": declarations_text, "roadmap_item": item, "module": module,
              "parent_pr": f"#{parent}" if parent else None, "expires": expires}
    return "\n\n".join(f"### {FIELDS[k]}\n\n{values[k] or '_No response_'}" for k in FIELDS) + "\n"


def register(project, result, *, client=None, parent=None, expires=None, dry_run=False, now=None) -> dict:
    """Create the intention issue as the contributor, then confirm it is the earliest claim.

    Re-checks open intentions immediately before creating (no write if an exact claim appeared)
    and again after creating it. If an earlier intention for the same target now exists, this one
    lost the race: it is closed with a comment pointing at the winner (only our own issue is ever
    touched) and the winner is reported.
    """
    if client is None:
        from .review_post import GitHub
        client = GitHub()
    now = now or datetime.now(timezone.utc)
    if result["verdict"] == "claimed":
        return {"state": "claimed", "winner": result["claimed"][0], "issue": None}
    target, kind = result["target"], result["kind"]
    expires = expires or (now + timedelta(days=EXPIRY_DAYS)).strftime("%Y-%m-%d")
    title = f"Intention: {target}"
    body = issue_body(target if kind == "declaration" else None, result["item"], result["module"], parent, expires)
    payload = {"title": title, "body": body, "labels": [LABEL]}

    def rivals():
        found = [w for w in read_intentions(project, client, now)
                 if w["state"] != "expired" and exact(w, kind, target, result["module"], result["item"])]
        return sorted(found, key=lambda w: w["number"])

    if dry_run:
        return {"state": "dry_run", "issue": None, "winner": None, "would_create": payload}
    before = rivals()
    if before:
        return {"state": "claimed", "winner": brief(before[0]), "issue": None}
    created = client.call(f"repos/{project.repository}/issues", payload=payload)
    if not isinstance(created, dict) or type(created.get("number")) is not int:
        raise RecordError("GitHub did not confirm the new intention issue; check before retrying")
    mine = {"number": created["number"], "url": created.get("html_url")}
    after = rivals()
    earlier = [w for w in after if w["number"] < mine["number"]]
    if not any(w["number"] == mine["number"] for w in after):
        return {"state": "unconfirmed", "issue": mine, "winner": None}
    if earlier:
        winner = brief(earlier[0])
        client.call(f"repos/{project.repository}/issues/{mine['number']}/comments", payload={
            "body": f"Duplicate of #{winner['number']}, which claimed `{target}` first. Closing this one."})
        client.call(f"repos/{project.repository}/issues/{mine['number']}", payload={"state": "closed"},
                    method="PATCH")
        return {"state": "lost_race", "issue": mine, "winner": winner}
    return {"state": "registered", "issue": mine, "winner": None}


# --- Rendering -----------------------------------------------------------------------------------

def describe(w) -> str:
    if w["kind"] == "intention":
        who = ", ".join(w["holders"]) or "nobody"
        state = {"claimed": f"claimed by {who}" + (f" until {w['expires']}" if w["expires"] else ""),
                 "expired": f"EXPIRED claim by {who} (expired {w['expires']})",
                 "unclaimed": "registered, unclaimed"}[w["state"]]
        what = ", ".join(w["declarations"]) or ", ".join(w["modules"]) or ", ".join(w["items"]) or w["title"]
        return f"intention #{w['number']} {state}: {what}"
    adds = ", ".join(w["declarations"][:6]) + (f", … ({len(w['declarations'])} in all)"
                                                if len(w["declarations"]) > 6 else "")
    draft = " (draft)" if w["draft"] else ""
    return (f"PR #{w['number']}{draft} by {w['author']} \"{w['title'][:70]}\" · {', '.join(w['modules'])}"
            + (f" · adds {adds}" if adds else ""))


def render(report) -> str:
    by_number = {(w["kind"], w["number"]): w for w in report["intentions"] + report["pull_requests"]}
    lines = [f"Work underway in {report['repository']} (observed {report['observed_at']}): "
             f"{len(report['intentions'])} intention(s), {len(report['pull_requests'])} open proof PR(s)"]
    for g in report["groups"]:
        title = {"item": f"Roadmap item {g['key']}", "module": f"Module {g['key']}", "other": "Other"}[g["kind"]]
        lines.append(f"{title}:")
        for number in g["intentions"]:
            lines.append("  " + describe(by_number[("intention", number)]))
        for number in g["pull_requests"]:
            lines.append("  " + describe(by_number[("pull_request", number)]))
    lines.append(f"Register an intention: {report['register_url']}")
    return "\n".join(lines)


def render_lookup(result) -> str:
    target = f"{result['kind']} {result['target']}"
    if result["verdict"] == "claimed":
        lines = [f"Already claimed: {target}"] + ["  " + describe_brief(w) for w in result["claimed"]]
        if result["related"]:
            lines += ["Related work:"] + ["  " + describe_brief(w) for w in result["related"]]
        return "\n".join(lines)
    lines = [f"No exact claim found for {target}."]
    if result["related"]:
        lines += ["Related open PRs and intentions (same module or roadmap item); check that none of them "
                  "already proves your result under another name:"]
        lines += ["  " + describe_brief(w) for w in result["related"]]
    else:
        lines.append("No related open PR or intention either (same module or roadmap item).")
    registration = result.get("registration")
    if registration is None:
        lines.append(f"Register it: {result['register_url']}  (or rerun with --register)")
    else:
        lines.append(render_registration(registration))
    return "\n".join(lines)


def render_registration(r) -> str:
    if r["state"] == "registered":
        return f"Registered intention #{r['issue']['number']}: {r['issue']['url']}"
    if r["state"] == "dry_run":
        return "Dry run: would create an intention issue titled " + repr(r["would_create"]["title"])
    if r["state"] == "claimed":
        return f"Not registered: it was just claimed by {describe_brief(r['winner'])}"
    if r["state"] == "lost_race":
        return (f"Lost the race: {describe_brief(r['winner'])} claimed it first. Your issue "
                f"#{r['issue']['number']} was closed as its duplicate.")
    return f"Created #{r['issue']['number']} but could not confirm it on the board; check {r['issue']['url']}"


def describe_brief(w) -> str:
    full = {"layers": [], "author": None, "draft": False, "holders": [], "state": None, "expires": None, **w}
    return describe(full) + (f" · {full['url']}" if full.get("url") else "")


def add_parser(commands):
    p = commands.add_parser("intentions", help="read-only: claimed proof targets beside open proof PRs")
    p.add_argument("--json", action="store_true")
    q = commands.add_parser("intend", help="read-only: is this declaration, module or roadmap item already underway?")
    q.add_argument("target", help="a Lean declaration name, a module path, or a roadmap item such as D5")
    q.add_argument("--kind", choices=("declaration", "module", "item"), help="override the guessed target kind")
    q.add_argument("--item", help="the roadmap item a declaration belongs to (e.g. D5), to show related work")
    q.add_argument("--module", help="the module a declaration belongs to, to show related work")
    q.add_argument("--register", action="store_true",
                   help="create the intention issue (as you, via gh) when no exact claim is found")
    q.add_argument("--dry-run", action="store_true", help="with --register: show the issue, create nothing")
    q.add_argument("--parent-pr", type=int, help="the PR this work builds on")
    q.add_argument("--expires", help="claim expiry date, YYYY-MM-DD (default: 14 days from today)")
    q.add_argument("--json", action="store_true")
    return p, q
