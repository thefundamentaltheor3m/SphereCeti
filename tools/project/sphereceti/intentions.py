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
import json
from datetime import datetime, timezone
import re
from urllib.parse import quote, urlencode

from .review_records import RecordError

SCHEMA = "sphereceti.intentions/v1"
LOOKUP_SCHEMA = "sphereceti.intend/v1"
LABEL = "intention"
TEMPLATE = "intention.yml"
# The format is defined by #134 (.github/ISSUE_TEMPLATE/intention.yml, scripts/intentions.py,
# docs/infrastructure/intentions.md). Mirrored here, and pinned by a test against #134's fixture:
# the headings GitHub renders from the form, keyed to the form's stable ids.
FIELDS = {"Target declaration": "target", "Roadmap item or layer": "roadmap_item",
          "Parent PR": "parent_pr", "Intended module": "module", "Expected duration": "duration"}
# The holder and expiry are recorded by #134's workflow in its own marker comments.
MARKER = "<!--sphereceti-intention:v1 "
BOT = "github-actions[bot]"
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


def parse_fields(body: str) -> dict:
    """Mirror of #134's scripts/intentions.py:parse_intention: form fields by stable form id, the
    target's fenced ```lean block unwrapped, and None for an empty or `_No response_` answer."""
    fields = {key: None for key in FIELDS.values()}
    parts = re.split(r"^### (.+?)[ \t]*$", (body or "").replace("\r\n", "\n"), flags=re.M)
    for heading, value in zip(parts[1::2], parts[2::2]):
        key = FIELDS.get(heading.strip())
        if key is None:
            continue
        value = value.strip()
        fence = re.fullmatch(r"(`{3,})[^\n]*\n([\s\S]*?)\n?\1", value)
        value = fence[2].strip() if fence else value
        fields[key] = None if value in ("", "_No response_") else value
    return fields


def target_names(target: str | None) -> list[str]:
    """The declaration a target block names: `theorem A.b ...`, or a bare name on its own."""
    if not target:
        return []
    for line in target.splitlines():
        text = line.strip()
        match = DECLARATION.match(text)
        if match and match.group(2):
            return [match.group(2).removeprefix("_root_.")]
        bare = re.fullmatch(r"[^\s:({\[⦃]+", text)
        if bare:
            return [text]
    return []


def instant(text: str) -> datetime:
    return datetime.strptime(text, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)


def claim_state(comments, assignees, now):
    """#134's rule: the latest marker by github-actions[bot] (type Bot) names the holder and expiry;
    a claim counts while that holder is still assigned. Markers by anyone else are ignored."""
    for comment in sorted(comments, key=lambda c: c.get("id", 0), reverse=True):
        user, body = comment.get("user") or {}, comment.get("body") or ""
        if user.get("login") != BOT or user.get("type") != "Bot" or not body.startswith(MARKER):
            continue
        try:
            data = json.loads(body[len(MARKER):].split("-->", 1)[0])
        except ValueError:
            continue
        if not isinstance(data, dict):
            continue
        if not data.get("holder") or data["holder"] not in assignees or not data.get("expires"):
            return None
        try:
            expired = instant(data["expires"]) <= now
        except (TypeError, ValueError):
            return None
        return {"holder": data["holder"], "expires": data["expires"], "expired": expired}
    return None


def parse_intention(issue, comments, now):
    fields = parse_fields(issue.get("body") or "")
    assignees = [a["login"] for a in issue.get("assignees") or [] if isinstance(a, dict) and a.get("login")]
    claim = claim_state(comments, assignees, now)
    state = "unclaimed" if not claim else "expired" if claim["expired"] else "claimed"
    item_text = fields["roadmap_item"] or ""
    parent = re.search(r"#?([0-9]+)", fields["parent_pr"] or "")
    return {"kind": "intention", "number": issue["number"], "url": issue.get("html_url") or issue.get("url"),
            "title": issue.get("title") or "", "holders": [claim["holder"]] if claim else [], "state": state,
            "expires": claim["expires"] if claim else None, "target": fields["target"],
            "declarations": target_names(fields["target"]),
            "modules": [module_path(fields["module"])] if fields["module"] else [],
            "items": list(dict.fromkeys(m.upper() for m in re.findall(r"\b([A-N][0-9]{1,2})\b", item_text))),
            "layers": list(dict.fromkeys(re.findall(r"\blayer\s*([0-9]+)", item_text, re.I))),
            "roadmap_item": fields["roadmap_item"], "duration": fields["duration"],
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
    """Labelled `intention`, or carrying the form's required headings: a contributor without triage
    rights cannot label an issue it creates through the API, so the body is the shared format."""
    labels = {(l.get("name") if isinstance(l, dict) else str(l)).lower() for l in issue.get("labels") or []}
    body = issue.get("body") or ""
    return LABEL in labels or all(re.search(rf"^###\s+{re.escape(h)}\s*$", body, re.M)
                                  for h in ("Target declaration", "Roadmap item or layer", "Intended module"))


def read_intentions(project, client, now):
    """Every open intention, whether filed through the issue form or by `sphereceti intend`, with
    its claim read from #134's workflow markers."""
    issues = pages(client, f"repos/{project.repository}/issues?state=open&per_page=100")
    found = []
    for issue in issues:
        if "pull_request" in issue or not is_intention(issue):
            continue
        comments = pages(client, f"repos/{project.repository}/issues/{issue['number']}/comments?per_page=100")
        found.append(parse_intention(issue, comments, now))
    return found


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


class RegistrationRefused(ValueError):
    """The request cannot become an intention (not a single declaration, or missing fields)."""


def same_declaration(a: str, b: str) -> bool:
    """Equal, or equal up to a namespace prefix one side did not spell out."""
    return a == b or a.endswith("." + b) or b.endswith("." + a)


def brief(work) -> dict:
    out = {k: work[k] for k in ("kind", "number", "url", "title", "modules", "items")}
    if work["kind"] == "intention":
        out.update(holders=work["holders"], state=work["state"], expires=work["expires"],
                   declarations=work["declarations"], target=work["target"])
    else:
        out.update(author=work["author"], draft=work["draft"], declarations=work["declarations"])
    return out


def exact(work, kind, target) -> bool:
    """An exact claim: the same declaration (#134 intentions name exactly one)."""
    return kind == "declaration" and any(same_declaration(target, d) for d in work["declarations"])


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
        if exact(w, kind, target):
            (claimed if live else related).append(brief(w))
        elif (module and module in w["modules"]) or (item and (item in w["items"] or (
                item.startswith("LAYER ") and item[6:] in w.get("layers", [])))):
            related.append(brief(w))
    claimed.sort(key=lambda w: (w["kind"] != "intention", w["number"]))
    prefill = {"title": f"[Intention]: {target}", "target": target if kind == "declaration" else None,
               "roadmap_item": item, "module": module}
    return {"schema": LOOKUP_SCHEMA, "repository": project.repository, "target": target, "kind": kind,
            "item": item, "module": module,
            "verdict": "claimed" if claimed else "no_exact_claim", "claimed": claimed, "related": related,
            "register_url": register_url(project, **prefill), "observed_at": observed["observed_at"],
            "registration": None}


def issue_body(target, item, module, parent, duration) -> str:
    """#134's form rendering exactly, so form-filed and CLI-filed intentions parse the same way."""
    values = {"target": f"```lean\n{target}\n```" if target else None, "roadmap_item": item,
              "parent_pr": f"#{parent}" if parent else None, "module": module, "duration": duration}
    return "\n\n".join(f"### {heading}\n\n{values[key] or '_No response_'}"
                        for heading, key in FIELDS.items()) + "\n"


def register(project, result, *, client=None, parent=None, duration=None, dry_run=False, now=None) -> dict:
    """Create #134's intention issue as the contributor, confirm it is first, then comment `claim`.

    Re-checks open intentions immediately before creating: an open intention with the same target
    (claimed or only registered) is shown with its link and nothing is written; one whose claim
    expired is claimed in place instead of duplicated. After creating, it reads them again: if an
    earlier one for the same target now exists, this one lost the race and is closed with a comment
    pointing at the winner (only our own issue is ever touched). Otherwise it comments `claim`
    (`claim <duration>`) so #134's workflow assigns the contributor.
    """
    if client is None:
        from .review_post import GitHub
        client = GitHub()
    now = now or datetime.now(timezone.utc)
    if result["verdict"] == "claimed":
        return {"state": "claimed", "winner": result["claimed"][0], "issue": None}
    target = result["target"]
    if result["kind"] != "declaration" or not result["item"] or not result["module"]:
        raise RegistrationRefused("an intention claims one declaration: give its name with --item and "
                                  "--module, which the form requires")
    payload = {"title": f"[Intention]: {target}", "labels": [LABEL],
               "body": issue_body(target, result["item"], result["module"], parent, duration)}
    command = "claim" + (f" {duration}" if duration else "")
    repo = project.repository

    def rivals():
        found = sorted((w for w in read_intentions(project, client, now) if exact(w, "declaration", target)),
                       key=lambda w: w["number"])
        return [w for w in found if w["state"] != "expired"], [w for w in found if w["state"] == "expired"]

    if dry_run:
        return {"state": "dry_run", "issue": None, "winner": None, "would_create": payload, "claim": command}
    live, expired = rivals()
    if live:
        return {"state": "claimed", "winner": brief(live[0]), "issue": None}
    if expired:  # take over the lapsed intention instead of opening a duplicate
        client.call(f"repos/{repo}/issues/{expired[0]['number']}/comments", payload={"body": command})
        return {"state": "claim_requested", "issue": {"number": expired[0]["number"], "url": expired[0]["url"]},
                "winner": None, "claim": command}
    created = client.call(f"repos/{repo}/issues", payload=payload)
    if not isinstance(created, dict) or type(created.get("number")) is not int:
        raise RecordError("GitHub did not confirm the new intention issue; check before retrying")
    mine = {"number": created["number"], "url": created.get("html_url")}
    live, _ = rivals()
    if not any(w["number"] == mine["number"] for w in live):
        return {"state": "unconfirmed", "issue": mine, "winner": None}
    earlier = [w for w in live if w["number"] < mine["number"]]
    if earlier:
        winner = brief(earlier[0])
        client.call(f"repos/{repo}/issues/{mine['number']}/comments", payload={
            "body": f"Duplicate of #{winner['number']}, which registered `{target}` first. Closing this one."})
        client.call(f"repos/{repo}/issues/{mine['number']}", payload={"state": "closed"}, method="PATCH")
        return {"state": "lost_race", "issue": mine, "winner": winner}
    client.call(f"repos/{repo}/issues/{mine['number']}/comments", payload={"body": command})
    return {"state": "registered", "issue": mine, "winner": None, "claim": command}


# --- Rendering -----------------------------------------------------------------------------------

def describe(w) -> str:
    if w["kind"] == "intention":
        who = ", ".join(w["holders"]) or "nobody"
        state = {"claimed": f"claimed by {who}" + (f" until {w['expires'][:10]}" if w["expires"] else ""),
                 "expired": f"EXPIRED claim by {who} (expired {(w['expires'] or '')[:10]})",
                 "unclaimed": "registered, unclaimed"}[w["state"]]
        first_line = ((w.get("target") or "").splitlines() or [""])[0]
        what = ", ".join(w["declarations"]) or first_line or w["title"]
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
        return (f"Registered intention #{r['issue']['number']}: {r['issue']['url']} and commented "
                f"`{r['claim']}`; the intentions workflow assigns you shortly.")
    if r["state"] == "claim_requested":
        return (f"An earlier intention for it had expired: commented `{r['claim']}` on "
                f"#{r['issue']['number']} ({r['issue']['url']}) instead of opening a duplicate.")
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
    q.add_argument("--duration", help="claim length for the `claim` comment, e.g. '3 weeks' (default: 30 days)")
    q.add_argument("--json", action="store_true")
    return p, q
