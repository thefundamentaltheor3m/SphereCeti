"""Announce a new PROGRESS.md section in Zulip, idempotently.

Idempotency is the whole design here, because the alternatives are both bad: post before the merge
and a failed merge announces work that never landed; post after the merge with no dedup and a
re-run of the workflow (or a retry after a lost response) posts the section twice.

So each section carries a stable id derived from its window, the id is embedded in the message, and
posting searches the topic for that id first. Re-running is then free, and a genuine transient
failure can be retried by re-running the workflow.

This runs in CI, not on the worker: the Zulip credentials are GitHub secrets, and the worker holds
none. It is also a separate job from the merge, so the App token that can write to the roadmap repo
and the Zulip key never sit in the same job.
"""

import pathlib
import re

from . import files, zulip

# The visible marker that makes a post findable. Zulip has no hidden metadata, and an HTML comment
# does not survive rendering, so the id is a short visible tag at the end of the message.
ID_PREFIX = "progress-log-id:"

MAX_MESSAGE_CHARS = 8000
ROADMAP_PARENTS = ("TauCetiRoadmap", "Completed")


def section_id(header):
    """A stable id for a window: `<Area>-<from7>-<to7>`."""
    return f"{header['roadmap']}-{header['from_sha'][:7]}-{header['to_sha'][:7]}"


def split_section(text):
    """`(header, prose)` for the appended text of a `PROGRESS.md` update.

    Note what `text` actually is: everything the update added to the file. For an area's *first*
    report that includes the file preamble ahead of the section, not just the section, so this cannot
    assume the text begins at the marker. It takes the prose after the last section marker's heading,
    which is right in both cases.
    """
    headers = files.parse_sections(text)
    if len(headers) != 1:
        raise files.FormatError(f"expected exactly one section, found {len(headers)}")
    m = re.search(r"<!--tauceti-progress:v1 .*?-->[^\n]*\n", text, flags=re.S)
    if not m:
        raise files.FormatError("no section marker found in the appended text")
    body = text[m.end():]
    # Drop the `## ...` heading too; Zulip gets a lead-in of our own.
    body = re.sub(r"\A\s*##[^\n]*\n", "", body).strip()
    return headers[0], body


def roadmap_file_url(area, filename, parent="TauCetiRoadmap"):
    """Canonical main-branch URL for a generated roadmap file."""
    if parent not in ROADMAP_PARENTS:
        raise ValueError(f"unexpected roadmap parent: {parent}")
    return f"https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/{parent}/{area}/{filename}"


def render_message(header, prose, roadmap_url=None, status_url=None, roadmap_parent="TauCetiRoadmap"):
    """The Zulip message for one section.

    Shape follows the review Kim gave Chris's bot: `TauCeti#NNN` linkifiers rather than markdown
    links, no claims about what Mathlib does or does not have, and no hidden trailing tag (Zulip
    renders none, so the id is visible).
    """
    area = header["roadmap"]
    prs = header["prs"]
    body = zulip.sanitize(prose)
    if len(body) > MAX_MESSAGE_CHARS:
        body = body[:MAX_MESSAGE_CHARS].rsplit("\n", 1)[0] + "\n\n(truncated; the full section is in `PROGRESS.md`)"
    progress_link = roadmap_url or roadmap_file_url(area, "PROGRESS.md", roadmap_parent)
    status_link = status_url or roadmap_file_url(area, "STATUS.md", roadmap_parent)
    return (
        f"**{area}** — progress on {len(prs)} merged pull requests "
        f"(`{header['from_sha'][:7]}` to `{header['to_sha'][:7]}`)\n\n"
        f"{body}\n\n"
        f"[Full progress log]({progress_link}) · [Current roadmap status]({status_link})\n"
        f"{ID_PREFIX}{section_id(header)}"
    )


def already_posted(client, channel, topic, sid):
    """Has this section already been announced?

    Searches for the id and then confirms the id actually appears in the message text, because
    Zulip's search is word-based and can return near matches.
    """
    needle = f"{ID_PREFIX}{sid}"
    for msg in client.search(channel, topic, sid):
        if needle in (msg.get("content") or ""):
            return msg
    return None


def run(section_file, channel=None, topic=None, roadmap_parent="TauCetiRoadmap", dry_run=False):
    """Post the section in `section_file`. Returns a process exit code.

    Raises on a transient failure rather than swallowing it, so the workflow run goes red and a
    retry is meaningful. The dedup check above is what makes that retry safe.
    """
    channel = channel or zulip.DEFAULT_CHANNEL
    topic = topic or zulip.DEFAULT_TOPIC

    text = pathlib.Path(section_file).read_text(encoding="utf-8")
    header, prose = split_section(text)
    sid = section_id(header)
    message = render_message(header, prose, roadmap_parent=roadmap_parent)

    if dry_run:
        print(f"[dry-run] would post to {channel} > {topic} as {sid}:\n\n{message}")
        return 0

    client = zulip.from_env()
    client.check(channel)

    existing = already_posted(client, channel, topic, sid)
    if existing is not None:
        print(f"already announced as message {existing['id']}; nothing to do")
        return 0

    mid = client.send(channel, topic, message)
    print(f"posted message {mid} for {sid}")
    return 0
