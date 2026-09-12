"""A minimal Zulip REST client: authenticate, search a topic, post, edit.

Adapted from `TauCeti/scripts/pr_status/zulip.py`, which is stdlib-only for the same reason this is
-- the whole toolchain runs with no PyPI dependencies. That file could not simply be imported: it
lives in another repository, under a human-owned `scripts/` directory. The duplication is about
ninety lines and is deliberate; the emoji-reconciliation machinery it carries is not reproduced.

The failure split is copied on purpose, because it is the right one:

* a **transient** hiccup (one 5xx, a network blip) is worth retrying, and
* a **configuration** break (missing creds, 401, a forbidden or unsubscribed bot) will never fix
  itself, so it must be loud.

One difference from the original. There, a failure to update an emoji is cosmetic and self-heals on
the next reconcile, so it exits 0. Here there is no later reconcile: an announcement that silently
fails is an announcement lost forever. So this module's caller raises instead of swallowing, and the
idempotency check below is what makes the resulting retry safe.
"""

import base64
import json
import os
import time
import urllib.error
import urllib.parse
import urllib.request

DEFAULT_SITE = "https://leanprover.zulipchat.com"
DEFAULT_CHANNEL = "Tau Ceti"
DEFAULT_TOPIC = "Progress logs"

ZWSP = "​"  # zero-width space, used to defuse mentions and linkifiers


class ConfigError(RuntimeError):
    """A persistent auth/permission/config failure that will not self-heal."""


class TransientError(RuntimeError):
    """A hiccup worth retrying."""


def sanitize(text):
    """Defuse Zulip markup that would do real harm if it came from generated prose.

    Two targets, and only two, so that ordinary text and wanted markup survive intact:

    * **`@`** starts a mention, which pings people. Always defused.
    * **A bare `#` followed by digits** hits the Lean Zulip's catch-all linkifier and silently turns
      into a link to some unrelated mathlib PR.

    Two things are deliberately *not* touched. A `#` preceded by an alphanumeric is a qualified
    linkifier -- `TauCeti#966`, `mathlib4#33505` -- which is exactly the form Kim asked for in place
    of markdown links, in any case. And a `#` not followed by a digit is a heading or ordinary
    punctuation, so defusing it would only corrupt the prose.

    A zero-width space after the sigil is invisible, so sanitised text still reads as written.
    """
    out = []
    for i, ch in enumerate(text):
        out.append(ch)
        if ch == "@":
            out.append(ZWSP)
        elif ch == "#":
            preceded_by_word = i > 0 and text[i - 1].isalnum()
            followed_by_digit = text[i + 1:i + 2].isdigit()
            if followed_by_digit and not preceded_by_word:
                out.append(ZWSP)
    return "".join(out)


class Zulip:
    def __init__(self, email, api_key, site=DEFAULT_SITE):
        self.base = site.rstrip("/") + "/api/v1"
        self.auth = "Basic " + base64.b64encode(f"{email}:{api_key}".encode()).decode()

    def _call(self, method, path, params=None, retries=3):
        data = urllib.parse.urlencode(params).encode() if params else None
        url = self.base + path
        if method in ("GET", "DELETE") and data:
            url += "?" + data.decode()
            data = None
        last = None
        for attempt in range(retries):
            req = urllib.request.Request(url, data=data, method=method)
            req.add_header("Authorization", self.auth)
            if data:
                req.add_header("Content-Type", "application/x-www-form-urlencoded")
            try:
                with urllib.request.urlopen(req, timeout=30) as resp:
                    return json.loads(resp.read().decode())
            except urllib.error.HTTPError as exc:
                payload = {}
                try:
                    payload = json.loads(exc.read().decode())
                except Exception:  # noqa: BLE001 - a non-JSON error body is itself information
                    pass
                detail = f"Zulip {method} {path}: {exc.code} {payload or exc.reason}"
                # 401, Zulip's own UNAUTHORIZED, or a 403 that Zulip itself answered (a JSON body)
                # are permission breaks. An opaque 403 with no body is usually a proxy, so treat
                # that as transient.
                if (exc.code == 401
                        or payload.get("code") == "UNAUTHORIZED"
                        or (exc.code == 403 and payload)):
                    raise ConfigError(detail) from exc
                last = detail
            except (urllib.error.URLError, TimeoutError) as exc:
                last = f"Zulip {method} {path}: {exc}"
            if attempt + 1 < retries:
                time.sleep(2 ** attempt)
        raise TransientError(last or f"Zulip {method} {path} failed")

    def my_user_id(self):
        return self._call("GET", "/users/me")["user_id"]

    def my_subscriptions(self):
        return [s["name"] for s in self._call("GET", "/users/me/subscriptions")["subscriptions"]]

    def search(self, channel, topic, query):
        """Recent messages in a topic matching `query`, raw markdown (so content compares exactly)."""
        narrow = [
            {"operator": "channel", "operand": channel},
            {"operator": "topic", "operand": topic},
            {"operator": "search", "operand": query},
        ]
        return self._call("GET", "/messages", {
            "anchor": "newest", "num_before": 200, "num_after": 0,
            "apply_markdown": "false", "narrow": json.dumps(narrow),
        })["messages"]

    def send(self, channel, topic, content):
        return self._call("POST", "/messages", {
            "type": "stream", "to": channel, "topic": topic, "content": content,
        })["id"]

    def check(self, channel):
        """Confirm the bot can act in `channel`. Raises ConfigError when it cannot."""
        uid = self.my_user_id()
        if channel not in self.my_subscriptions():
            raise ConfigError(
                f"bot (user {uid}) is not subscribed to channel {channel!r}; it cannot post there"
            )
        return uid


def from_env():
    """A client from `ZULIP_EMAIL` / `ZULIP_API_KEY` / `ZULIP_SITE`.

    Credentials are stripped: a stray newline in a GitHub secret is the single most common way this
    breaks, because the byte rides into the Basic-auth header and Zulip rejects the key as malformed.
    """
    email = (os.environ.get("ZULIP_EMAIL") or "").strip()
    key = (os.environ.get("ZULIP_API_KEY") or "").strip()
    site = (os.environ.get("ZULIP_SITE") or DEFAULT_SITE).strip()
    if not (email and key):
        raise ConfigError("ZULIP_EMAIL / ZULIP_API_KEY are not set")
    return Zulip(email, key, site)
