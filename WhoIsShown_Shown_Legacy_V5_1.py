import requests
import json
import time
import re
import logging
import logging.handlers
import gc
import os
import sys
import random
import string
import threading
from datetime import datetime, timedelta
# Coloured reply + inline buttons require pyTelegramBotAPI>=4.31.0 (Bot API 9.4).
from telebot import TeleBot, types
from telebot.types import InlineKeyboardMarkup, InlineKeyboardButton, InputFile, MessageEntity
from threading import Lock, Thread
from concurrent.futures import ThreadPoolExecutor
import urllib3
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
import hashlib
import html as _html
from collections import OrderedDict
import heapq
import io
import tempfile
import subprocess
import signal
import shutil
from urllib.parse import quote as _urlquote

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# ============================================================
#  EMBEDDED STORE — Mongo-compatible documents + readable
#  user cards posted to a Telegram channel. Self-contained:
#  no pymongo, no external module, this file only.
# ============================================================
import sqlite3
import atexit


import atexit
import json
import os
import random
import re
import sqlite3
import threading
import time
import traceback
from collections import OrderedDict


ASCENDING = 1
DESCENDING = -1

_MAX_MSG_CHARS = 3800
_MAX_LINES_PER_MSG = 40


# ══════════════════════════════════════════════════════════════
#  Exceptions / sentinels (pymongo drop-in)
# ══════════════════════════════════════════════════════════════

class DuplicateKeyError(Exception):
    """Raised when a unique index is violated."""


class OperationFailure(Exception):
    """Raised for malformed queries/updates."""


class ReturnDocument:
    BEFORE = 0
    AFTER = 1


class ObjectId(str):
    """String-compatible stand-in for bson.ObjectId (ids are stored as strings)."""

    def __new__(cls, value=None):
        if value is None:
            value = "%024x" % random.getrandbits(96)
        return super().__new__(cls, str(value))

    @property
    def binary(self):
        return str(self)


class InsertOneResult:
    __slots__ = ("acknowledged", "inserted_id")

    def __init__(self, inserted_id):
        self.acknowledged = True
        self.inserted_id = inserted_id


class InsertManyResult:
    __slots__ = ("acknowledged", "inserted_ids")

    def __init__(self, ids):
        self.acknowledged = True
        self.inserted_ids = ids


class UpdateResult:
    __slots__ = ("acknowledged", "matched_count", "modified_count", "upserted_id", "raw_result")

    def __init__(self, matched=0, modified=0, upserted=None):
        self.acknowledged = True
        self.matched_count = matched
        self.modified_count = modified
        self.upserted_id = upserted
        self.raw_result = {"n": matched, "nModified": modified, "upserted": upserted}


class DeleteResult:
    __slots__ = ("acknowledged", "deleted_count", "raw_result")

    def __init__(self, deleted=0):
        self.acknowledged = True
        self.deleted_count = deleted
        self.raw_result = {"n": deleted}


# ══════════════════════════════════════════════════════════════
#  Value helpers
# ══════════════════════════════════════════════════════════════

_MISSING = object()


def _resolve(doc, path):
    """Dot-path lookup: 'a.b.c' -> doc['a']['b']['c']."""
    cur = doc
    for part in str(path).split("."):
        if isinstance(cur, dict):
            if part not in cur:
                return _MISSING
            cur = cur[part]
        elif isinstance(cur, list):
            try:
                cur = cur[int(part)]
            except (ValueError, IndexError):
                return _MISSING
        else:
            return _MISSING
    return cur


def _assign(doc, path, value):
    parts = str(path).split(".")
    cur = doc
    for part in parts[:-1]:
        nxt = cur.get(part)
        if not isinstance(nxt, dict):
            nxt = {}
            cur[part] = nxt
        cur = nxt
    cur[parts[-1]] = value


def _unassign(doc, path):
    parts = str(path).split(".")
    cur = doc
    for part in parts[:-1]:
        cur = cur.get(part)
        if not isinstance(cur, dict):
            return
    cur.pop(parts[-1], None)


def _eq(a, b):
    """Loose equality — tolerates ObjectId/str/int id mismatches."""
    if a is b:
        return True
    if isinstance(a, bool) or isinstance(b, bool):
        return a == b
    try:
        if a == b:
            return True
    except Exception:
        pass
    if isinstance(a, (str, int, float)) and isinstance(b, (str, int, float)):
        return str(a) == str(b)
    return False


def _cmp_key(v):
    if v is None:
        return (0, 0)
    if isinstance(v, bool):
        return (1, int(v))
    if isinstance(v, (int, float)):
        return (2, v)
    return (3, str(v))


def _sort_docs(docs, sort_spec):
    if not sort_spec:
        return docs
    if isinstance(sort_spec, str):
        sort_spec = [(sort_spec, ASCENDING)]
    elif isinstance(sort_spec, tuple) and len(sort_spec) == 2 and not isinstance(sort_spec[0], (list, tuple)):
        sort_spec = [sort_spec]
    out = list(docs)
    for field, direction in reversed(list(sort_spec)):
        direction = direction if direction in (1, -1) else 1
        out.sort(key=lambda d: _cmp_key(_resolve(d, field) if _resolve(d, field) is not _MISSING else None),
                 reverse=(direction == DESCENDING))
    return out


# ── filter engine ──────────────────────────────────────────────

_OPS = {"$eq", "$ne", "$gt", "$gte", "$lt", "$lte", "$in", "$nin",
        "$regex", "$options", "$exists", "$size", "$all", "$not"}


def _match_value(value, cond):
    if isinstance(cond, dict) and any(k in _OPS for k in cond):
        return _match_ops(value, cond)
    if isinstance(cond, re.Pattern):
        return isinstance(value, str) and bool(cond.search(value))
    if value is _MISSING:
        return cond is None
    return _eq(value, cond)


def _match_ops(value, cond):
    exists = value is not _MISSING
    for op, arg in cond.items():
        if op == "$options":
            continue
        if op == "$eq":
            if not (exists and _eq(value, arg)):
                return False
        elif op == "$ne":
            if exists and _eq(value, arg):
                return False
        elif op == "$gt":
            if not exists or (value is not None and arg is not None and not value > arg):
                return False
        elif op == "$gte":
            if not exists or (value is not None and arg is not None and not value >= arg):
                return False
        elif op == "$lt":
            if not exists or (value is not None and arg is not None and not value < arg):
                return False
        elif op == "$lte":
            if not exists or (value is not None and arg is not None and not value <= arg):
                return False
        elif op == "$in":
            if not exists or not any(_eq(value, c) if not isinstance(c, re.Pattern)
                                     else (isinstance(value, str) and c.search(value)) for c in arg):
                return False
        elif op == "$nin":
            if exists and any(_eq(value, c) if not isinstance(c, re.Pattern)
                              else (isinstance(value, str) and c.search(value)) for c in arg):
                return False
        elif op == "$regex":
            flags = re.I if "i" in str(cond.get("$options", "")) else 0
            pattern = arg if isinstance(arg, re.Pattern) else re.compile(str(arg), flags)
            if not exists or not isinstance(value, str) or not pattern.search(value):
                return False
        elif op == "$exists":
            if bool(arg) != exists:
                return False
        elif op == "$size":
            if not exists or not isinstance(value, (list, tuple)) or len(value) != arg:
                return False
        elif op == "$all":
            if not exists or not isinstance(value, list):
                return False
            if not all(any(_eq(v, c) for v in value) for c in arg):
                return False
        elif op == "$not":
            if _match_value(value, arg):
                return False
        else:
            raise OperationFailure(f"unsupported operator {op}")
    return True


def _eval_expr(doc, expr):
    """Tiny aggregation-expression evaluator (enough for $expr inside filters)."""
    if isinstance(expr, dict):
        if len(expr) != 1:
            raise OperationFailure("expression must have exactly one key")
        op, arg = next(iter(expr.items()))
        if op == "$literal":
            return arg
        if op == "$ifNull":
            val = _eval_expr(doc, arg[0])
            return _eval_expr(doc, arg[1]) if val is None or val is _MISSING else val
        if op in ("$add", "$subtract", "$multiply", "$divide", "$mod"):
            vals = [_eval_expr(doc, a) for a in arg]
            vals = [0 if v is _MISSING or v is None else v for v in vals]
            if op == "$add":
                return sum(vals)
            if op == "$subtract":
                return vals[0] - vals[1]
            if op == "$multiply":
                out = 1
                for v in vals:
                    out *= v
                return out
            if op == "$divide":
                return vals[0] / vals[1] if vals[1] else None
            return vals[0] % vals[1] if vals[1] else None
        if op in ("$eq", "$ne", "$gt", "$gte", "$lt", "$lte"):
            a, b = (_eval_expr(doc, arg[0]), _eval_expr(doc, arg[1]))
            a = None if a is _MISSING else a
            b = None if b is _MISSING else b
            return {"$eq": _eq(a, b), "$ne": not _eq(a, b),
                    "$gt": a is not None and b is not None and a > b,
                    "$gte": a is not None and b is not None and a >= b,
                    "$lt": a is not None and b is not None and a < b,
                    "$lte": a is not None and b is not None and a <= b}[op]
        raise OperationFailure(f"unsupported expression operator {op}")
    if isinstance(expr, str) and expr.startswith("$"):
        val = _resolve(doc, expr[1:])
        return None if val is _MISSING else val
    return expr


def _matches(doc, flt):
    if not flt:
        return True
    for key, cond in flt.items():
        if key == "$or":
            if not any(_matches(doc, sub) for sub in cond):
                return False
        elif key == "$and":
            if not all(_matches(doc, sub) for sub in cond):
                return False
        elif key == "$nor":
            if any(_matches(doc, sub) for sub in cond):
                return False
        elif key == "$expr":
            if not _eval_expr(doc, cond):
                return False
        elif key == "$comment":
            continue
        else:
            if not _match_value(_resolve(doc, key), cond):
                return False
    return True


# ── projection / update engine ─────────────────────────────────

def _project(doc, projection):
    if not projection:
        return doc
    include = {k for k, v in projection.items() if v and k != "_id"}
    exclude = {k for k, v in projection.items() if not v}
    if include:
        out = {"_id": doc.get("_id")} if projection.get("_id", 1) and "_id" in doc else {}
        for k in include:
            val = _resolve(doc, k)
            if val is not _MISSING:
                _assign(out, k, val)
        return out
    out = dict(doc)
    for k in exclude:
        _unassign(out, k)
    return out


_UPDATE_OPS = {"$set", "$unset", "$inc", "$mul", "$min", "$max", "$rename",
               "$push", "$addToSet", "$pop", "$pull", "$setOnInsert", "$currentDate"}


def _apply_update(doc, update, inserting=False):
    if not any(k.startswith("$") for k in update):
        # replacement-style update
        new = dict(update)
        new.setdefault("_id", doc.get("_id"))
        return new
    for op, payload in update.items():
        if op == "$set":
            for k, v in payload.items():
                _assign(doc, k, v)
        elif op == "$setOnInsert":
            if inserting:
                for k, v in payload.items():
                    if _resolve(doc, k) is _MISSING:
                        _assign(doc, k, v)
        elif op == "$unset":
            for k in payload:
                _unassign(doc, k)
        elif op == "$inc":
            for k, v in payload.items():
                cur = _resolve(doc, k)
                _assign(doc, k, (0 if cur is _MISSING or cur is None else cur) + v)
        elif op == "$mul":
            for k, v in payload.items():
                cur = _resolve(doc, k)
                _assign(doc, k, (0 if cur is _MISSING or cur is None else cur) * v)
        elif op == "$min":
            for k, v in payload.items():
                cur = _resolve(doc, k)
                if cur is _MISSING or cur is None or v < cur:
                    _assign(doc, k, v)
        elif op == "$max":
            for k, v in payload.items():
                cur = _resolve(doc, k)
                if cur is _MISSING or cur is None or v > cur:
                    _assign(doc, k, v)
        elif op == "$rename":
            for k, v in payload.items():
                cur = _resolve(doc, k)
                if cur is not _MISSING:
                    _unassign(doc, k)
                    _assign(doc, v, cur)
        elif op == "$push":
            for k, v in payload.items():
                cur = _resolve(doc, k)
                arr = list(cur) if isinstance(cur, list) else []
                if isinstance(v, dict) and "$each" in v:
                    arr.extend(v["$each"])
                else:
                    arr.append(v)
                _assign(doc, k, arr)
        elif op == "$addToSet":
            for k, v in payload.items():
                cur = _resolve(doc, k)
                arr = list(cur) if isinstance(cur, list) else []
                values = v["$each"] if isinstance(v, dict) and "$each" in v else [v]
                for item in values:
                    if not any(_eq(item, e) for e in arr):
                        arr.append(item)
                _assign(doc, k, arr)
        elif op == "$pop":
            for k, v in payload.items():
                cur = _resolve(doc, k)
                if isinstance(cur, list) and cur:
                    arr = list(cur)
                    arr.pop(0 if v == -1 else -1)
                    _assign(doc, k, arr)
        elif op == "$pull":
            for k, v in payload.items():
                cur = _resolve(doc, k)
                if isinstance(cur, list):
                    _assign(doc, k, [e for e in cur if not _match_value(e, v)])
        elif op == "$currentDate":
            for k in payload:
                _assign(doc, k, time.strftime("%Y-%m-%d %H:%M:%S"))
        elif op.startswith("$"):
            raise OperationFailure(f"unsupported update operator {op}")
    return doc


# ══════════════════════════════════════════════════════════════
#  Cursor
# ══════════════════════════════════════════════════════════════

class Cursor:
    def __init__(self, docs_fn, mapper=None):
        self._docs_fn = docs_fn          # returns list[dict] already filtered
        self._mapper = mapper
        self._sort = None
        self._limit = None
        self._skip = 0
        self._cache = None

    def sort(self, key_or_list, direction=None):
        self._sort = key_or_list if direction is None else [(key_or_list, direction)]
        self._cache = None
        return self

    def limit(self, n):
        self._limit = n
        self._cache = None
        return self

    def skip(self, n):
        self._skip = n or 0
        self._cache = None
        return self

    def _materialise(self):
        if self._cache is None:
            docs = _sort_docs(self._docs_fn(), self._sort)
            if self._skip:
                docs = docs[self._skip:]
            if self._limit is not None and self._limit >= 0:
                docs = docs[:self._limit]
            self._cache = [self._mapper(d) if self._mapper else d for d in docs]
        return self._cache

    def __iter__(self):
        return iter(self._materialise())

    def __len__(self):
        return len(self._materialise())

    def __getitem__(self, i):
        return self._materialise()[i]

    def __bool__(self):
        return bool(self._materialise())

    def count(self):
        return len(self._materialise())

    def to_list(self, length=None):
        data = self._materialise()
        return data if length is None else data[:length]

    def distinct(self, field):
        seen, out = set(), []
        for d in self._materialise():
            v = _resolve(d, field)
            if v is _MISSING:
                continue
            marker = json.dumps(v, default=str, sort_keys=True)
            if marker not in seen:
                seen.add(marker)
                out.append(v)
        return out


# ══════════════════════════════════════════════════════════════
#  Readable user cards (what non-coders see in the channel)
# ══════════════════════════════════════════════════════════════

_DIVIDER = "─" * 26

_USER_FIELDS = (
    ("first_name",       "Name"),
    ("username",         "Username"),
    ("user_id",          "User ID"),
    ("phone",            "Phone"),
    ("credits",          "Credits"),
    ("total_commands",   "Commands used"),
    ("referral_count",   "Referrals"),
    ("referred_by",      "Referred by"),
    ("join_date",        "Joined"),
    ("last_active",      "Last active"),
    ("phone_verified_at", "Phone verified"),
)

# Fields whose change is worth a channel post. Credits/commands/last_active are
# intentionally excluded — otherwise every search would spam the channel.
# Add "credits" here (or set TG_STORE_LOG_CREDITS=1) if you want balance changes.
_IMPORTANT_FIELDS = ("phone", "phone_verified_at", "is_blocked", "is_admin",
                     "referral_count", "username", "first_name", "referred_by")

_STATUS_LABELS = {0: "active", 1: "active", "0": "active", "1": "active"}


def _fmt_value(value):
    if value in (None, "", "N/A", "none", "None"):
        return "not shared"
    if isinstance(value, bool):
        return "yes" if value else "no"
    return str(value)


def _status_line(doc):
    if doc.get("is_blocked") in (1, "1", True):
        return "BLOCKED"
    if doc.get("is_admin") in (1, "1", True):
        return "admin"
    if doc.get("pending_signup"):
        return "signup pending"
    return "active"


def _status_transition(prev, doc):
    before, after = _status_line(prev), _status_line(doc)
    if before != after:
        return f"status: {before} → {after}"
    return None


def render_user_card(doc, prev=None):
    """
    Build the channel message for one user.

    prev is None      -> user is new: full card
    prev is a dict    -> only a card if an important field changed
    doc is None       -> user deleted
    Returns None when nothing worth posting changed.
    """
    if doc is None:
        if not prev:
            return None
        return "\n".join([
            "🗑 USER DELETED",
            _DIVIDER,
            f"{'Name':<15}: {_fmt_value(prev.get('first_name'))}",
            f"{'Username':<15}: {_fmt_value(prev.get('username'))}",
            f"{'User ID':<15}: {_fmt_value(prev.get('user_id'))}",
            _DIVIDER,
        ])

    if prev is None:
        lines = ["🆕 NEW USER", _DIVIDER]
        lines.append(f"{'Name':<15}: {_fmt_value(doc.get('first_name'))}")
        username = doc.get("username")
        lines.append(f"{'Username':<15}: "
                     + (f"@{username}" if username and username not in ("N/A", "None") else "not set"))
        lines.append(f"{'User ID':<15}: {_fmt_value(doc.get('user_id'))}")
        lines.append(f"{'Phone':<15}: {_fmt_value(doc.get('phone'))}")
        lines.append(f"{'Credits':<15}: {_fmt_value(doc.get('credits'))}")
        lines.append(f"{'Referrals':<15}: {_fmt_value(doc.get('referral_count'))}")
        if doc.get("referred_by"):
            lines.append(f"{'Referred by':<15}: {_fmt_value(doc.get('referred_by'))}")
        lines.append(f"{'Joined':<15}: {_fmt_value(doc.get('join_date'))}")
        lines.append(f"{'Status':<15}: {_status_line(doc)}")
        lines.append(_DIVIDER)
        return "\n".join(lines)

    changed = []
    for field, label in _USER_FIELDS:
        if field in ("last_active", "total_commands", "join_date"):
            continue
        if field not in _IMPORTANT_FIELDS and not _LOG_CREDITS:
            continue
        before = prev.get(field)
        after = doc.get(field)
        if _eq(before, after):
            continue
        if field == "phone_verified_at":
            changed.append("phone verified")
        elif field == "phone":
            changed.append(f"phone: {_fmt_value(before)} → {_fmt_value(after)}")
        else:
            changed.append(f"{label.lower()}: {_fmt_value(before)} → {_fmt_value(after)}")

    status_change = _status_transition(prev, doc)
    if status_change:
        changed.append(status_change)

    if not changed:
        return None

    lines = [
        "✏️ USER UPDATED",
        _DIVIDER,
        f"{'Name':<15}: {_fmt_value(doc.get('first_name'))}",
        f"{'User ID':<15}: {_fmt_value(doc.get('user_id'))}",
        "",
        "Changed:",
    ]
    lines += [f"  • {c}" for c in changed]
    lines.append(_DIVIDER)
    return "\n".join(lines)


_LOG_CREDITS = str(os.environ.get("TG_STORE_LOG_CREDITS", "0")).lower() in ("1", "true", "yes")


# Send the WHOLE users.json on every new signup instead of one file per user.
TG_SEND_FULL_DUMP_ON_NEW = str(os.environ.get("TG_SEND_FULL_DUMP_ON_NEW", "0")).lower() in ("1", "true", "yes")


def render_user_file(doc: dict) -> str:
    """Full record of one user as a plain-text file (readable first, json last)."""
    if not doc:
        return ""
    width = 18
    lines = ["WHOISSHOWN — USER RECORD", "=" * 46]

    def row(label, value):
        lines.append(f"{label:<{width}}: {value}")

    uname = doc.get("username")
    row("Name", _fmt_value(doc.get("first_name")))
    row("Username", ("@" + str(uname)) if uname not in (None, "", "N/A", "None") else "not set")
    row("User ID", _fmt_value(doc.get("user_id")))
    row("Phone", _fmt_value(doc.get("phone")))
    row("Phone verified", _fmt_value(doc.get("phone_verified_at")))
    row("Credits", _fmt_value(doc.get("credits")))
    row("Commands used", _fmt_value(doc.get("total_commands")))
    row("Referrals", _fmt_value(doc.get("referral_count")))
    row("Referred by", _fmt_value(doc.get("referred_by")))
    row("Joined", _fmt_value(doc.get("join_date")))
    row("Last active", _fmt_value(doc.get("last_active")))
    row("Status", _status_line(doc))
    row("Admin", "yes" if doc.get("is_admin") in (1, "1", True) else "no")

    raw = {k: v for k, v in doc.items() if k != "_id"}
    lines += ["=" * 46, "", "RAW RECORD (json)", json.dumps(raw, indent=2, default=str, ensure_ascii=False)]
    return "\n".join(lines) + "\n"


def user_file_name(doc: dict) -> str:
    uid = str(doc.get("user_id") or doc.get("_id") or "unknown")
    uname = str(doc.get("username") or "").strip().lstrip("@")
    uname = re.sub(r"[^A-Za-z0-9_.-]", "", uname)[:24]
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    return f"user_{uid}{('_' + uname) if uname else ''}_{stamp}.txt"


# ══════════════════════════════════════════════════════════════
#  Telegram channel sink
# ══════════════════════════════════════════════════════════════

class ChannelSink:
    """Posts coalesced document snapshots to a channel via the Bot API."""

    def __init__(self, bot_token: str, channel_id, logger=None, timeout=15):
        self.token = bot_token
        self.channel_id = channel_id
        self.timeout = timeout
        self._log = logger or (lambda msg: None)
        self._sess = requests.Session()

    @property
    def enabled(self):
        return bool(self.token and self.channel_id)

    def post_chunk(self, text: str) -> bool:
        if not self.enabled:
            return False
        url = f"https://api.telegram.org/bot{self.token}/sendMessage"
        body = {
            "chat_id": self.channel_id,
            "text": text,
            "disable_web_page_preview": True,
            "disable_notification": True,
        }
        for attempt in range(4):
            try:
                r = self._sess.post(url, json=body, timeout=self.timeout)
                if r.status_code == 200:
                    return True
                if r.status_code == 429:
                    try:
                        wait = int(r.json().get("parameters", {}).get("retry_after", 3))
                    except Exception:
                        wait = 3
                    time.sleep(min(wait, 10))
                    continue
                self._log(f"channel write rejected HTTP {r.status_code}: {r.text[:200]}")
                if r.status_code in (400, 403):
                    return False          # channel id / permissions — retrying won't help
                time.sleep(1 + attempt)
            except Exception as exc:
                self._log(f"channel write failed: {exc}")
                time.sleep(1 + attempt)
        return False

    def post_document(self, filename: str, content: str, caption: str = "") -> bool:
        """Send a plain-text/json file to the channel."""
        if not self.enabled:
            return False
        url = f"https://api.telegram.org/bot{self.token}/sendDocument"
        data = {"chat_id": self.channel_id, "disable_notification": True}
        if caption:
            data["caption"] = caption[:1000]
        payload = content.encode("utf-8")
        for attempt in range(4):
            try:
                r = self._sess.post(
                    url,
                    data=data,
                    files={"document": (filename, payload, "text/plain")},
                    timeout=max(self.timeout, 30),
                )
                if r.status_code == 200:
                    return True
                if r.status_code == 429:
                    try:
                        wait = int(r.json().get("parameters", {}).get("retry_after", 3))
                    except Exception:
                        wait = 3
                    time.sleep(min(wait, 10))
                    continue
                self._log(f"channel document rejected HTTP {r.status_code}: {r.text[:200]}")
                if r.status_code in (400, 403):
                    return False
                time.sleep(1 + attempt)
            except Exception as exc:
                self._log(f"channel document failed: {exc}")
                time.sleep(1 + attempt)
        return False

    def fetch_history(self, limit=None):
        """Yield (message_id, text). Bot API has no history method — returns []."""
        return []


# ══════════════════════════════════════════════════════════════
#  Collection
# ══════════════════════════════════════════════════════════════

class Collection:
    def __init__(self, store, name):
        self._store = store
        self.name = name
        self._unique = []          # list[tuple[field, ...]]
        self._indexes = set()

    # ── internal ───────────────────────────────────────────────
    @property
    def _docs(self):
        return self._store._coll(self.name)

    def _check_unique(self, doc, ignore_key=None):
        for key in self._unique:
            for other_key, other in self._docs.items():
                if other_key == ignore_key:
                    continue
                if all(_eq(_resolve(doc, f) if _resolve(doc, f) is not _MISSING else None,
                           _resolve(other, f) if _resolve(other, f) is not _MISSING else None)
                       for f in key):
                    raise DuplicateKeyError(f"duplicate key {key} in {self.name}")

    # ── indexes ────────────────────────────────────────────────
    def create_index(self, keys, unique=False, **kwargs):
        if isinstance(keys, str):
            name = keys
            fields = (keys,)
        elif isinstance(keys, (list, tuple)) and keys and isinstance(keys[0], (list, tuple)):
            fields = tuple(k for k, _ in keys)
            name = "_".join(f"{f}_{d}" for f, d in keys)
        elif isinstance(keys, (list, tuple)):
            fields = tuple(str(k) for k in keys)
            name = "_".join(fields)
        else:
            raise OperationFailure("bad index spec")
        if unique and fields not in self._unique:
            self._unique.append(fields)
        self._indexes.add(name)
        return name

    def drop_index(self, name):
        self._indexes.discard(name)

    def index_information(self):
        return {n: {} for n in self._indexes}

    # ── reads ──────────────────────────────────────────────────
    def find(self, filter=None, projection=None):
        def _fetch():
            return [d for d in self._docs.values() if _matches(d, filter)]
        mapper = (lambda d: _project(d, projection)) if projection else (lambda d: dict(d))
        return Cursor(_fetch, mapper=mapper)

    def find_one(self, filter=None, projection=None, sort=None):
        cur = self.find(filter, projection)
        if sort:
            cur.sort(sort)
        for doc in cur.limit(1):
            return doc
        return None

    def count_documents(self, filter=None, **kwargs):
        return sum(1 for d in self._docs.values() if _matches(d, filter))

    def estimated_document_count(self, **kwargs):
        return len(self._docs)

    def distinct(self, field, filter=None):
        return self.find(filter).distinct(field)

    # ── writes ─────────────────────────────────────────────────
    def insert_one(self, doc, **kwargs):
        with self._store._lock:
            doc = dict(doc)
            if "_id" not in doc:
                doc["_id"] = self._store._next_id()
            key = str(doc["_id"])
            if key in self._docs:
                raise DuplicateKeyError(f"duplicate _id {doc['_id']} in {self.name}")
            self._check_unique(doc)
            self._docs[key] = doc
            self._store._persist(self.name, doc)
            return InsertOneResult(doc["_id"])

    def insert(self, doc, **kwargs):
        return self.insert_one(doc).inserted_id

    def insert_many(self, docs, **kwargs):
        return InsertManyResult([self.insert_one(d).inserted_id for d in docs])

    def _find_keys(self, filter):
        return [k for k, d in self._docs.items() if _matches(d, filter)]

    def update_one(self, filter, update, upsert=False, **kwargs):
        with self._store._lock:
            keys = self._find_keys(filter)
            if keys:
                key = keys[0]
                original = json.dumps(self._docs[key], default=str, sort_keys=True)
                new_doc = _apply_update(dict(self._docs[key]), update, inserting=False)
                new_doc["_id"] = self._docs[key].get("_id")
                self._check_unique(new_doc, ignore_key=key)
                self._docs[key] = new_doc
                self._store._persist(self.name, new_doc)
                changed = 0 if json.dumps(new_doc, default=str, sort_keys=True) == original else 1
                return UpdateResult(matched=1, modified=changed)
            if not upsert:
                return UpdateResult()
            seed = {k: v for k, v in filter.items()
                    if not k.startswith("$") and not isinstance(v, dict)}
            new_doc = _apply_update(seed, update, inserting=True)
            if "_id" not in new_doc:
                new_doc["_id"] = self._store._next_id()
            self._check_unique(new_doc)
            self._docs[str(new_doc["_id"])] = new_doc
            self._store._persist(self.name, new_doc)
            return UpdateResult(matched=0, modified=0, upserted=new_doc["_id"])

    def update_many(self, filter, update, upsert=False, **kwargs):
        with self._store._lock:
            keys = self._find_keys(filter)
            modified = 0
            for key in keys:
                new_doc = _apply_update(dict(self._docs[key]), update, inserting=False)
                new_doc["_id"] = self._docs[key].get("_id")
                self._docs[key] = new_doc
                self._store._persist(self.name, new_doc)
                modified += 1
            if not keys and upsert:
                return self.update_one(filter, update, upsert=True)
            return UpdateResult(matched=len(keys), modified=modified)

    def replace_one(self, filter, replacement, upsert=False, **kwargs):
        with self._store._lock:
            keys = self._find_keys(filter)
            if keys:
                key = keys[0]
                new_doc = dict(replacement)
                new_doc["_id"] = self._docs[key].get("_id")
                self._docs[key] = new_doc
                self._store._persist(self.name, new_doc)
                return UpdateResult(matched=1, modified=1)
            if upsert:
                return self.update_one(filter, {"$set": dict(replacement)}, upsert=True)
            return UpdateResult()

    def find_one_and_update(self, filter, update, projection=None,
                            return_document=ReturnDocument.BEFORE, upsert=False, **kwargs):
        after = return_document in (ReturnDocument.AFTER, 1) or \
                str(return_document).lower().endswith("after") or return_document is True
        with self._store._lock:
            keys = self._find_keys(filter)
            if keys:
                key = keys[0]
                before = dict(self._docs[key])
                new_doc = _apply_update(dict(before), update, inserting=False)
                new_doc["_id"] = before.get("_id")
                self._check_unique(new_doc, ignore_key=key)
                self._docs[key] = new_doc
                self._store._persist(self.name, new_doc)
                chosen = new_doc if after else before
                return _project(chosen, projection) if projection else chosen
            if not upsert:
                return None
            seed = {k: v for k, v in filter.items()
                    if not k.startswith("$") and not isinstance(v, dict)}
            new_doc = _apply_update(seed, update, inserting=True)
            if "_id" not in new_doc:
                new_doc["_id"] = self._store._next_id()
            self._docs[str(new_doc["_id"])] = new_doc
            self._store._persist(self.name, new_doc)
            return _project(new_doc, projection) if projection else new_doc

    def find_one_and_delete(self, filter, projection=None, **kwargs):
        with self._store._lock:
            keys = self._find_keys(filter)
            if not keys:
                return None
            key = keys[0]
            doc = self._docs.pop(key)
            self._store._purge(self.name, key)
            return _project(doc, projection) if projection else doc

    def find_one_and_replace(self, filter, replacement, **kwargs):
        return self.find_one_and_update(filter, {"$set": replacement}, **kwargs)

    def delete_one(self, filter, **kwargs):
        with self._store._lock:
            keys = self._find_keys(filter)
            if not keys:
                return DeleteResult()
            key = keys[0]
            self._docs.pop(key, None)
            self._store._purge(self.name, key)
            return DeleteResult(1)

    def delete_many(self, filter, **kwargs):
        with self._store._lock:
            keys = self._find_keys(filter)
            for key in keys:
                self._docs.pop(key, None)
                self._store._purge(self.name, key)
            return DeleteResult(len(keys))

    # ── aggregation ────────────────────────────────────────────
    def aggregate(self, pipeline, **kwargs):
        docs = [dict(d) for d in self._docs.values()]
        for stage in pipeline:
            if not isinstance(stage, dict) or len(stage) != 1:
                raise OperationFailure("each pipeline stage must be a single-key dict")
            op, arg = next(iter(stage.items()))
            if op == "$match":
                docs = [d for d in docs if _matches(d, arg)]
            elif op == "$sample":
                size = int(arg.get("size", 1))
                if len(docs) > size:
                    docs = random.sample(docs, size)
            elif op == "$sort":
                docs = _sort_docs(docs, arg)
            elif op == "$limit":
                docs = docs[:int(arg)]
            elif op == "$skip":
                docs = docs[int(arg):]
            elif op == "$count":
                docs = [{arg: len(docs)}]
            elif op == "$project":
                docs = [_project(d, arg) for d in docs]
            elif op == "$unset":
                fields = [arg] if isinstance(arg, str) else list(arg)
                for d in docs:
                    for f in fields:
                        _unassign(d, f)
            elif op == "$addFields":
                for d in docs:
                    for k, v in arg.items():
                        _assign(d, k, _eval_expr(d, v) if isinstance(v, (str, dict)) else v)
            elif op == "$group":
                docs = _group(docs, arg)
            elif op in ("$lookup", "$facet", "$unwind", "$out", "$merge"):
                raise OperationFailure(f"stage {op} is not supported by tg_store")
            else:
                raise OperationFailure(f"unknown stage {op}")
        return Cursor(lambda: docs)

    # convenience aliases used by some code paths
    def remove(self, *a, **k):
        return self.delete_many(*a, **k)

    def save(self, doc, **kwargs):
        if "_id" in doc:
            self.replace_one({"_id": doc["_id"]}, doc, upsert=True)
            return doc["_id"]
        return self.insert_one(doc).inserted_id


def _group(docs, spec):
    key_field = spec.get("_id")
    buckets = OrderedDict()
    for doc in docs:
        key = None if key_field is None else _eval_expr(doc, key_field) if isinstance(key_field, str) else key_field
        marker = json.dumps(key, default=str, sort_keys=True)
        buckets.setdefault(marker, {"_id": key, "_docs": []})["_docs"].append(doc)
    out = []
    for bucket in buckets.values():
        rows = bucket.pop("_docs")
        result = {"_id": bucket["_id"]}
        for field, acc in spec.items():
            if field == "_id":
                continue
            if not isinstance(acc, dict):
                raise OperationFailure("accumulator must be a dict")
            op, expr = next(iter(acc.items()))
            values = [_eval_expr(d, expr) if isinstance(expr, str) and expr.startswith("$") else expr
                      for d in rows]
            values = [v for v in values if v is not None]
            if op == "$sum":
                result[field] = sum(values)
            elif op == "$count":
                result[field] = len(rows)
            elif op == "$avg":
                result[field] = (sum(values) / len(values)) if values else 0
            elif op == "$min":
                result[field] = min(values) if values else None
            elif op == "$max":
                result[field] = max(values) if values else None
            elif op == "$first":
                result[field] = values[0] if values else None
            elif op == "$last":
                result[field] = values[-1] if values else None
            elif op == "$push":
                result[field] = values
            elif op == "$addToSet":
                result[field] = list({json.dumps(v, default=str): v for v in values}.values())
            else:
                raise OperationFailure(f"unsupported accumulator {op}")
        out.append(result)
    return out


# ══════════════════════════════════════════════════════════════
#  Store
# ══════════════════════════════════════════════════════════════

class TGStore:
    """Mongo-ish store: memory + SQLite + readable Telegram channel log."""

    def __init__(self, db_path="tg_store.db", channel_id=None, bot_token=None,
                 flush_interval=4.0, logger=print, autostart=True,
                 readable_collections=("users",)):
        self.db_path = db_path
        self._log = logger or (lambda *a: None)
        self._lock = threading.RLock()
        self._colls = {}
        self._data = {}
        self._seq = 0
        self._dirty = OrderedDict()       # (coll, key) -> None
        self._dirty_lock = threading.Lock()
        self._readable = set(readable_collections or ())
        self._posted = {}                 # (coll, key) -> last doc posted to channel
        self.sink = ChannelSink(bot_token, channel_id, logger=self._log)
        self._flush_interval = flush_interval
        self._stop = threading.Event()
        self._thread = None

        self._conn = sqlite3.connect(db_path, check_same_thread=False)
        self._conn.execute("PRAGMA journal_mode=WAL")
        self._conn.execute("PRAGMA synchronous=NORMAL")
        self._conn.execute("PRAGMA busy_timeout=5000")
        self._conn.executescript("""
            CREATE TABLE IF NOT EXISTS docs (
                coll TEXT NOT NULL,
                id   TEXT NOT NULL,
                body TEXT NOT NULL,
                PRIMARY KEY (coll, id)
            );
            CREATE TABLE IF NOT EXISTS tombstones (
                coll TEXT NOT NULL,
                id   TEXT NOT NULL,
                PRIMARY KEY (coll, id)
            );
            CREATE TABLE IF NOT EXISTS posted (
                coll TEXT NOT NULL,
                id   TEXT NOT NULL,
                body TEXT NOT NULL,
                PRIMARY KEY (coll, id)
            );
            CREATE TABLE IF NOT EXISTS meta (k TEXT PRIMARY KEY, v TEXT);
        """)
        self._conn.commit()
        self._load()
        if autostart and self.sink.enabled:
            self._thread = threading.Thread(target=self._flush_loop, name="tg-store-flush", daemon=True)
            self._thread.start()
            atexit.register(self.close)
            self._log(f"tg_store: {db_path} loaded | channel log {'ON' if self.sink.enabled else 'OFF'}")

    # ── loading ────────────────────────────────────────────────
    def _load(self):
        with self._lock:
            for coll, doc_id, body in self._conn.execute("SELECT coll, id, body FROM docs"):
                try:
                    doc = json.loads(body)
                except Exception:
                    continue
                self._data.setdefault(coll, OrderedDict())[doc_id] = doc
            for coll, doc_id, body in self._conn.execute("SELECT coll, id, body FROM posted"):
                try:
                    self._posted[(coll, doc_id)] = json.loads(body)
                except Exception:
                    continue
            row = self._conn.execute("SELECT v FROM meta WHERE k='seq'").fetchone()
            self._seq = int(row[0]) if row else 0
            for (coll,) in self._conn.execute("SELECT DISTINCT coll FROM docs"):
                self._data.setdefault(coll, OrderedDict())
        self._log(f"tg_store: {sum(len(v) for v in self._data.values())} docs restored")

    def _coll(self, name):
        with self._lock:
            return self._data.setdefault(name, OrderedDict())

    def _next_id(self):
        self._seq += 1
        self._conn.execute("INSERT OR REPLACE INTO meta(k, v) VALUES('seq', ?)", (str(self._seq),))
        self._conn.commit()
        return self._seq

    # ── persistence ────────────────────────────────────────────
    def _persist(self, coll, doc):
        body = json.dumps(doc, default=str, ensure_ascii=False)
        self._conn.execute(
            "INSERT OR REPLACE INTO docs(coll, id, body) VALUES(?,?,?)",
            (coll, str(doc.get("_id")), body))
        self._conn.execute("DELETE FROM tombstones WHERE coll=? AND id=?", (coll, str(doc.get("_id"))))
        self._conn.commit()
        with self._dirty_lock:
            self._dirty[(coll, str(doc.get("_id")))] = None

    def _purge(self, coll, key):
        self._conn.execute("DELETE FROM docs WHERE coll=? AND id=?", (coll, key))
        self._conn.execute("INSERT OR REPLACE INTO tombstones(coll, id) VALUES(?,?)", (coll, key))
        self._conn.commit()
        with self._dirty_lock:
            self._dirty[(coll, key)] = None

    # ── channel flusher ────────────────────────────────────────
    def _flush_loop(self):
        cycles = 0
        while not self._stop.wait(self._flush_interval):
            try:
                self.flush_once()
            except Exception as exc:
                self._log(f"tg_store flush error: {exc}")
            cycles += 1
            if cycles % 40 == 0:                     # ~ every 3 minutes
                self.checkpoint()

    def checkpoint(self):
        """Fold the WAL back into the main db — keeps disk usage flat."""
        try:
            self._conn.execute("PRAGMA wal_checkpoint(TRUNCATE)")
        except Exception as exc:
            self._log(f"checkpoint failed: {exc}")

    def flush_once(self):
        """Post every pending user change to the channel as readable cards."""
        with self._dirty_lock:
            if not self._dirty:
                return 0
            pending = list(self._dirty.keys())
            self._dirty.clear()

        cards = []
        snapshots = []          # (coll, key, doc or None) to remember after a successful post
        new_user_docs = []      # docs of brand-new users -> their data file is sent too
        with self._lock:
            for coll, key in pending:
                if coll not in self._readable:
                    continue
                doc = self._data.get(coll, {}).get(key)
                prev = self._posted.get((coll, key))
                try:
                    card = render_user_card(doc, prev)
                except Exception as exc:
                    self._log(f"tg_store card render error: {exc}")
                    card = None
                if card:
                    cards.append(card)
                    snapshots.append((coll, key, doc))
                    if doc is not None and prev is None:
                        new_user_docs.append(dict(doc))

        if not cards:
            return 0

        posted = 0
        batch, batch_docs = "", []
        ok = True
        for card, snap in zip(cards, snapshots):
            if batch and len(batch) + len(card) + 2 > _MAX_MSG_CHARS:
                ok = self.sink.post_chunk(batch) and ok
                if not ok:
                    break
                posted += 1
                self._remember(batch_docs)
                batch, batch_docs = "", []
                time.sleep(0.8)                     # stay friendly with flood limits
            batch = (batch + "\n\n" + card) if batch else card
            batch_docs.append(snap)

        if ok and batch:
            ok = self.sink.post_chunk(batch)
            if ok:
                posted += 1
                self._remember(batch_docs)

        if ok and new_user_docs:
            posted += self._send_new_user_files(new_user_docs)

        if not ok:
            with self._dirty_lock:                  # retry on the next cycle
                for item in pending:
                    self._dirty.setdefault(item, None)
        return posted

    def _send_new_user_files(self, docs):
        """Auto-send the data file for freshly registered users."""
        sent = 0
        if TG_SEND_FULL_DUMP_ON_NEW:
            try:
                payload = json.dumps(
                    {str(d.get("user_id")): d for d in
                     sorted(self._data.get("users", {}).values(),
                            key=lambda x: _cmp_key(x.get("_id")))},
                    indent=2, default=str, ensure_ascii=False)
                if self.sink.post_document("users.json", payload,
                                           caption=f"users.json — {len(self._data.get('users', {}))} users"):
                    sent += 1
            except Exception as exc:
                self._log(f"tg_store users.json error: {exc}")
            return sent

        for doc in docs:
            try:
                caption = (f"New user: {_fmt_value(doc.get('first_name'))}"
                           f" (@{doc.get('username')})" if doc.get("username") not in (None, "", "N/A", "None")
                           else f"New user: {_fmt_value(doc.get('first_name'))} — {doc.get('user_id')}")
                if self.sink.post_document(user_file_name(doc), render_user_file(doc), caption):
                    sent += 1
                time.sleep(0.6)
            except Exception as exc:
                self._log(f"tg_store user file error: {exc}")
        return sent

    def _remember(self, snapshots):
        """Save the last doc state we posted, so restarts do not re-post."""
        with self._lock:
            for coll, key, doc in snapshots:
                if doc is None:
                    self._posted.pop((coll, key), None)
                    self._conn.execute("DELETE FROM posted WHERE coll=? AND id=?", (coll, key))
                else:
                    snap = dict(doc)
                    self._posted[(coll, key)] = snap
                    self._conn.execute(
                        "INSERT OR REPLACE INTO posted(coll, id, body) VALUES(?,?,?)",
                        (coll, key, json.dumps(snap, default=str, ensure_ascii=False)))
            self._conn.commit()

    def pending(self):
        with self._dirty_lock:
            return len(self._dirty)

    # ── manual export ──────────────────────────────────────────
    def export_collection(self, name="users", limit=None, pace=1.0, with_json=True):
        """
        Post a full card for every document in `name` to the channel,
        followed by a .json file with the whole collection.
        Used by the /exportusers admin command.
        """
        if not self.sink.enabled:
            return 0
        with self._lock:
            docs = sorted(self._data.get(name, {}).values(),
                          key=lambda d: _cmp_key(d.get("_id")))
        if limit:
            docs = docs[:int(limit)]
        cards = [render_user_card(d, None) for d in docs]
        cards = [c for c in cards if c]

        posted = 0
        batch = ""
        for card in cards:
            if batch and len(batch) + len(card) + 2 > _MAX_MSG_CHARS:
                if not self.sink.post_chunk(batch):
                    return posted
                posted += 1
                batch = ""
                time.sleep(pace)
            batch = (batch + "\n\n" + card) if batch else card
        if batch and self.sink.post_chunk(batch):
            posted += 1

        with self._lock:                             # exported state is now known
            for doc in docs:
                key = str(doc.get("_id"))
                self._posted[(name, key)] = dict(doc)
                self._conn.execute(
                    "INSERT OR REPLACE INTO posted(coll, id, body) VALUES(?,?,?)",
                    (name, key, json.dumps(doc, default=str, ensure_ascii=False)))
            self._conn.commit()

        if with_json and docs:
            payload = json.dumps(docs, indent=2, default=str, ensure_ascii=False)
            stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            if self.sink.post_document(f"{name}_{stamp}.json", payload,
                                       caption=f"{name}.json — {len(docs)} records"):
                posted += 1
        return posted

    # NOTE: the channel holds readable cards, not machine state — replaying them
    # back into a database is not something you should ever need. The working copy
    # is the SQLite file next to the bot; copy it for backup and the channel stays
    # as the human-readable history.

    # ── misc ───────────────────────────────────────────────────
    def __getitem__(self, name):
        with self._lock:
            if name not in self._colls:
                self._colls[name] = Collection(self, name)
            return self._colls[name]

    def get_collection(self, name, **kwargs):
        return self[name]

    def list_collection_names(self):
        return list(self._data.keys())

    def command(self, *a, **k):
        return {"ok": 1}

    def close(self):
        self._stop.set()
        try:
            self.flush_once()
        except Exception:
            pass
        try:
            self._conn.commit()
            self._conn.close()
        except Exception:
            pass

    def stats(self):
        return {name: len(docs) for name, docs in self._data.items()}


# Alias so old imports keep working
MongoClient = TGStore




# ── HTTP session — defined early so make_api_request can use it anywhere ──
def create_session():
    _sess = requests.Session()
    _adapter = HTTPAdapter(
        pool_connections=50,
        pool_maxsize=50,
        max_retries=Retry(total=0),  # no adapter retries — fallbacks handled in code
        pool_block=False
    )
    _sess.mount('http://', _adapter)
    _sess.mount('https://', _adapter)
    _sess.headers.update({
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
        'Accept': 'application/json',
        'Accept-Language': 'en-US,en;q=0.9',
        'Connection': 'keep-alive'
    })
    return _sess

session = create_session()

# ============================================================
# CONTACT STORAGE — MongoDB only (Turso removed)
# ============================================================

# Premium emoji IDs for the green captcha button
CAPTCHA_BTN_EMOJI_1 = "5864127571754489150"
CAPTCHA_BTN_EMOJI_2 = "6080263490163973583"

# ── Contact-gate state dicts ────────────────────────────────────
_LAST_CAPCHA_MESSAGE: dict = {}   # uid -> captcha prompt message_id
_LAST_FJ_MESSAGE:     dict = {}   # uid -> force-join message_id
_PENDING_REF:         dict = {}   # uid -> referral id (survives the gate)


def _is_contact_verified(uid: int) -> bool:
    """
    Check if user is verified — MongoDB only.
    True if phone field is present and non-empty.
    """
    if uid in _VERIFIED_UIDS:
        return True
    try:
        doc = _col_users.find_one({"user_id": uid}, {"phone": 1, "contact_verified": 1})
        if doc and (doc.get("phone") or doc.get("contact_verified")):
            _VERIFIED_UIDS.add(uid)
            return True
    except Exception as e:
        print(f"[IS_VERIFIED_MONGO] {e}")
    return False


def _mark_contact_verified(uid: int, phone: str):
    """
    Mark user verified — MongoDB only.
    upsert=True so phone saves even if user doc does not exist yet.
    """
    try:
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        _col_users.update_one(
            {"user_id": uid},
            {
                "$set": {
                    "phone": phone,
                    "phone_verified_at": now,
                    "contact_verified": True,
                },
                "$setOnInsert": {
                    "username": "N/A",
                    "first_name": "Unknown",
                    "credits": 0,
                    "is_admin": 0,
                    "referred_by": None,
                    "referral_count": 0,
                    "join_date": now,
                    "last_active": now,
                    "total_commands": 0,
                    "joined_channel1": 0,
                    "joined_channel2": 0,
                    "joined_channel3": 0,
                    "is_blocked": 0,
                    # stub doc: create_user() finalises it (welcome + referral credits) once
                    "pending_signup": True,
                },
            },
            upsert=True,
        )
        _VERIFIED_UIDS.add(uid)
        print(f"[MARK_VERIFIED] uid={uid} phone=***{str(phone)[-4:]} saved")
    except Exception as e:
        print(f"[MARK_VERIFIED_MONGO] {e}")


def _save_pending_ref(uid: int, ref):
    """Stash referral so it survives the contact-gate redirect."""
    if ref:
        _PENDING_REF[uid] = ref


def _KB(text: str, request_contact: bool = False, style: str = None,
        icon_custom_emoji_id: str = None, **kwargs):
    """Build a reply-keyboard button using Bot API 9.4 native styling.

    IMPORTANT: pyTelegramBotAPI must be >= 4.31.0 for Bot API 9.4 fields.
    Assigning ``btn.style`` after construction is NOT reliable with older
    serializers: the attribute can exist locally but be omitted from JSON.
    """
    style = style if style in ("primary", "success", "danger") else None
    button_kwargs = dict(text=text, request_contact=request_contact, **kwargs)
    if style:
        button_kwargs["style"] = style
    if icon_custom_emoji_id:
        button_kwargs["icon_custom_emoji_id"] = icon_custom_emoji_id

    try:
        # Pass style during construction so supported library versions include
        # it in KeyboardButton.to_dict()/the outgoing Telegram API payload.
        return types.KeyboardButton(**button_kwargs)
    except TypeError as exc:
        # Do not silently pretend colours were applied. Older library versions
        # need upgrading; fallback keeps the keyboard usable until then.
        if "style" in button_kwargs:
            print(
                "[KEYBOARD_STYLE] pyTelegramBotAPI does not support KeyboardButton.style. "
                "Upgrade with: pip install -U pyTelegramBotAPI>=4.31.0"
            )
            button_kwargs.pop("style", None)
        if "icon_custom_emoji_id" in button_kwargs:
            button_kwargs.pop("icon_custom_emoji_id", None)
        try:
            return types.KeyboardButton(**button_kwargs)
        except TypeError:
            # Last-resort compatibility with older versions.
            return types.KeyboardButton(text=text, request_contact=request_contact)


# ── Turso removed — MongoDB is sole store — stubs prevent crashes ──
TURSO_URL    = ""
TURSO_TOKEN  = ""
TURSO_HEADERS = {}

# ── API Base URL — sirf yahan change karo, sab jagah apply ho jaayega ──
BASE_URL = "YOUR_SERVER_URL_HERE"          # (BASE) apna server yaha daalo

def turso_execute(sql: str, args=None):
    return {}

def turso_init():
    print("✅ Turso removed — MongoDB only")

def turso_is_verified(user_id: int) -> bool:
    return False

def turso_save_contact(user_id: int, phone: str):
    pass
# ──────────────────────────────────────────────────────────────

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.handlers.RotatingFileHandler(
            'bot.log', maxBytes=2 * 1024 * 1024, backupCount=2, encoding='utf-8'),
        logging.StreamHandler(),
    ]
)
logger = logging.getLogger(__name__)

# ===== PREMIUM EMOJI IDs =====
PREMIUM_EMOJI_IDS = [
"4956420859771225351",
"4958626617535497157",
"4958734459869332468",
"4956282853882069908",
"4956247175588742152",
"5296491800423340716",
"4956739572114392015",
"4956606007221421405",
"4958617898751886363",
"4956290155326473271",
"4958714479681471536",
"4956461073550017373",
"4956719506027185156",
"5116414868357907335",
"4958587679361991667",
"4956560549287560231",
"4956539525422646612",
"6127546175240280564",
"6127558265573218459",
"5084613633418199991",
"5098265504796115765",
"5116296632203216188",
"6147565374289220368",
"6147464060305676048",
"6235459831302460476",
"6235355429237430006",
"6129434968713076807",
"6129828611055689014",
"6129700535130922338"
]

def get_random_premium_emoji_id():
    pool = [i for i in PREMIUM_EMOJI_IDS if i not in _BAD_EMOJI_IDS]
    return random.choice(pool or PREMIUM_EMOJI_IDS)

# ============================================================
# PREMIUM EMOJI MAP — NUMBER INFO SPECIFIC
# ============================================================
NUM_EMOJIS = {
    "header_divider": "5467641505525016018",   # ➿
    "phone_title":    "6172503852785342178",   # 📞
    "status_ok":      "6129812419028982717",   # ✅
    "query":          "5379999674193172777",   # 🔭
    "records":        "5197269100878907942",   # ✍️
    "record_badge":   "5249231689695115145",   # 📰
    "number":         "6026092115631543342",   # 📲
    "name":           "5425124408786197150",   # 👤
    "father":         "5258513401784573443",   # 👥
    "alt_num":        "5453965363286925977",   # 📞
    "circle":         "5895476993314524652",   # 🔎
    "address":        "4958485609464202497",   # 🏡
    "id_card":        "5985796637971191405",   # 💳
    "email":          "5303416490295304868",   # 📧
    "speed":          "6203911118964924015",   # 🚀
    "credits":        "5326049357332513437",   # 🧱
    "bot_icon":       "5355051922862653659",   # 🤖
    "star":           "6118385795976930086",   # 🌟
}
# ============================================================
# PREMIUM EMOJI MAP — AADHAR INFO SPECIFIC
# ============================================================
ADHR_EMOJIS = {
    "header_divider": "5467641505525016018",   # ➿
    "adhr_title":     "6030753228889526497",   # 🪪
    "status_ok":      "6071022434234930063",   # ✅
    "query":          "5379999674193172777",   # 🔭
    "records":        "5197269100878907942",   # ✍️
    "record_badge":   "5249231689695115145",   # 📰
    "mobile":         "6026092115631543342",   # 📲
    "name":           "5425124408786197150",   # 👤
    "circle":         "5375365992891312468",   # 🛜
    "address":        "4958485609464202497",   # 🏡
    "id_card":        "5985796637971191405",   # 💳
    "speed":          "6203911118964924015",   # 🚀
    "credits":        "5931368295545443065",   # 📊
    "bot_icon":       "5355051922862653659",   # 🤖
    "star":           "6118385795976930086",   # 🌟
    "father":         "5258513401784573443",   # 👥
    "email":          "5303416490295304868",   # 📧
}

def build_adhr_divider() -> str:
    d = te(ADHR_EMOJIS["header_divider"], "➿")
    return (d * 8) + "\n"

# ============================================================
# PREMIUM EMOJI MAP — VEHICLE / RC SPECIFIC
# ============================================================
VECH_EMOJIS = {
    "header_divider": "5467641505525016018",   # ➿
    "veh_title":      "5323272789824654613",   # 🪪
    "rc_number":      "6093653759378858331",   # 🚗
    "source":         "5798417071796653494",   # 💎
    "status_ok":      "6129812419028982717",   # ✅
    "vehicle":        "5312322066328853156",   # 🚗
    "make":           "6077707920198338212",   # 🏭
    "mfg_year":       "6021757076290675447",   # 🗓️
    "fuel":           "5359588280205605798",   # ⚡️
    "vclass":         "6226775738142432221",   # 👿
    "cc":             "4904936030232117798",   # ⚙️
    "seating":        "5260732577026696524",   # 🐸
    "colour":         "5926764846518376076",   # 📋
    "body":           "6233262422954613958",   # 🏎
    "owner":          "5832263552982851814",   # 👨‍🦰
    "mobile":         "6104960836311195547",   # 📲
    "address":        "4958485609464202497",   # 🏡
    "registration":   "5226929552319594190",   # 0️⃣
    "reg_date":       "5472279086657199080",   # 🗓️
    "rto":            "6303001048185309018",   # 🗺
    "rto_code":       "5422449357125350081",   # 🔢
    "financer":       "5264733042710181045",   # 🏢
    "commercial":     "5796205953913196373",   # 💎
    "insurance":      "5188688567970308198",   # 🏎
    "ins_status":     "6300604035527346062",   # 🛡
    "technical":      "5341715473882955310",   # ⚙️
    "chassis":        "5258023599419171861",   # 🔧
    "engine":         "4967657001023701985",   # ⚙️
    "norms":          "4904936030232117798",   # ⚙️
    "speed":          "6203911118964924015",   # 🚀
    "credits":        "5326049357332513437",   # 🧱
    "bot_icon":       "5355051922862653659",   # 🤖
    "star":           "6118385795976930086",   # 🌟
    "query":          "5379999674193172777",   # 🔭
    "records":        "5197269100878907942",   # ✍️
    "record_badge":   "5249231689695115145",   # 📰
}

def build_vech_divider() -> str:
    d = te(VECH_EMOJIS["header_divider"], "➿")
    return (d * 12) + "\n"


# ============================================================
# PREMIUM EMOJI MAP — INSTAGRAM SPECIFIC
# ============================================================
INSTA_EMOJIS = {
    "header_divider": "5465629669829128119",   # ➿
    "insta_title":    "6197411888553270114",   # 📸
    "username":       "6122805733936342496",   # 👤
    "name":           "6183633702187176982",   # 👑
    "user_id":        "5193037303961920951",   # 🆔
    "status":         "6035239240625820254",   # 🔒
    "acc_type":       "6091402470666279677",   # 💼
    "joined":         "5348227245599105972",   # 📅
    "profile":        "6305370152145787193",   # ❔
    "followers":      "5890937706803894250",   # 👥
    "following":      "5310095671246733180",   # 🔄
    "posts":          "5301276827782755360",   # 📱
    "speed":          "6203911118964924015",   # 🚀
    "credits":        "5326049357332513437",   # 🧱
    "bot_icon":       "5355051922862653659",   # 🤖
    "star":           "6118385795976930086",   # 🌟
}

def build_insta_divider() -> str:
    d = te(INSTA_EMOJIS["header_divider"], "➿")
    # Keep the Instagram caption below Telegram's 1024-character photo limit.
    return (d * 2) + "\n"


def te(emoji_id: str, fallback: str = "⭐") -> str:
    if not PREMIUM_EMOJI_SUPPORTED:
        return fallback
    """Shorthand: build a <tg-emoji> tag. Must use double quotes — Telegram HTML parser rejects single quotes."""
    return '<tg-emoji emoji-id="' + emoji_id + '">' + fallback + '</tg-emoji>'

def build_num_divider() -> str:
    d = te(NUM_EMOJIS["header_divider"], "➿")
    return (d * 8) + "\n"


# ===== PREMIUM EMOJI REPLACEMENT SYSTEM =====
EMOJI_TO_PREMIUM = {
    "⚠": "4956420859771225351",
    "⚡": "4958626617535497157",
    "✅": "4958734459869332468",
    "✏": "4956282853882069908",
    "✨": "4956247175588742152",
    "❌": "5296491800423340716",
    "❓": "4956739572114392015",
    "❤": "4956606007221421405",
    "➕": "4958617898751886363",
    "➖": "4956290155326473271",
    "➡": "4958714479681471536",
    "🌍": "4956461073550017373",
    "🌐": "4956719506027185156",
    "🌟": "5116414868357907335",
    "🎂": "4958587679361991667",
    "🎉": "4956560549287560231",
    "🎥": "4956539525422646612",
    "🎨": "6127546175240280564",
    "🎫": "6127558265573218459",
    "🎬": "5084613633418199991",
    "🎮": "5098265504796115765",
    "🏆": "5116414868357907335",
    "🏙": "5116296632203216188",
    "🏠": "6147565374289220368",
    "🏦": "6147464060305676048",
    "🐙": "6235459831302460476",
    "👋": "6235355429237430006",
    "👑": "6129434968713076807",
    "👤": "6129828611055689014",
    "👥": "6129700535130922338",
    "👦": "4956420859771225351",
    "👧": "4958626617535497157",
    "👨": "4958734459869332468",
    "👩": "4956282853882069908",
    "💡": "4956247175588742152",
    "💬": "5296491800423340716",
    "💰": "4956739572114392015",
    "💳": "4956606007221421405",
    "📄": "4958617898751886363",
    "📅": "4956290155326473271",
    "📈": "4958714479681471536",
    "📊": "4956461073550017373",
    "📋": "4956719506027185156",
    "📌": "5116414868357907335",
    "📍": "4958587679361991667",
    "📚": "4956560549287560231",
    "📛": "4956539525422646612",
    "📝": "6127546175240280564",
    "📞": "6127558265573218459",
    "📢": "5084613633418199991",
    "📥": "5098265504796115765",
    "📧": "5116414868357907335",
    "📨": "5116296632203216188",
    "📮": "6147565374289220368",
    "📱": "6147464060305676048",
    "📸": "6235459831302460476",
    "📺": "6235355429237430006",
    "🔄": "6129434968713076807",
    "🔍": "6129828611055689014",
    "🔐": "6129700535130922338",
    "🔑": "4956420859771225351",
    "🔒": "4958626617535497157",
    "🔓": "4958734459869332468",
    "🔔": "4956282853882069908",
    "🔗": "4956247175588742152",
    "🔘": "5296491800423340716",
    "🔙": "4956739572114392015",
    "🔢": "4956606007221421405",
    "🔥": "4958617898751886363",
    "🔧": "4956290155326473271",
    "🕐": "4958714479681471536",
    "🖼": "4956461073550017373",
    "🗑": "4956719506027185156",
    "🗺": "5116414868357907335",
    "🚗": "4958587679361991667",
    "🚫": "4956560549287560231",
    "🛑": "4956539525422646612",
    "🟢": "6127546175240280564",
    "🧪": "6127558265573218459",
    "⭐": "5116414868357907335",
    "🆔": "6129828611055689014",
    "🆕": "6129700535130922338",
    "🎰": "4956560549287560231",
}

_TG_EMOJI_RE = re.compile(r'<tg-emoji emoji-id=["\'"]\d+["\'"]>[^<]*</tg-emoji>')
_FREE_EMOJI_RE = re.compile(
    "["
    "\U0001F600-\U0001F64F"   # Emoticons 😀-🙏
    "\U0001F300-\U0001F5FF"   # Misc Symbols & Pictographs 🌀-🗿
    "\U0001F680-\U0001F6FF"   # Transport & Map 🚀-🛿
    "\U0001F1E0-\U0001F1FF"   # Flags 🇠-🇿
    "\U00002702-\U000027B0"   # Dingbats ✂-➰
    "\U0001F900-\U0001F9FF"   # Supplemental Symbols & Pictographs
    "\U0001FA00-\U0001FA6F"   # Chess Symbols
    "\U0001FA70-\U0001FAFF"   # Symbols & Pictographs Extended-A
    "\U00002600-\U000026FF"   # Misc Symbols ☀-⛿
    "\U00002B00-\U00002BFF"   # Misc Symbols & Arrows
    "\U00002300-\U000023FF"   # Misc Technical
    "\U0001F7E0-\U0001F7FF"   # Geometric Shapes Extended
    "\U0000200D"                # ZWJ
    "\U000024C2-\U000024FF"   # Enclosed Alphanumerics Ⓜ-Ⓩ
    "\U0001F000-\U0001F02F"   # Mahjong Tiles
    "\U0001F0A0-\U0001F0FF"   # Playing Cards
    "\U0001F200-\U0001F2FF"   # Enclosed Ideographic Supplement
    "]+", flags=re.UNICODE
)

def replace_with_premium_emojis(text):
    """Replace all free emojis in text with random premium Telegram emoji tags.
    Existing <tg-emoji> tags are preserved untouched."""
    if not text or not isinstance(text, str):
        return text

    # Step 1: Protect existing <tg-emoji> tags
    tg_emoji_pattern = _TG_EMOJI_RE
    placeholders = []
    def protect(match):
        placeholders.append(match.group(0))
        return f"[[P_{len(placeholders)-1}]]"
    text = tg_emoji_pattern.sub(protect, text)

    # Step 2: Replace free emojis with premium tags
    emoji_pattern = _FREE_EMOJI_RE

    def replace_emoji(match):
        if not PREMIUM_EMOJI_SUPPORTED:
            return match.group(0)      # keep the user's own emoji as-is
        random_id = get_random_premium_emoji_id()
        return '<tg-emoji emoji-id="' + random_id + '">⭐</tg-emoji>'

    text = emoji_pattern.sub(replace_emoji, text)

    # Step 3: Restore protected tags
    for i, original in enumerate(placeholders):
        text = text.replace(f"[[P_{i}]]", original)

    return text

def truncate_text(text, max_length=10000):
    """Truncate text safely without breaking HTML tags"""
    if not text:
        return text
    if len(text) <= max_length:
        return text

    truncate_msg = "\n\n<blockquote>... (truncated - download JSON for full data)</blockquote>"
    available = max_length - len(truncate_msg)

    # Find last complete </blockquote> before max_length
    search_text = text[:available]
    last_close = search_text.rfind('</blockquote>')

    if last_close > 0:
        cut_point = last_close + len('</blockquote>')
        return text[:cut_point] + truncate_msg
    else:
        return text[:available] + truncate_msg


_SAFE_TAG_RE = re.compile(
    r'</?(?:b|i|u|s|code|pre|a|blockquote|tg-emoji|tg-spoiler|br|span)'
    r'(?:\s[^<>]*)?>',
    re.IGNORECASE
)

def _sanitise_html(text: str) -> str:
    """
    Protect Telegram HTML parse_mode from raw exception strings.
    Leaves valid Telegram HTML tags untouched; escapes bare < > & that
    are NOT part of a recognised Telegram HTML construct.
    Known safe tags: b, i, u, s, code, pre, a, blockquote, tg-emoji,
                     tg-spoiler, br, span.
    """
    SAFE = _SAFE_TAG_RE
    result = []
    pos = 0
    for m in SAFE.finditer(text):
        # escape everything before this safe tag
        chunk = text[pos:m.start()]
        chunk = chunk.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
        result.append(chunk)
        result.append(m.group())          # keep the safe tag as-is
        pos = m.end()
    # tail after last safe tag
    tail = text[pos:]
    tail = tail.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
    result.append(tail)
    return ''.join(result)



# ════════════════════════════════════════════════════════════
# PREMIUM-EMOJI FALLBACK LADDER
# If Telegram refuses the <tg-emoji> entities (a bot may only use custom
# emoji if it owns the sticker set or has a Fragment username), the old
# code retried with parse_mode removed — which dumped the raw
# "<tg-emoji emoji-id=...>" tags into the chat. These helpers degrade
# cleanly instead: premium emoji -> plain emoji -> plain text.
# ════════════════════════════════════════════════════════════
_TG_EMOJI_FULL_RE = re.compile(r'<tg-emoji[^>]*>(.*?)</tg-emoji>', re.S | re.I)
_ANY_TAG_RE = re.compile(r'<[^>]+>')

# Set True once Telegram has rejected custom emoji, so later messages skip
# the doomed first attempt instead of paying for it every time.
PREMIUM_EMOJI_SUPPORTED = True
_PREMIUM_WARNED = False


def _downgrade_premium_emojis(text: str) -> str:
    """Replace each <tg-emoji ...>X</tg-emoji> with its fallback character X.
    All other HTML (b, code, blockquote...) is kept intact."""
    return _TG_EMOJI_FULL_RE.sub(lambda m: m.group(1), str(text))


def _html_to_plain(text: str) -> str:
    """Last resort: strip every tag and unescape entities — never show markup."""
    t = _downgrade_premium_emojis(text)
    t = _ANY_TAG_RE.sub('', t)
    return _html.unescape(t)


def _is_custom_emoji_error(exc) -> bool:
    e = str(exc).lower()
    # deliberately narrow: a generic "can't parse entities" can come from any
    # malformed tag, and must not permanently disable premium emoji
    return ("custom_emoji" in e or "custom emoji" in e
            or "emoji_invalid" in e or "customemoji" in e)


def _note_premium_unsupported(exc):
    global PREMIUM_EMOJI_SUPPORTED, _PREMIUM_WARNED
    if _is_custom_emoji_error(exc):
        PREMIUM_EMOJI_SUPPORTED = False
        if not _PREMIUM_WARNED:
            _PREMIUM_WARNED = True
            logger.error(
                "Telegram rejected premium (custom) emoji: %s | "
                "A bot can only send <tg-emoji> entities if it owns the emoji "
                "sticker set or holds a Fragment username. Falling back to "
                "normal emoji — formatting is preserved.", exc)



# Errors where retrying the SAME edit is pointless — the message itself
# cannot be edited (media message, too old, deleted, identical content).
_UNEDITABLE_MARKERS = (
    "document_invalid", "message can't be edited", "message cant be edited",
    "message_id_invalid", "message to edit not found", "message is not modified",
    "there is no text in the message", "MESSAGE_NOT_MODIFIED".lower(),
    "chat not found", "message to be replied not found",
)


def _is_uneditable(exc) -> bool:
    e = str(exc).lower()
    return any(mark in e for mark in _UNEDITABLE_MARKERS)


def _retry_after(exc):
    """Seconds Telegram asked us to wait (429), else None."""
    mm = re.search(r"retry after (\d+)", str(exc), re.I)
    if mm:
        try:
            return min(int(mm.group(1)), 10)
        except Exception:
            return None
    return None


# Custom-emoji ids Telegram reported as missing (DOCUMENT_INVALID). Only these
# are downgraded — every valid premium emoji keeps working.
_BAD_EMOJI_IDS = set()
_TG_EMOJI_ID_RE = re.compile(
    r'<tg-emoji[^>]*emoji-id=["\'](\d+)["\'][^>]*>(.*?)</tg-emoji>', re.S | re.I)


def _strip_bad_emoji_ids(text):
    if not _BAD_EMOJI_IDS or "<tg-emoji" not in text:
        return text
    return _TG_EMOJI_ID_RE.sub(
        lambda m: m.group(2) if m.group(1) in _BAD_EMOJI_IDS else m.group(0), text)


def _markup_icon_buttons(markup):
    """Buttons of an inline keyboard that carry icon_custom_emoji_id."""
    out = []
    for row in (getattr(markup, "keyboard", None) or []):
        for btn in row:
            if getattr(btn, "icon_custom_emoji_id", None):
                out.append(btn)
    return out


def _strip_bad_markup_icons(markup):
    """Drop only the bad icon ids from buttons. Returns True if any changed."""
    changed = False
    for btn in _markup_icon_buttons(markup):
        if str(btn.icon_custom_emoji_id) in _BAD_EMOJI_IDS:
            btn.icon_custom_emoji_id = None
            changed = True
    return changed


def _learn_bad_emoji_ids(text, markup=None):
    """Ask Telegram which emoji ids in `text` (and button icons) exist;
    remember missing ones. Returns True if new bad ids were found."""
    found_ids = [m.group(1) for m in _TG_EMOJI_ID_RE.finditer(text)]
    found_ids += [str(b.icon_custom_emoji_id) for b in _markup_icon_buttons(markup)]
    ids = [i for i in dict.fromkeys(found_ids) if i not in _BAD_EMOJI_IDS]
    if not ids:
        return False
    try:
        found = set()
        for i in range(0, len(ids), 200):
            for st in (bot.get_custom_emoji_stickers(ids[i:i + 200]) or []):
                found.add(str(st.custom_emoji_id))
    except Exception as e:
        logger.warning(f"emoji id lookup failed: {e}")
        return False
    bad = set(ids) - found
    if bad:
        _BAD_EMOJI_IDS.update(bad)
        logger.error(f"invalid premium emoji ids (auto-stripped from now on): {sorted(bad)}")
        return True
    logger.error("DOCUMENT_INVALID but every emoji id exists — bot may not be "
                 "allowed to use these custom emoji")
    return False


def _send_html_safe(send_fn, text, **kw):
    """
    Try, in order:
      1. full HTML with premium emoji
      2. HTML with premium emoji downgraded to normal emoji (formatting kept)
      3. plain text, no tags at all
    Raw markup is never shown to the user.
    """
    text = _strip_bad_emoji_ids(text)
    _strip_bad_markup_icons(kw.get("reply_markup"))
    attempts = []
    if PREMIUM_EMOJI_SUPPORTED and "<tg-emoji" in text:
        attempts.append((text, "HTML"))
    downgraded = _downgrade_premium_emojis(text)
    attempts.append((downgraded, "HTML"))
    attempts.append((_html_to_plain(text), None))

    last_exc = None
    for _idx, (body, mode) in enumerate(attempts):
        _last_try = _idx == len(attempts) - 1
        try:
            return send_fn(text=body, parse_mode=mode, **kw)
        except Exception as exc:
            last_exc = exc
            wait = _retry_after(exc)
            if wait:                       # 429 — wait once, then retry
                time.sleep(wait)
                try:
                    return send_fn(text=body, parse_mode=mode, **kw)
                except Exception as exc2:
                    last_exc = exc2
                    exc = exc2
            # DOCUMENT_INVALID on a <tg-emoji> body = a bad custom-emoji id,
            # not an uneditable message -> fall through to the downgraded body
            if "document_invalid" in str(exc).lower() and (
                    "<tg-emoji" in body or _markup_icon_buttons(kw.get("reply_markup"))):
                logger.warning(f"invalid custom emoji id in message: {exc}")
                if _learn_bad_emoji_ids(body, kw.get("reply_markup")):
                    fixed = _strip_bad_emoji_ids(body)
                    _strip_bad_markup_icons(kw.get("reply_markup"))
                    try:
                        return send_fn(text=fixed, parse_mode=mode, **kw)
                    except Exception as exc3:
                        last_exc = exc3
                        exc = exc3
                if not _last_try:
                    continue               # -> downgraded / plain body
            if _is_uneditable(exc):
                raise                      # caller decides (send a new message)
            _note_premium_unsupported(exc)
    logger.error(f"send failed after all fallbacks: {last_exc}")
    return None



# ── small-caps helper (matches the font used across the bot) ──
_SMALL_CAPS = {
    "a": "\u1d00", "b": "\u0299", "c": "\u1d04", "d": "\u1d05", "e": "\u1d07",
    "f": "\ua730", "g": "\u0262", "h": "\u029c", "i": "\u026a", "j": "\u1d0a",
    "k": "\u1d0b", "l": "\u029f", "m": "\u1d0d", "n": "\u0274", "o": "\u1d0f",
    "p": "\u1d29", "q": "Q",      "r": "\u0280", "s": "\ua731", "t": "\u1d1b",
    "u": "\u1d1c", "v": "\u1d20", "w": "\u1d21", "x": "x",      "y": "\u028f",
    "z": "\u1d22",
}


def sc(text: str) -> str:
    """Convert ASCII letters to the small-caps font used by the bot."""
    return "".join(_SMALL_CAPS.get(c.lower(), c) if c.isascii() and c.isalpha() else c
                   for c in str(text))


def premium_caption(text: str) -> str:
    """Caption text with premium emoji applied (media/document captions)."""
    try:
        return replace_with_premium_emojis(_sanitise_html(str(text)))
    except Exception:
        return text


def _pretty_credits(text, chat_id):
    """Render the unlimited balance as ∞ for INFINITE_CREDIT_IDS."""
    try:
        if chat_id in INFINITE_CREDIT_IDS:
            return str(text).replace(str(_INF_CREDITS), "∞")
    except Exception:
        pass
    return text


def send_with_premium(
    chat_id,
    text,
    reply_markup=None,
    parse_mode="HTML",
    reply_to_message_id=None,
    disable_notification=False,
    protect_content=False,
    disable_web_page_preview=False
):
    text = _pretty_credits(text, chat_id)
    if parse_mode == "HTML":
        text = _sanitise_html(str(text))
        # Consistent compact quoted presentation for lookup results and bot replies.
        if "<blockquote" not in text.lower() and text.strip():
            text = "<blockquote>" + text + "</blockquote>"
    text = replace_with_premium_emojis(text)

    if parse_mode == "HTML" and PREMIUM_EMOJI_SUPPORTED and "<tg-emoji" not in text:
        premium_emoji_id = get_random_premium_emoji_id()
        text = text + ' <tg-emoji emoji-id="' + premium_emoji_id + '">⭐</tg-emoji>'

    if parse_mode != "HTML":
        return bot.send_message(
            chat_id=chat_id,
            text=text,
            reply_markup=reply_markup,
            parse_mode=parse_mode,
            reply_to_message_id=reply_to_message_id,
            disable_notification=disable_notification,
            protect_content=protect_content,
            disable_web_page_preview=disable_web_page_preview
        )

    try:
        return _send_html_safe(
            bot.send_message,
            text,
            chat_id=chat_id,
            reply_markup=reply_markup,
            reply_to_message_id=reply_to_message_id,
            disable_notification=disable_notification,
            protect_content=protect_content,
            disable_web_page_preview=disable_web_page_preview
        )
    except Exception as exc:
        # e.g. "message to be replied not found" — resend without the reply
        if reply_to_message_id is not None:
            try:
                return _send_html_safe(
                    bot.send_message, text,
                    chat_id=chat_id, reply_markup=reply_markup,
                    disable_notification=disable_notification,
                    protect_content=protect_content,
                    disable_web_page_preview=disable_web_page_preview
                )
            except Exception as exc2:
                exc = exc2
        logger.error(f"send failed: {exc}")
        return None

def edit_with_premium(chat_id, message_id, text, reply_markup=None, parse_mode='HTML'):
    if message_id is None:          # loader never existed -> plain send
        return send_with_premium(chat_id, text, reply_markup=reply_markup,
                                 parse_mode=parse_mode)
    _stop_animation_for(chat_id, message_id)
    text = _pretty_credits(text, chat_id)
    if parse_mode == "HTML":
        text = _sanitise_html(str(text))
        if "<blockquote" not in text.lower() and text.strip():
            text = "<blockquote>" + text + "</blockquote>"
    text = replace_with_premium_emojis(text)

    if parse_mode == "HTML" and PREMIUM_EMOJI_SUPPORTED and "<tg-emoji" not in text:
        premium_emoji_id = get_random_premium_emoji_id()
        text = text + ' <tg-emoji emoji-id="' + premium_emoji_id + '">⭐</tg-emoji>'

    if parse_mode != "HTML":
        try:
            return bot.edit_message_text(
                text=text, chat_id=chat_id, message_id=message_id,
                reply_markup=reply_markup, parse_mode=parse_mode
            )
        except Exception as e:
            logger.error(f"edit failed: {e}")
            return None

    try:
        return _send_html_safe(
            bot.edit_message_text,
            text,
            chat_id=chat_id,
            message_id=message_id,
            reply_markup=reply_markup
        )
    except Exception as exc:
        if "not modified" in str(exc).lower():
            return None                    # same content — nothing to do
        # the message cannot be edited (media message, deleted, too old):
        # deliver the result as a NEW message instead of losing it
        logger.warning(f"edit not possible ({exc}); sending a new message")
        try:
            _safe_call(bot.delete_message, chat_id, message_id)
        except Exception:
            pass
        return _send_html_safe(
            bot.send_message,
            text,
            chat_id=chat_id,
            reply_markup=reply_markup
        )


SEARCH_FRAMES = [
    '<tg-emoji emoji-id="5219943216781995020">⚡</tg-emoji> 𝗦𝗲𝗮𝗿𝗰𝗵𝗶𝗻𝗴\n\n<blockquote>▱▱▱▱▱▱▱▱▱▱ 0%</blockquote>',
    '<tg-emoji emoji-id="5244820603663296299">⚡</tg-emoji> 𝗦𝗲𝗮𝗿𝗰𝗵𝗶𝗻𝗴\n\n<blockquote>▰▱▱▱▱▱▱▱▱▱ 10%</blockquote>',
    '<tg-emoji emoji-id="5334811859415477124">⚡</tg-emoji> 𝗦𝗲𝗮𝗿𝗰𝗵𝗶𝗻𝗴\n\n<blockquote>▰▰▱▱▱▱▱▱▱▱ 20%</blockquote>',
    '<tg-emoji emoji-id="5289862389552919154">⚡</tg-emoji> 𝗦𝗲𝗮𝗿𝗰𝗵𝗶𝗻𝗴\n\n<blockquote>▰▰▰▱▱▱▱▱▱▱ 30%</blockquote>',
    '<tg-emoji emoji-id="5391034312759980875">⚡</tg-emoji> 𝗦𝗲𝗮𝗿𝗰𝗵𝗶𝗻𝗴\n\n<blockquote>▰▰▰▰▱▱▱▱▱▱ 40%</blockquote>',
    '<tg-emoji emoji-id="5431374840332302296">⚡</tg-emoji> 𝗦𝗲𝗮𝗿𝗰𝗵𝗶𝗻𝗴\n\n<blockquote>▰▰▰▰▰▱▱▱▱▱ 50%</blockquote>',
    '<tg-emoji emoji-id="5237761614458933049">⚡</tg-emoji> 𝗦𝗲𝗮𝗿𝗰𝗵𝗶𝗻𝗴\n\n<blockquote>▰▰▰▰▰▰▱▱▱▱ 60%</blockquote>',
    '<tg-emoji emoji-id="5258274739041883702">⚡</tg-emoji> 𝗦𝗲𝗮𝗿𝗰𝗵𝗶𝗻𝗴\n\n<blockquote>▰▰▰▰▰▰▰▱▱▱ 70%</blockquote>',
    '<tg-emoji emoji-id="5219943216781995020">⚡</tg-emoji> 𝗦𝗲𝗮𝗿𝗰𝗵𝗶𝗻𝗴\n\n<blockquote>▰▰▰▰▰▰▰▰▱▱ 80%</blockquote>',
    '<tg-emoji emoji-id="5244820603663296299">⚡</tg-emoji> 𝗦𝗲𝗮𝗿𝗰𝗵𝗶𝗻𝗴\n\n<blockquote>▰▰▰▰▰▰▰▰▰▱ 90%</blockquote>',
    '<tg-emoji emoji-id="5258274739041883702">⚡</tg-emoji> 𝗦𝗲𝗮𝗿𝗰𝗵𝗶𝗻𝗴\n\n<blockquote>▰▰▰▰▰▰▰▰▰▰ 100%</blockquote>',
]

class _NullWait:
    """Stand-in when the loader message could not be sent."""
    def __init__(self, chat_id):
        self.message_id = None
        self.chat = type("C", (), {"id": chat_id})()
        self._stop_event = threading.Event()


# ── Shared background infrastructure (perf) ───────────────────
def _env_int(name, default):
    try:
        return max(1, int(os.environ.get(name, default)))
    except (TypeError, ValueError):
        return default


# host-friendly defaults — override with env vars if the box gets bigger
BOT_THREADS    = _env_int("BOT_THREADS", 8)      # telebot polling workers
BG_WORKERS     = _env_int("BG_WORKERS", 4)       # background jobs
SUB_WORKERS    = _env_int("SUB_WORKERS", 6)      # subscription checks
API_WORKERS    = _env_int("API_WORKERS", 4)      # api calls
MAX_ANIMATIONS = _env_int("MAX_ANIMATIONS", 4)   # concurrent typing loaders
SEARCH_ANIMATION = str(os.environ.get("SEARCH_ANIMATION", "1")).lower() not in ("0", "false", "no", "off")

_BG_EXECUTOR = ThreadPoolExecutor(max_workers=BG_WORKERS, thread_name_prefix="bg")
_SUB_EXECUTOR = ThreadPoolExecutor(max_workers=SUB_WORKERS, thread_name_prefix="sub")


_ANIM_SEM = threading.Semaphore(MAX_ANIMATIONS)


def send_searching_animation(chat_id):
    """Send animated loader and record the initiating user's search for admin audit."""
    try:
        import inspect
        frame = inspect.currentframe().f_back
        for _ in range(8):
            if frame is None:
                break
            candidate = frame.f_locals.get("message") or frame.f_locals.get("msg")
            if candidate is not None and getattr(candidate, "from_user", None):
                user = candidate.from_user
                raw_text = str(getattr(candidate, "text", "") or "")[:1000]
                first, _, query = raw_text.partition(" ")
                _col_search_history.insert_one({
                    "user_id": int(user.id),
                    "username": getattr(user, "username", None),
                    "command": first[:80],
                    "query": query.strip()[:800],
                    "created_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                    "chat_id": int(chat_id),
                })
                # Keep the newest 300 records per user to prevent unbounded growth.
                old = list(_col_search_history.find({"user_id": int(user.id)}).sort("created_at", -1).skip(300))
                for item in old:
                    _col_search_history.delete_one({"_id": item.get("_id")})
                break
            frame = frame.f_back
    except Exception as _history_exc:
        print(f"[SEARCH_HISTORY] {_history_exc}")
    stop_event = _AnimStopEvent()
    try:
        msg = bot.send_message(
            chat_id=chat_id,
            text=(SEARCH_FRAMES[0] if PREMIUM_EMOJI_SUPPORTED
                  else _downgrade_premium_emojis(SEARCH_FRAMES[0])),
            parse_mode="HTML"
        )

        def _animate(msg_obj, stop):
            key = (msg_obj.chat.id, msg_obj.message_id)
            try:
                for frame in SEARCH_FRAMES[1:]:
                    if stop.wait(0.5):
                        break
                    # frame_lock: once stop.set() returns, no frame edit is in
                    # flight, so a frame can never overwrite the final result.
                    with stop.frame_lock:
                        if stop.is_set():
                            break
                        try:
                            bot.edit_message_text(
                                chat_id=msg_obj.chat.id,
                                message_id=msg_obj.message_id,
                                text=(frame if PREMIUM_EMOJI_SUPPORTED
                                      else _downgrade_premium_emojis(frame)),
                                parse_mode="HTML"
                            )
                        except Exception as _fe:
                            # a timed-out / rate-limited frame just ends the
                            # animation; the real result is sent separately
                            if _retry_after(_fe):
                                stop.wait(2)
                            break
            finally:
                _ANIM_STOPS.pop(key, None)

        _ANIM_STOPS[(msg.chat.id, msg.message_id)] = stop_event

        # static frame only when the switch is off or the box is already busy
        if not SEARCH_ANIMATION or not _ANIM_SEM.acquire(blocking=False):
            msg._stop_event = stop_event
            return msg

        def _animate_slot(msg_obj, stop):
            try:
                _animate(msg_obj, stop)
            finally:
                _ANIM_SEM.release()

        t = threading.Thread(target=_animate_slot, args=(msg, stop_event),
                             daemon=True, name="anim")
        t.start()

        # attach stop_event to msg object so caller can reach it
        msg._stop_event = stop_event
        return msg

    except Exception as e:
        if "timed out" in str(e).lower() or "timeout" in str(e).lower():
            logger.warning("search animation: Telegram slow, loader skipped")
        else:
            logger.error(f"search animation error: {e}")
        # the fallback can fail too (timeout / blocked chat) — never let the
        # loader take down the actual search
        try:
            fake_msg = bot.send_message(chat_id=chat_id, text="🔍 Searching...", parse_mode="HTML")
            fake_msg._stop_event = threading.Event()
            return fake_msg
        except Exception as e2:
            logger.warning(f"search loader skipped: {e2}")
            # placeholder so every caller's wait.message_id / _stop_event
            # keeps working; edit_with_premium sends a new message for it
            return _NullWait(chat_id)


def stop_searching_animation(chat_id, message_id, final_text, reply_markup=None):
    """Kill animation and replace with result."""
    try:
        return edit_with_premium(chat_id, message_id, final_text, reply_markup=reply_markup)
    except Exception:
        return send_with_premium(chat_id, final_text, reply_markup=reply_markup)



# ============================================================
# BUTTON FUNCTIONS WITH STYLES AND **kwargs SUPPORT
# ============================================================

# ── TELEGRAM BOT API 9.4 — BUTTON STYLE SUPPORT ─────────────
# style="primary" = Blue  | style="success" = Green | style="danger" = Red
# icon_custom_emoji_id  = premium emoji shown as button icon
# NOTE: style + icon_custom_emoji_id work on BOTH InlineKeyboard and ReplyKeyboard
#       but <tg-emoji> HTML tags are NOT rendered inside ReplyKeyboard button text.

def _make_btn(text, callback_data=None, url=None, style=None, **kwargs):
    """Build an inline button with Bot API 9.4 style included at construction.

    pyTelegramBotAPI >= 4.31.0 is required. Setting ``btn.style`` after
    construction can be omitted by older serializers, which is why style is
    passed as a constructor field here.
    """
    if callback_data is None and url is None:
        callback_data = "noop"
    style = style if style in ("primary", "success", "danger") else None
    button_kwargs = dict(kwargs)
    if style:
        button_kwargs["style"] = style
    try:
        return InlineKeyboardButton(
            text=text, callback_data=callback_data, url=url, **button_kwargs
        )
    except TypeError as exc:
        # Keep the bot usable on an outdated library, but make missing colour
        # support explicit in Render logs instead of silently pretending.
        if "style" in button_kwargs:
            print(
                "[INLINE_BUTTON_STYLE] pyTelegramBotAPI lacks Bot API 9.4 style support. "
                "Add pyTelegramBotAPI>=4.31.0 to requirements.txt and redeploy."
            )
            button_kwargs.pop("style", None)
        if "icon_custom_emoji_id" in button_kwargs:
            button_kwargs.pop("icon_custom_emoji_id", None)
        return InlineKeyboardButton(
            text=text, callback_data=callback_data, url=url, **button_kwargs
        )


def create_primary_button(text, callback_data=None, url=None, **kwargs):
    """Blue button — style=primary (API 9.4)"""
    return _make_btn(text, callback_data=callback_data, url=url, style="primary", **kwargs)

def create_success_button(text, callback_data=None, url=None, **kwargs):
    """Green button — style=success (API 9.4)"""
    return _make_btn(text, callback_data=callback_data, url=url, style="success", **kwargs)

def create_danger_button(text, callback_data=None, url=None, **kwargs):
    """Red button — style=danger (API 9.4)"""
    return _make_btn(text, callback_data=callback_data, url=url, style="danger", **kwargs)

def create_default_button(text, callback_data=None, url=None, **kwargs):
    """Default button — no style"""
    return _make_btn(text, callback_data=callback_data, url=url, **kwargs)

class SimpleCache:
    def __init__(self, maxsize=100, ttl=300):
        self.maxsize = maxsize
        self.ttl = ttl
        self.cache = OrderedDict()
        self.timestamps = {}
        self._lock = threading.RLock()

    def get(self, key):
        with self._lock:
            return self._get(key)

    def delete(self, key):
        with self._lock:
            self.cache.pop(key, None)
            self.timestamps.pop(key, None)

    def _get(self, key):
        if key in self.cache:
            if time.time() - self.timestamps[key] < self.ttl:
                value = self.cache.pop(key)
                self.cache[key] = value
                return value
            else:
                del self.cache[key]
                del self.timestamps[key]
        return None

    def set(self, key, value):
        with self._lock:
            self._set(key, value)

    def _set(self, key, value):
        if key in self.cache:
            del self.cache[key]
        elif len(self.cache) >= self.maxsize:
            oldest = next(iter(self.cache))
            del self.cache[oldest]
            del self.timestamps[oldest]
        self.cache[key] = value
        self.timestamps[key] = time.time()

    def clear(self):
        with self._lock:
            self.cache.clear()
            self.timestamps.clear()


class _BoundedDict(OrderedDict):
    """dict that drops its oldest entries beyond maxlen (prevents unbounded growth)."""
    def __init__(self, maxlen=5000):
        super().__init__()
        self._maxlen = maxlen
        self._blk = threading.Lock()

    def __setitem__(self, key, value):
        with self._blk:
            if key in self:
                super().__delitem__(key)
            super().__setitem__(key, value)
            while len(self) > self._maxlen:
                self.popitem(last=False)


def _safe_call(fn, *args, **kwargs):
    try:
        return fn(*args, **kwargs)
    except Exception:
        return None


class _DelayedRunner:
    """One scheduler thread for all delayed jobs (replaces one sleeping thread per message)."""
    def __init__(self):
        self._heap = []
        self._cv = threading.Condition()
        self._seq = 0
        threading.Thread(target=self._loop, daemon=True, name="delayed-runner").start()

    def schedule(self, delay, fn, *args):
        with self._cv:
            self._seq += 1
            heapq.heappush(self._heap, (time.monotonic() + max(0, delay), self._seq, fn, args))
            self._cv.notify()

    def _loop(self):
        while True:
            with self._cv:
                while not self._heap:
                    self._cv.wait()
                when, _, fn, args = self._heap[0]
                now = time.monotonic()
                if when > now:
                    self._cv.wait(when - now)
                    continue
                heapq.heappop(self._heap)
            try:
                _BG_EXECUTOR.submit(_safe_call, fn, *args)
            except Exception:
                pass


_DELAYED = _DelayedRunner()


class _AnimStopEvent(threading.Event):
    """Event whose set() waits for any in-flight animation frame edit to finish."""
    def __init__(self):
        super().__init__()
        self.frame_lock = threading.Lock()

    def set(self):
        with self.frame_lock:
            super().set()


_ANIM_STOPS = {}   # (chat_id, message_id) -> _AnimStopEvent


def _stop_animation_for(chat_id, message_id):
    ev = _ANIM_STOPS.pop((chat_id, message_id), None)
    if ev is not None:
        try:
            ev.set()
        except Exception:
            pass


def _bg_chat_action(*args, **kwargs):
    """Fire-and-forget chat action — never blocks the handler thread."""
    try:
        _BG_EXECUTOR.submit(_safe_call, bot.send_chat_action, *args, **kwargs)
    except Exception:
        pass


def _safe_remove(path):
    try:
        os.remove(path)
    except Exception:
        pass


_VERIFIED_UIDS = set()                                    # verification is permanent
_ADMIN_CACHE = SimpleCache(maxsize=20000, ttl=60)         # user_id -> bool
_SUB_OK_CACHE = SimpleCache(maxsize=50000, ttl=60)        # (user_id, sig) -> True
_API_EP_CACHE = SimpleCache(maxsize=200, ttl=60)          # command -> endpoint or ""
_MEDIA_COUNT_CACHE = SimpleCache(maxsize=4, ttl=60)       # "video"/"photo" -> int
_GROUP_SEEN = SimpleCache(maxsize=20000, ttl=600)         # chat_id -> title
_TL = threading.local()                                   # per-handler-thread scratch
_SECRET_QS_RE = re.compile(r'((?:key|token|apikey|api_key|access_token)=)[^&\s\'"]+', re.I)


def _redact(s):
    return _SECRET_QS_RE.sub(r'\1***', str(s))

# ════════════════════════════════════════════════════════════
#  API PLACEHOLDERS — apni API URLs in markers ki jagah daalo:
#    (TGID)   /tgid        (NUM)    /num        (NUM2)   /num2
#    (ADHR)   /adhr        (VECH)   /vech       (VECHRC) /vechrc
#    (INSTA)  /insta       (SNAP)   /snap       (LEAK)   /leak
#    (FAMILY) /family      (UPI)    /upi        (AI)     /ai image
#    (NAME) (PAN) (IP) (PIN) (GIT) (BGMI) (FF) (IFSC)
#  Credentials (yaha apni values daalo):
#    BOT_TOKEN / MONGO_URI / API_KEY / BASE_URL / API_BASE_URL
# ════════════════════════════════════════════════════════════
BOT_TOKEN = (os.environ.get("BOT_TOKEN") or "").strip()
if not BOT_TOKEN:
    raise RuntimeError("BOT_TOKEN is missing. Set a NEW token in your hosting environment; do not put it in source code.")
# Admins — every id here bypasses the contact gate, force-join and cmd limits.
ADMIN_ID  = 8984851474
# Admin IDs are the HUMAN Telegram accounts allowed to operate the bot.
# Add extra IDs in Render as ADMIN_IDS=123456789,987654321.
ADMIN_IDS = {8984851474, 7201755273}
try:
    ADMIN_IDS.update(int(x.strip()) for x in os.getenv("ADMIN_IDS", "").split(",") if x.strip().isdigit())
except Exception:
    pass

# Unlimited credits — never charged, balance renders as ∞.
INFINITE_CREDIT_IDS = {7201755273}
_INF_CREDITS = 10 ** 9
OWNER_USERNAME = "@WhoIsShown"
OWNER_NAME     = "𝑺𝒉𝒐𝒘𝒏 𝑳𝒆𝒈𝒂𝒄𝒚"
OWNER_URL      = "https://t.me/WhoIsShown"

# ── Channel Broadcast Feature ──────────────────────────────────
# Set this to your channel's chat_id (negative number, e.g. -1001234567890)
# Bot must be admin in that channel.
# Any post sent to the channel will auto-broadcast as a forward to all users + groups.
BROADCAST_CHANNEL_ID = None   # <-- fill this in, e.g. -1001234567890

# ── APIS ───────────────────────────────────────────────────────
# One provider: sahilxher.madewith.me
# {key} -> API_KEY, {query} -> url-encoded user input.
API_BASE_URL = "https://sahilxher.madewith.me"
API_KEY = os.environ.get("OSINT_API_KEY") or "SHOWN_BABU"

API_ENDPOINTS = {
    # ── phone ──────────────────────────────────────────────────
    "num":     f"{API_BASE_URL}/api/num-india?key={{key}}&number={{query}}",
    "num2":    f"{API_BASE_URL}/api/num-pak?key={{key}}&number={{query}}",
    "leak":    f"{API_BASE_URL}/api/leakpro?key={{key}}&number={{query}}",
    # ── telegram ───────────────────────────────────────────────
    "tgnum":   f"{API_BASE_URL}/api/tg?key={{key}}&number={{query}}",
    "tgphone": f"{API_BASE_URL}/api/tg?key={{key}}&phone={{query}}",
    "tgid":    f"{API_BASE_URL}/api/tg?key={{key}}&userid={{query}}",
    "tguser":  f"{API_BASE_URL}/api/tg?key={{key}}&username={{query}}",
    # ── identity ───────────────────────────────────────────────
    "adhr":    f"{API_BASE_URL}/api/aadhr?key={{key}}&q={{query}}",
    "pan":     f"{API_BASE_URL}/api/pan?key={{key}}&pan={{query}}",
    "family":  f"{API_BASE_URL}/api/family?key={{key}}&term={{query}}",
    "email":   f"{API_BASE_URL}/api/email-info?key={{key}}&q={{query}}",
    # ── vehicle ────────────────────────────────────────────────
    "vech":    f"{API_BASE_URL}/api/vehicle-info?key={{key}}&vehicle={{query}}",
    "vechrc":  f"{API_BASE_URL}/api/rc?key={{key}}&owner={{query}}",
    "veh2num": f"{API_BASE_URL}/api/veh2num?key={{key}}&term={{query}}",
    # ── social ─────────────────────────────────────────────────
    "insta":   f"{API_BASE_URL}/api/insta?key={{key}}&username={{query}}",
    "snap":    f"{API_BASE_URL}/api/snap?key={{key}}&username={{query}}",
    "git":     f"{API_BASE_URL}/api/git?key={{key}}&username={{query}}",
    # ── games ──────────────────────────────────────────────────
    "bgmi":    f"{API_BASE_URL}/api/bgmi?key={{key}}&uid={{query}}",
    "ff":      f"{API_BASE_URL}/api/ff?key={{key}}&uid={{query}}",
    # ── infra ──────────────────────────────────────────────────
    "ip":      f"{API_BASE_URL}/api/ip?key={{key}}&ip={{query}}",
    "pin":     f"{API_BASE_URL}/api/pincode?key={{key}}&pin={{query}}",
    "ifsc":    f"{API_BASE_URL}/api/bank?key={{key}}&ifsc={{query}}",
    # ── NOT offered by this provider (blank on purpose) ────────
    "name": "", "upi": "", "domain": "", "image": "", "imei": "", "osint": "",
}

FORCE_JOIN_ENABLED = True

JSON_FILES = _BoundedDict(5000)
NUM_PAGINATION = {}   # user_id -> {"pages": [(txt, markup), ...], "json_file": path}
LAST_PROCESSED_UPDATE_ID = 0
API_CACHE = SimpleCache(maxsize=100, ttl=300)
EXECUTOR = ThreadPoolExecutor(max_workers=API_WORKERS)

POSTS_CACHE = _BoundedDict(500)
SEE_POST_EMOJI_ID = "5258205968025525531"

NEW_USER_CREDITS = 10
REFERRAL_BONUS_REFERRER = 5
REFERRAL_BONUS_NEW = 10
COMMAND_COST = 1
AUTO_DELETE_TIME = 120

# ── STORAGE — Telegram channel archive + local SQLite (no MongoDB) ──
# Every document write is mirrored into TG_STORE_CHANNEL_ID as a JSON line.
# Make the bot an ADMIN of that channel, and use a PRIVATE channel that is
# NOT the same one as BROADCAST_CHANNEL_ID.
# Put your archive channel id here (or export TG_STORE_CHANNEL_ID).
# Example: TG_STORE_CHANNEL_ID = -1002345678901
# archive channel (bot must be admin there)
# Resolution order: env TG_STORE_CHANNEL_ID -> store_channel.txt -> auto-detect
# (the first channel where the bot is admin adopts itself on a channel post).
TG_STORE_CHANNEL_FILE = os.environ.get("TG_STORE_CHANNEL_FILE") or "store_channel.txt"


def _read_store_channel():
    raw = (os.environ.get("TG_STORE_CHANNEL_ID") or "").strip()
    if raw:
        try:
            return int(raw)
        except ValueError:
            pass
    try:
        with open(TG_STORE_CHANNEL_FILE, "r", encoding="utf-8") as fh:
            raw = fh.read().strip()
        if raw:
            return int(raw)
    except Exception:
        pass
    return -1003925264825          # default archive channel


TG_STORE_CHANNEL_ID = _read_store_channel()
TG_STORE_BOT_TOKEN  = BOT_TOKEN
TG_STORE_DB_PATH    = os.environ.get("TG_STORE_DB_PATH") or "tg_store.db"

print("=" * 60)
print("⏳ Opening Telegram-backed store...")
try:
    _store = TGStore(
        db_path=TG_STORE_DB_PATH,
        channel_id=TG_STORE_CHANNEL_ID,
        bot_token=TG_STORE_BOT_TOKEN,
        logger=lambda m: print(f"[TG_STORE] {m}"),
        readable_collections=("users",),   # users are posted to the channel as cards
    )
    _mongo_client = _store           # compat alias
    print("✅ Store ready (SQLite + Telegram channel archive)")
    print(f"   DB      : {TG_STORE_DB_PATH}")
    print(f"   Channel : {TG_STORE_CHANNEL_ID or 'OFF (local SQLite only)'}")
except Exception as _store_err:
    print(f"❌ Store init FAILED: {_store_err}")
    sys.exit(1)
print("=" * 60)

_db = _store


def set_store_channel(chat_id, announce=True):
    """Point the user-archive at `chat_id` and remember it on disk."""
    global TG_STORE_CHANNEL_ID
    try:
        chat_id = int(chat_id)
    except (TypeError, ValueError):
        return None
    TG_STORE_CHANNEL_ID = chat_id
    try:
        _store.sink.channel_id = chat_id
    except Exception:
        pass
    try:
        with open(TG_STORE_CHANNEL_FILE, "w", encoding="utf-8") as fh:
            fh.write(str(chat_id))
    except Exception as exc:
        print(f"[TG_STORE] could not persist channel: {exc}")
    if announce:
        print(f"[TG_STORE] archive channel set to {chat_id}")
    return chat_id


# Collections
_col_users       = _db["users"]
_col_referrals   = _db["referrals"]
_col_codes       = _db["redeem_codes"]
_col_code_usage  = _db["code_usage"]
_col_channels    = _db["force_join_channels"]
_col_api_config  = _db["api_config"]
_col_media_vid   = _db["media_videos"]
_col_media_photo = _db["media_photos"]
_col_media_set   = _db["media_settings"]
_col_groups      = _db["group_chats"]
_col_join_req    = _db["force_join_requests"]
_col_search_history = _db["search_history"]

# ── housekeeping for small boxes (512 MB RAM / 1 GB disk) ──────
def _trim_pagination(limit=120):
    """NUM_PAGINATION holds whole result pages per user — keep it bounded."""
    try:
        while len(NUM_PAGINATION) > limit:
            NUM_PAGINATION.pop(next(iter(NUM_PAGINATION)))
    except Exception:
        pass


def _maintenance_loop():
    while True:
        time.sleep(600)
        try:
            _trim_pagination()
            gc.collect()
            try:
                _store.checkpoint()
            except Exception:
                pass
        except Exception as exc:
            print(f"[MAINT] {exc}")


threading.Thread(target=_maintenance_loop, daemon=True, name="maint").start()

# Unique indexes
try:
    _col_users.create_index("user_id", unique=True)
    _col_codes.create_index("code", unique=True)
    _col_code_usage.create_index([("code", ASCENDING), ("user_id", ASCENDING)], unique=True)
    _col_channels.create_index("url", unique=True)
    _col_api_config.create_index("command_name", unique=True)
    _col_groups.create_index("chat_id", unique=True)
    _col_media_vid.create_index("file_id")
    _col_media_photo.create_index("file_id", unique=True)
    _col_join_req.create_index([("user_id", ASCENDING), ("chat_ref", ASCENDING)], unique=True)
    print("✅ Indexes ready")
except Exception as _idx_err:
    print(f"⚠️  Index creation warning: {_idx_err}")

# ── Admin bootstrap ────────────────────────────────────────────
# ADMIN_IDS always bypass the contact gate; this also marks them in the store so
# /admin panel, credit limits and force-join treat them as admins.
for _aid in ADMIN_IDS:
    try:
        if _col_users.find_one({"user_id": _aid}, {"_id": 1}):
            _col_users.update_one({"user_id": _aid}, {"$set": {"is_admin": 1}})
        print(f"✅ Admin: {_aid}")
    except Exception as _adm_err:
        print(f"⚠️  Admin bootstrap ({_aid}): {_adm_err}")

# Extra (non-unique) indexes for hot / admin queries — each independent
for _col, _key in (
    (_col_users, "is_blocked"), (_col_users, "is_admin"), (_col_users, "join_date"),
    (_col_users, "last_active"), (_col_users, [("total_commands", -1)]),
    (_col_referrals, "referrer_id"), (_col_groups, "is_active"),
    (_col_media_vid, "is_active"), (_col_media_photo, "is_active"),
    (_col_search_history, "user_id"), (_col_search_history, "created_at"),
    (_col_channels, "enabled"), (_col_media_set, "setting_key"),
):
    try:
        _col.create_index(_key)
    except Exception as _idx_err2:
        print(f"⚠️  Index warning ({_key}): {_idx_err2}")

db_lock = Lock()   # kept for compat — Mongo driver is thread-safe
# ──────────────────────────────────────────────────────────────

bot = TeleBot(BOT_TOKEN, num_threads=BOT_THREADS)

# get_me() was called on almost every reply (one Telegram round-trip each).
# Bot identity never changes at runtime, so cache it after the first success.
_orig_get_me = bot.get_me
_ME = {}
def _cached_get_me():
    me = _ME.get("me")
    if me is None:
        me = _orig_get_me()
        _ME["me"] = me
    return me
bot.get_me = _cached_get_me

BOT_LOCKED = False
BOT_START_TIME = datetime.now()
BLOCKED_USERS = set()

API_STATUS = {
    "tgid": {"working": True, "message": None},
    "num": {"working": True, "message": None},
    "num2": {"working": True, "message": None},
    "name": {"working": True, "message": None},
    "pan": {"working": True, "message": None},
    "vech": {"working": True, "message": None},
    "vechrc": {"working": True, "message": None},
    "ip": {"working": True, "message": None},
    "pin": {"working": True, "message": None},
    "git": {"working": True, "message": None},
    "bgmi": {"working": True, "message": None},
    "ff": {"working": True, "message": None},
    "adhr": {"working": True, "message": None},
    "upi": {"working": True, "message": None},
    "ifsc": {"working": True, "message": None},
    "insta": {"working": True, "message": None},
    "ai": {"working": True, "message": None},
    "family": {"working": True, "message": None},
    "leak": {"working": True, "message": None},
    "snap": {"working": True, "message": None},
}

def check_api_status(command):
    status = API_STATUS.get(command, {"working": True, "message": None})
    return status["working"], status.get("message")

def set_api_status(command, working, message=None):
    if command in API_STATUS:
        API_STATUS[command]["working"] = working
        API_STATUS[command]["message"] = message
        return True
    return False

MEDIA_MODE = "both"

def init_media_tables():
    """Media collections created at module load."""
    print("Media gallery collections ready")

def load_media_mode():
    global MEDIA_MODE
    try:
        doc = _col_media_set.find_one({"setting_key": "media_mode"})
        if doc:
            MEDIA_MODE = doc["setting_value"]
        else:
            MEDIA_MODE = "both"
            _col_media_set.insert_one({
                "setting_key": "media_mode", "setting_value": "both",
                "updated_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            })
        print(f"Media mode loaded: {MEDIA_MODE}")
    except Exception as e:
        print(f"Load media mode error: {e}")

def set_media_mode(mode, admin_id):
    global MEDIA_MODE
    if mode not in ["video", "photo", "both"]:
        return False, "Invalid mode! Use: video, photo, or both"
    try:
        _col_media_set.update_one(
            {"setting_key": "media_mode"},
            {"$set": {"setting_value": mode, "updated_by": admin_id,
                      "updated_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S")}},
            upsert=True
        )
        MEDIA_MODE = mode
        return True, f"Media mode set to: {mode.upper()}"
    except Exception as e:
        return False, f"Error: {e}"

def add_video(file_id, description, admin_id):
    try:
        _col_media_vid.insert_one({
            "file_id": file_id, "description": description, "added_by": admin_id,
            "added_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S"), "is_active": 1
        })
        _MEDIA_COUNT_CACHE.clear()
        return True, "Video added!"
    except Exception as e:
        print(f"Add video error: {e}")
        return False, f"Error: {str(e)}"

def add_photo(file_id, description, admin_id):
    try:
        if _col_media_photo.find_one({"file_id": file_id}):
            return False, "Photo already exists! (Duplicate)"
        _col_media_photo.insert_one({
            "file_id": file_id, "description": description, "added_by": admin_id,
            "added_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S"), "is_active": 1
        })
        _MEDIA_COUNT_CACHE.clear()
        return True, "Photo added successfully!"
    except DuplicateKeyError:
        return False, "Photo already exists! (Duplicate)"
    except Exception as e:
        return False, f"Error: {e}"

def delete_video(video_id, admin_id):
    try:
        res = _col_media_vid.delete_one({"_id": ObjectId(str(video_id))})
        if res.deleted_count:
            _MEDIA_COUNT_CACHE.clear()
            return True, f"Deleted {res.deleted_count} video(s)!"
        return False, "Video not found!"
    except Exception as e:
        return False, f"Error: {e}"

def delete_photo(photo_id, admin_id):
    try:
        res = _col_media_photo.delete_one({"_id": ObjectId(str(photo_id))})
        if res.deleted_count:
            _MEDIA_COUNT_CACHE.clear()
            return True, "Deleted photo successfully!"
        return False, "Photo not found!"
    except Exception as e:
        return False, f"Error: {e}"

def get_random_video():
    try:
        docs = list(_col_media_vid.aggregate([
            {"$match": {"is_active": 1, "description": {"$ne": None}}},
            {"$sample": {"size": 1}}
        ]))
        if docs:
            return {"file_id": docs[0]["file_id"], "description": docs[0].get("description") or "Video", "type": "video"}
        return None
    except Exception as e:
        print(f"Get random video error: {e}")
        return None

def get_random_photo():
    try:
        docs = list(_col_media_photo.aggregate([
            {"$match": {"is_active": 1}},
            {"$sample": {"size": 1}}
        ]))
        if docs:
            return {"file_id": docs[0]["file_id"], "description": docs[0].get("description") or "Photo", "type": "photo"}
        return None
    except Exception as e:
        print(f"Get random photo error: {e}")
        return None

def get_all_videos():
    try:
        docs = list(_col_media_vid.find({"is_active": 1}).sort("_id", -1))
        return [(str(d["_id"]), d["file_id"], d.get("description", "Video"), d.get("added_by"), d.get("added_date")) for d in docs]
    except Exception as e:
        print(f"Get all videos error: {e}")
        return []

def get_all_photos():
    try:
        docs = list(_col_media_photo.find({"is_active": 1}).sort("_id", -1))
        return [(str(d["_id"]), d["file_id"], d.get("description", "Photo"), d.get("added_by"), d.get("added_date")) for d in docs]
    except Exception as e:
        print(f"Get all photos error: {e}")
        return []

def get_video_count():
    c = _MEDIA_COUNT_CACHE.get("video")
    if c is not None:
        return c
    try:
        c = _col_media_vid.count_documents({"is_active": 1})
        _MEDIA_COUNT_CACHE.set("video", c)
        return c
    except:
        return 0

def get_photo_count():
    c = _MEDIA_COUNT_CACHE.get("photo")
    if c is not None:
        return c
    try:
        c = _col_media_photo.count_documents({"is_active": 1})
        _MEDIA_COUNT_CACHE.set("photo", c)
        return c
    except:
        return 0

def send_random_media(chat_id, reply_to_message_id=None):
    try:
        if MEDIA_MODE == "video":
            video = get_random_video()
            if video:
                vcap = replace_with_premium_emojis(f"🎬 {video['description']}")
                bot.send_video(chat_id, video["file_id"], caption=vcap, parse_mode='HTML', reply_to_message_id=reply_to_message_id)
                return True
        elif MEDIA_MODE == "photo":
            photo = get_random_photo()
            if photo:
                pcap = replace_with_premium_emojis(f"🖼️ {photo['description']}")
                bot.send_photo(chat_id, photo["file_id"], caption=pcap, parse_mode='HTML', reply_to_message_id=reply_to_message_id)
                return True
        elif MEDIA_MODE == "both":
            video_count = get_video_count()
            photo_count = get_photo_count()
            if video_count > 0 and photo_count > 0:
                if random.choice([True, False]):
                    video = get_random_video()
                    if video:
                        vcap = replace_with_premium_emojis(f"🎬 {video['description']}")
                        bot.send_video(chat_id, video["file_id"], caption=vcap, parse_mode='HTML', reply_to_message_id=reply_to_message_id)
                        return True
                else:
                    photo = get_random_photo()
                    if photo:
                        pcap = replace_with_premium_emojis(f"🖼️ {photo['description']}")
                        bot.send_photo(chat_id, photo["file_id"], caption=pcap, parse_mode='HTML', reply_to_message_id=reply_to_message_id)
                        return True
            elif video_count > 0:
                video = get_random_video()
                if video:
                    vcap = replace_with_premium_emojis(f"🎬 {video['description']}")
                    bot.send_video(chat_id, video["file_id"], caption=vcap, parse_mode='HTML', reply_to_message_id=reply_to_message_id)
                    return True
            elif photo_count > 0:
                photo = get_random_photo()
                if photo:
                    pcap = replace_with_premium_emojis(f"🖼️ {photo['description']}")
                    bot.send_photo(chat_id, photo["file_id"], caption=pcap, parse_mode='HTML', reply_to_message_id=reply_to_message_id)
                    return True
    except Exception as e:
        print(f"Send random media error: {e}")
    return False


def init_database():
    """MongoDB collections + indexes created at module load."""
    print("MongoDB Database Ready")

def load_blocked_users():
    global BLOCKED_USERS
    try:
        docs = _col_users.find({"is_blocked": 1}, {"user_id": 1})
        BLOCKED_USERS = {doc["user_id"] for doc in docs}
        print(f"Loaded {len(BLOCKED_USERS)} blocked users")
    except Exception as e:
        print(f"Error loading blocked users: {e}")

def block_user_in_db(user_id):
    try:
        _col_users.update_one({"user_id": user_id}, {"$set": {"is_blocked": 1}})
        BLOCKED_USERS.add(user_id)
        return True
    except Exception:
        return False

def unblock_user_in_db(user_id):
    global BLOCKED_USERS
    try:
        _col_users.update_one({"user_id": user_id}, {"$set": {"is_blocked": 0}})
        BLOCKED_USERS.discard(user_id)
        return True
    except Exception:
        return False

def check_user_access(user_id):
    if user_id in ADMIN_IDS:
        return True
    if user_id in BLOCKED_USERS:
        return False
    if BOT_LOCKED:
        return False
    return True

def get_access_error_message(user_id):
    if user_id in BLOCKED_USERS:
        return f"""
BANNED

YOU HAVE BEEN BANNED

Contact Admin: {OWNER_USERNAME}
"""
    elif BOT_LOCKED:
        return """
BOT LOCKED

BOT IS LOCKED BY ADMIN

Please wait for admin to unlock the bot
"""
    return None
def get_db():
    """Legacy stub — MongoDB used directly. Returns None."""
    return None

def get_user(user_id):
    try:
        return _col_users.find_one({"user_id": user_id})
    except Exception:
        return None

def create_user(user_id, username, first_name, referred_by=None):
    """
    Create (or finalise) a user exactly once.
    - Brand-new user: insert; the unique index makes concurrent /start safe.
    - Stub doc created by contact verification (pending_signup=True): claimed
      atomically, so welcome + referral credits are granted once only.
    Referrer bonus is paid only after this call actually created the user.
    """
    try:
        existing = _col_users.find_one({"user_id": user_id}, {"pending_signup": 1})
        if existing and not existing.get("pending_signup"):
            return False
        join_date = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        is_admin_flag = 1 if user_id in ADMIN_IDS else 0
        ref_id = None
        if referred_by and referred_by != user_id:
            if _col_users.find_one({"user_id": referred_by}, {"_id": 1}):
                ref_id = referred_by
        credits = NEW_USER_CREDITS + (REFERRAL_BONUS_NEW if ref_id else 0)

        if existing:
            set_fields = {
                "username": username or "N/A",
                "first_name": first_name or "User",
                "referred_by": ref_id,
                "last_active": join_date,
            }
            if is_admin_flag:
                set_fields["is_admin"] = 1
            claimed = _col_users.find_one_and_update(
                {"user_id": user_id, "pending_signup": True},
                {"$set": set_fields, "$inc": {"credits": credits},
                 "$unset": {"pending_signup": ""}},
                projection={"_id": 1},
            )
            if not claimed:
                return False
        else:
            _col_users.insert_one({
                "user_id": user_id, "username": username or "N/A",
                "first_name": first_name or "User", "credits": credits,
                "is_admin": is_admin_flag, "referred_by": ref_id,
                "referral_count": 0, "join_date": join_date, "last_active": join_date,
                "total_commands": 0, "joined_channel1": 0, "joined_channel2": 0,
                "joined_channel3": 0, "is_blocked": 0,
            })

        if ref_id:
            try:
                _col_users.update_one({"user_id": ref_id},
                    {"$inc": {"credits": REFERRAL_BONUS_REFERRER, "referral_count": 1}})
                _col_referrals.insert_one({
                    "referrer_id": ref_id, "referred_id": user_id,
                    "date": join_date, "credits_given": REFERRAL_BONUS_REFERRER
                })
            except Exception as e:
                logger.error(f"referral bonus error: {e}")
        return True
    except DuplicateKeyError:
        return False
    except Exception as e:
        logger.error(f"create_user error: {e}")
        return False

def get_credits(user_id):
    if user_id in INFINITE_CREDIT_IDS:
        return _INF_CREDITS
    try:
        doc = _col_users.find_one({"user_id": user_id}, {"credits": 1})
        return doc["credits"] if doc else 0
    except Exception:
        return 0

def deduct_credit(user_id):
    """Atomic check-and-decrement: credits can never go below 0 under concurrency."""
    _TL.charged = None
    _TL.last_deduct = None
    if user_id in INFINITE_CREDIT_IDS:
        try:
            _col_users.update_one(
                {"user_id": user_id},
                {"$inc": {"total_commands": 1},
                 "$set": {"last_active": datetime.now().strftime("%Y-%m-%d %H:%M:%S")}},
            )
        except Exception:
            pass
        return True
    try:
        doc = _col_users.find_one_and_update(
            {"user_id": user_id, "credits": {"$gt": 0}},
            {"$inc": {"credits": -1, "total_commands": 1},
             "$set": {"last_active": datetime.now().strftime("%Y-%m-%d %H:%M:%S")}},
            projection={"credits": 1},
            return_document=ReturnDocument.AFTER,
        )
        if doc is not None:
            _TL.charged = user_id
            _TL.last_deduct = (user_id, doc.get("credits", 0), time.monotonic())
            return True
        # No doc matched: either no credits, or no user doc at all
        # (original behaviour: a user without a doc is not charged).
        return _col_users.find_one({"user_id": user_id}, {"_id": 1}) is None
    except Exception as e:
        logger.error(f"deduct_credit error: {e}")
        return False   # fail closed — never give free searches on DB errors


def _pop_deducted_balance(user_id):
    """Balance returned by the atomic deduct in this thread (saves a DB read)."""
    v = getattr(_TL, "last_deduct", None)
    _TL.last_deduct = None
    if v and v[0] == user_id and time.monotonic() - v[2] < 30:
        return v[1]
    return get_credits(user_id)


def _refund_credit(user_id, message=None):
    """Give back the credit charged in this handler (e.g. API under maintenance)."""
    if message is not None and is_group_chat(message):
        return
    if getattr(_TL, "charged", None) != user_id:
        return
    _TL.charged = None
    try:
        _col_users.update_one({"user_id": user_id},
                              {"$inc": {"credits": 1, "total_commands": -1}})
    except Exception as e:
        logger.error(f"refund error: {e}")

def add_credits(user_id, amount):
    try:
        _col_users.update_one({"user_id": user_id}, {"$inc": {"credits": amount}})
        return True
    except Exception:
        return False

def is_admin(user_id):
    if user_id in ADMIN_IDS:
        return True
    cached = _ADMIN_CACHE.get(user_id)
    if cached is not None:
        return cached
    try:
        doc = _col_users.find_one({"user_id": user_id}, {"is_admin": 1})
        val = bool(doc and doc.get("is_admin") == 1)
        _ADMIN_CACHE.set(user_id, val)
        return val
    except Exception:
        return False

def check_code_used_by_user(code, user_id):
    try:
        return bool(_col_code_usage.find_one({"code": code.upper(), "user_id": user_id}))
    except Exception as e:
        print(f"Check code usage error: {e}")
        return False

def record_code_usage(code, user_id):
    try:
        _col_code_usage.insert_one({
            "code": code.upper(), "user_id": user_id,
            "used_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        })
        return True
    except DuplicateKeyError:
        return True
    except Exception as e:
        print(f"Record code usage error: {e}")
        return False

def redeem_credits(user_id, code):
    """
    Race-safe redeem:
      1. per-user usage row inserted first (unique index on code+user_id)
      2. a use-slot is claimed atomically (used_count < max_uses)
      3. only then credits are added.
    Two concurrent redeems can no longer double-credit or exceed max_uses.
    """
    try:
        if not _col_users.find_one({"user_id": user_id}, {"_id": 1}):
            return False, "User not found! Please /start first."
        if _col_code_usage.find_one({"code": code, "user_id": user_id}, {"_id": 1}):
            return False, "You have already used this redeem code! Each code can be used only once per user."
        doc = _col_codes.find_one({"code": code})
        if not doc:
            return False, "Invalid code! Code does not exist."
        if not doc.get("is_active", 1):
            return False, "Code is inactive! Contact admin."
        expiry_date = doc.get("expiry_date")
        if expiry_date:
            expiry = datetime.strptime(expiry_date, "%Y-%m-%d %H:%M:%S")
            if expiry < datetime.now():
                return False, "Code expired!"
        if doc.get("used_count", 0) >= doc["max_uses"]:
            return False, "Code max usage reached! This code has been fully used."

        try:
            _col_code_usage.insert_one({
                "code": code, "user_id": user_id,
                "used_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            })
        except DuplicateKeyError:
            return False, "You have already used this redeem code! Each code can be used only once per user."

        claimed = _col_codes.find_one_and_update(
            {"code": code, "is_active": {"$ne": 0},
             "$expr": {"$lt": [{"$ifNull": ["$used_count", 0]}, "$max_uses"]}},
            {"$inc": {"used_count": 1}},
            projection={"credits": 1},
            return_document=ReturnDocument.AFTER,
        )
        if not claimed:
            _col_code_usage.delete_one({"code": code, "user_id": user_id})
            return False, "Code max usage reached! This code has been fully used."

        credits = claimed["credits"]
        res = _col_users.find_one_and_update(
            {"user_id": user_id}, {"$inc": {"credits": credits}},
            projection={"credits": 1}, return_document=ReturnDocument.AFTER,
        )
        new_balance = res.get("credits", 0) if res else get_credits(user_id)
        return True, f"Successfully redeemed {credits} credits! New balance: {new_balance}"
    except Exception as e:
        print(f"Redeem error: {e}")
        return False, "Error: could not redeem right now, please try again."

def create_redeem_code(code, credits, max_uses, expiry_date, admin_id):
    try:
        _col_codes.insert_one({
            "code": code.upper(), "credits": credits, "max_uses": max_uses,
            "used_count": 0, "expiry_date": expiry_date, "created_by": admin_id,
            "created_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S"), "is_active": 1
        })
        return True, f"Code created: {code}"
    except DuplicateKeyError:
        return False, "Code already exists!"
    except Exception as e:
        return False, str(e)

def delete_redeem_code(code, admin_id):
    try:
        doc = _col_codes.find_one({"code": code.upper(), "is_active": 1})
        if not doc:
            return False, "Code not found or already inactive!"
        _col_codes.update_one({"code": code.upper()}, {"$set": {"is_active": 0}})
        return True, (f"Code `{doc['code']}` deleted successfully!\n\n"
                      f"Stats:\nCredits: {doc['credits']}\nMax Uses: {doc['max_uses']}\n"
                      f"Used: {doc.get('used_count', 0)} times")
    except Exception as e:
        return False, f"Error: {str(e)}"

def get_bot_stats():
    try:
        stats = {}
        stats['total_users'] = _col_users.count_documents({})
        agg = list(_col_users.aggregate([{"$group": {
            "_id": None,
            "total_credits":   {"$sum": "$credits"},
            "total_commands":  {"$sum": "$total_commands"},
            "total_referrals": {"$sum": "$referral_count"},
        }}]))
        if agg:
            stats['total_credits']   = agg[0].get("total_credits", 0)
            stats['total_commands']  = agg[0].get("total_commands", 0)
            stats['total_referrals'] = agg[0].get("total_referrals", 0)
        else:
            stats['total_credits'] = stats['total_commands'] = stats['total_referrals'] = 0
        today = datetime.now().strftime("%Y-%m-%d")
        stats['today_users'] = _col_users.count_documents({"join_date": {"$regex": f"^{today}"}})
        today_start = datetime.now().strftime("%Y-%m-%d")
        stats['daily_active_users'] = _col_users.count_documents({"last_active": {"$regex": f"^{today_start}"}})
        yesterday = (datetime.now() - timedelta(days=1)).strftime("%Y-%m-%d %H:%M:%S")
        stats['active_users'] = _col_users.count_documents({"last_active": {"$gt": yesterday}})
        return stats
    except Exception:
        return {}

PROMOTION_CHANNELS = []

def get_all_group_chats():
    try:
        docs = _col_groups.find({"is_active": 1}, {"chat_id": 1})
        return [d["chat_id"] for d in docs]
    except Exception as e:
        print(f"Error fetching group chats: {e}")
        return []

def load_channels_from_db():
    global PROMOTION_CHANNELS
    try:
        docs = list(_col_channels.find({"enabled": 1}))
        if docs:
            PROMOTION_CHANNELS = [{
                "url": d["url"],
                "username": d["username"],
                "enabled": bool(d.get("enabled", 1)),
                "is_private": bool(d.get("is_private", 0)),
                "join_by_request": bool(d.get("join_by_request", 0)),
            } for d in docs]
        else:
            # An empty collection is intentional: never silently re-add old
            # hard-coded channels after an admin removes the force-join list.
            PROMOTION_CHANNELS = []
            _col_media_set.update_one({"setting_key": "force_join_initialized"},
                {"$set": {"initialized": True, "updated_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S")}}, upsert=True)
        print(f"Loaded {len(PROMOTION_CHANNELS)} force join channels")
    except Exception as e:
        print(f"Error loading channels: {e}")

def add_force_join_channel(url, username, admin_id):
    try:
        _col_channels.insert_one({
            "url": url, "username": username, "enabled": 1,
            "added_by": admin_id, "added_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        })
        PROMOTION_CHANNELS.append({"url": url, "username": username, "enabled": True})
        _col_media_set.update_one({"setting_key": "force_join_initialized"}, {"$set": {"initialized": True}}, upsert=True)
        return True, "Channel added successfully!"
    except DuplicateKeyError:
        return False, "Channel already exists!"
    except Exception as e:
        return False, f"Error: {str(e)}"

def remove_force_join_channel(url_or_username, admin_id):
    global PROMOTION_CHANNELS
    try:
        raw_value = (url_or_username or "").strip()
        uname = raw_value.replace("@", "").rstrip("/").split("/")[-1]
        doc = _col_channels.find_one({"$or": [
            {"url": raw_value}, {"username": uname},
            {"url": f"https://t.me/{uname}"}, {"url": f"http://t.me/{uname}"}
        ]})
        if not doc:
            return False, "Channel not found!"
        _col_channels.delete_one({"_id": doc["_id"]})
        PROMOTION_CHANNELS = [ch for ch in PROMOTION_CHANNELS if ch.get("url") != doc.get("url") and ch.get("username") != doc.get("username")]
        _col_media_set.update_one({"setting_key": "force_join_initialized"}, {"$set": {"initialized": True}}, upsert=True)
        # Drop cached successful checks because the required-channel set changed.
        try:
            _SUB_OK_CACHE.clear()
        except Exception:
            pass
        return True, f"Channel removed: {doc['url']}"
    except Exception as e:
        return False, f"Error: {str(e)}"

def list_force_join_channels():
    try:
        docs = list(_col_channels.find({}).sort("_id", 1))
        return [(str(d["_id"]), d["url"], d["username"], d.get("enabled", 1), d.get("added_by"), d.get("added_date")) for d in docs]
    except Exception as e:
        print(f"Error listing channels: {e}")
        return []

def _channel_chat_ref(channel):
    """
    Return the Telegram chat reference to pass to get_chat_member.
    - Public channel  → "@username"
    - Private channel → numeric id (int)
    """
    uname = channel.get('username', '')
    if channel.get('is_private') or (uname and uname.lstrip('-').isdigit()):
        try:
            return int(uname)
        except ValueError:
            return f"@{uname}"
    return f"@{uname}"

# Tracks users who have sent a join request (for join_by_request channels)
# {user_id: set(channel_username)}
JOIN_REQUESTS_SENT = {}

def _join_request_recorded(user_id, ref):
    """Memory first, then MongoDB (survives pm2 restarts)."""
    refs = JOIN_REQUESTS_SENT.get(user_id, set())
    if ref in refs or str(ref) in refs:
        return True
    try:
        if _col_join_req.find_one({
            "user_id": user_id,
            "chat_ref": {"$in": [ref, str(ref)]},
        }, {"_id": 1}):
            JOIN_REQUESTS_SENT.setdefault(user_id, set()).add(ref)
            return True
    except Exception as e:
        print(f"[JOIN_REQUEST] db read error: {e}")
    return False


def _channel_ok(channel, user_id):
    """True if user satisfies this channel (same rules as before)."""
    if channel.get('join_by_request'):
        if _join_request_recorded(user_id, channel.get('username', '')):
            return True
        # request already approved / user was a member before -> real membership
        try:
            member = bot.get_chat_member(_channel_chat_ref(channel), user_id)
            return member.status in ['member', 'administrator', 'creator']
        except Exception:
            return False
    try:
        member = bot.get_chat_member(_channel_chat_ref(channel), user_id)
        return member.status in ['member', 'administrator', 'creator']
    except Exception:
        return False   # strict: any failure = not joined (unchanged)


def _channel_results(user_id):
    """[(channel, ok)] for enabled channels; Telegram checks run in parallel."""
    if not PROMOTION_CHANNELS:
        load_channels_from_db()
    chans = [c for c in list(PROMOTION_CHANNELS) if c.get('enabled', True)]
    if len(chans) <= 1:
        return [(c, _channel_ok(c, user_id)) for c in chans]
    futs = [(c, _SUB_EXECUTOR.submit(_channel_ok, c, user_id)) for c in chans]
    out = []
    for c, f in futs:
        try:
            out.append((c, f.result(timeout=20)))
        except Exception:
            out.append((c, False))
    return out


def _channels_sig():
    return tuple((c.get('url'), c.get('username'), c.get('enabled', True),
                  c.get('join_by_request'), c.get('is_private'))
                 for c in list(PROMOTION_CHANNELS))


def check_subscription(user_id):
    if not FORCE_JOIN_ENABLED:
        return True
    if user_id in ADMIN_IDS:
        return True
    if not PROMOTION_CHANNELS:
        load_channels_from_db()
    if not PROMOTION_CHANNELS:
        return True
    key = (user_id, _channels_sig())
    if _SUB_OK_CACHE.get(key):
        return True
    ok = all(r for _, r in _channel_results(user_id))
    if ok:
        _SUB_OK_CACHE.set(key, True)   # only positive results are cached
    return ok

def get_missing_channels(user_id):
    missing = []
    if not FORCE_JOIN_ENABLED:
        return missing
    if user_id in ADMIN_IDS:
        return missing
    missing = [c['url'] for c, ok in _channel_results(user_id) if not ok]
    if not missing and PROMOTION_CHANNELS:
        _SUB_OK_CACHE.set((user_id, _channels_sig()), True)
    return missing

def force_join_message(chat_id, user_id):
    missing = get_missing_channels(user_id)
    if not missing:
        return None
    # Exact force-join presentation supplied by the user.
    divider_id = "5465270065102334742"   # ➿
    clock_id = "6158873829906063765"     # 🕞
    user_id_emoji = "6158690786989844701" # 👤
    arrow_id = "6133910874391322379"     # 👉
    robot_id = "6158903873202297860"     # 🤖
    check_id = "6071022434234930063"     # ✅
    owner_id = "4958900559139570572"     # 👨‍💻
    divider = te(divider_id, "➿") * 10
    msg = (
        "<blockquote>"
        f"{divider}\n"
        f"{te(clock_id, '🕞')} ᴊᴏɪɴ ʀᴇǫᴜɪʀᴇᴅ! {te(user_id_emoji, '👤')}\n"
        f"{divider}\n\n"
        f"{te(arrow_id, '👉')} ʙᴏᴛ ᴜꜱᴇ ᴋᴀʀɴᴇ ᴋᴇ ʟɪʏᴇ\n\n"
        f"{te(robot_id, '🤖')} ɴᴇᴇᴄʜᴇ ᴅɪʏᴇ ɢᴀʏᴇ ꜱᴀᴀʀᴇ "
        "ᴄʜᴀɴɴᴇʟꜱ ᴊᴏɪɴ ᴋᴀʀɴᴀ ᴢᴀʀᴏᴏʀɪ ʜᴀɪ.\n\n"
        f"{te(check_id, '✅')} ᴊᴏɪɴ ᴋᴀʀɴᴇ ᴋᴇ ʙᴀᴀᴅ ᴠᴇʀɪꜰʏ ᴅᴀʙᴀᴏ.\n\n"
        f"{divider}\n"
        f"{te(owner_id, '👨‍💻')} ᴏᴡɴᴇʀ : "
        f"<a href=\"{OWNER_URL}\">{OWNER_NAME}</a>"
        "</blockquote>"
    )
    markup = InlineKeyboardMarkup(row_width=2)
    join_buttons = []
    for idx, channel in enumerate(missing, 1):
        join_buttons.append(create_primary_button(
            f"{sc('Join Channel')} {idx}",
            url=channel,
            icon_custom_emoji_id=owner_id,
        ))
    for row_start in range(0, len(join_buttons), 2):
        markup.row(*join_buttons[row_start:row_start + 2])
    markup.add(create_success_button(
        sc("I've Joined All"),
        callback_data="check_join",
        icon_custom_emoji_id=check_id,
    ))
    try:
        return send_with_premium(
            chat_id, msg, reply_markup=markup,
            disable_web_page_preview=True,
        )
    except Exception as e:
        print(f"Force join message error: {e}")
        return None

def _enforce_verify_gate(message):
    """
    Central verify gate — called by enforce_force_join before any command runs.
    Returns True  → user is verified (or admin), command may proceed.
    Returns False → gate shown, command must stop.

    GC  : shows inline "Verify in Private" button (60 s auto-delete).
    PVT : shows contact-share button via send_contact_verification_prompt().
    Admin/owner skip always.
    """
    uid     = message.from_user.id
    chat_id = message.chat.id

    # Global kill switch — VERIFY_GATE=0 disables the contact gate for everyone
    if str(os.environ.get("VERIFY_GATE", "1")).lower() in ("0", "false", "no", "off"):
        return True

    # Admin / owner — always pass
    if is_admin(uid):
        return True

    # Already verified — pass
    if _is_contact_verified(uid):
        return True

    # ── GROUP / SUPERGROUP ───────────────────────────────────────────
    if message.chat.type in ("group", "supergroup"):
        try:
            bot_me = bot.get_me()
            bot_uname = bot_me.username
        except Exception:
            bot_uname = None

        if bot_uname:
            deep_link = f"https://t.me/{bot_uname}?start=verify"
            markup = types.InlineKeyboardMarkup()
            btn = types.InlineKeyboardButton(
                text="📱 ᴠᴇʀɪꜰʏ ɪɴ ᴘʀɪᴠᴀᴛᴇ",
                url=deep_link,
            )
            try:
                btn.style = "success"
            except Exception:
                pass
            markup.add(btn)

            grp_text = (
                "<blockquote>"
                f"{_cv_pe('robot', '🤖')} <b>ᴠᴇʀɪꜰɪᴄᴀᴛɪᴏɴ ʀᴇQᴜɪʀᴇᴅ</b>\n\n"
                f"{_cv_pe('shield', '🛡️')} Bot use karne ke liye pehle "
                "<b>private chat mein verify</b> karo.\n\n"
                f"{_cv_pe('phone', '📱')} Neeche button dabao aur apna contact share karo."
                "</blockquote>"
            )
            try:
                sent = send_with_premium(chat_id, grp_text, reply_markup=markup)
                if sent:
                    _DELAYED.schedule(60, bot.delete_message, chat_id, sent.message_id)
            except Exception as exc:
                print(f"[VERIFY_GATE_GC] {exc}")
        return False   # block command

    # ── PRIVATE CHAT ─────────────────────────────────────────────────
    # Save what command they tried so we can resume after verify
    try:
        _txt = getattr(message, "text", None) or "/start"
        if _txt.startswith("/start"):
            # keep the referral id (int) so it survives verification
            _r = extract_referral(_txt)
            if _r:
                _PENDING_REF[uid] = _r
            elif not isinstance(_PENDING_REF.get(uid), int):
                _PENDING_REF[uid] = _txt
        else:
            _PENDING_REF[uid] = _txt
    except Exception:
        pass
    send_contact_verification_prompt(uid)
    return False   # block command


def enforce_force_join(message):
    user_id = message.from_user.id
    chat_id = message.chat.id
    if user_id in ADMIN_IDS:
        return True

    # ── Verify gate: must verify before any command ──────────────────
    if not _enforce_verify_gate(message):
        return False

    # Record an interaction for calendar-day DAU reporting.
    try:
        _col_users.update_one(
            {"user_id": user_id},
            {"$set": {"last_active": datetime.now().strftime("%Y-%m-%d %H:%M:%S")}},
        )
    except Exception as activity_exc:
        logger.debug("activity timestamp update failed: %s", activity_exc)

    if not check_subscription(user_id):
        force_join_message(chat_id, user_id)
        return False
    return True

def schedule_deletion(message_id, chat_id):
    _DELAYED.schedule(AUTO_DELETE_TIME, bot.delete_message, chat_id, message_id)

def extract_referral(text):
    if text and 'ref_' in text:
        try:
            return int(text.split('ref_')[1])
        except:
            return None
    return None


def modernize_lookup_result_text(value):
    """Normalize every lookup result to a compact, consistent Telegram HTML style.

    Telegram Bot API does not expose arbitrary font-family or font-size controls.
    This helper standardizes spacing and removes oversized decorative divider
    runs while preserving existing HTML formatting, labels, data and emojis.
    """
    import re as _re
    text = str(value or "")
    # Replace very long decorative divider-only lines with a subtle short rule.
    text = _re.sub(
        r"(?m)^[ \t]*(?:[━─—═╌·•➖➿⭐✨🔸🔹]\s*){5,}$",
        "━━━━━━━━",
        text
    )
    # Trim divider lines that are excessively long without touching content.
    text = _re.sub(r"(?m)^(?:━|─|—|═){9,}$", "━━━━━━━━", text)
    # Keep at most one blank line between content blocks.
    text = _re.sub(r"\n[ \t]*\n(?:[ \t]*\n)+", "\n\n", text)
    # Remove leading/trailing whitespace from each line.
    text = "\n".join(line.rstrip() for line in text.splitlines()).strip()
    return text


def send_result_with_json(chat_id, result_text, json_file, message_id=None, edit=True):
    final_text = modernize_lookup_result_text(result_text)
    file_id = hashlib.md5(json_file.encode()).hexdigest()[:16]
    JSON_FILES[file_id] = json_file

    markup = InlineKeyboardMarkup(row_width=2)
    markup.add(create_primary_button("Download JSON", callback_data=f"dljson_{file_id}"))
    markup.add(create_default_button("Back", callback_data="back_to_result"))

    try:
        sent = None
        if message_id and edit:
            try:
                sent = edit_with_premium(chat_id, message_id, final_text, reply_markup=markup)
            except Exception as e_ed:
                print(f"[SEND_RESULT] edit failed chat={chat_id}: {e_ed}")
                sent = None
        if sent is None:
            sent = send_with_premium(chat_id, final_text, reply_markup=markup)
        if sent is None:
            # last resort: without the JSON keyboard (a bad markup must never
            # swallow the paid result)
            print(f"[SEND_RESULT] send with markup failed chat={chat_id}; retrying without markup (see bot.log 'send failed')")
            sent = send_with_premium(chat_id, final_text)
        if sent is None:
            print(f"[SEND_RESULT] all delivery attempts failed chat={chat_id}")
            return None
        if message_id and getattr(sent, "message_id", None) != message_id:
            try:
                bot.delete_message(chat_id, message_id)   # drop stale loader
            except Exception:
                pass
        schedule_deletion(sent.message_id, chat_id)
        return sent
    except Exception as e:
        print(f"Error sending result: {e}")
        return None

def send_result(chat_id, result_text, wait_message=None, edit=True):
    final_text = modernize_lookup_result_text(result_text)
    final_text = replace_with_premium_emojis(final_text)
    if "<tg-emoji" not in final_text:
        premium_emoji_id = get_random_premium_emoji_id()
        final_text = final_text + '<tg-emoji emoji-id="' + premium_emoji_id + '">⭐</tg-emoji>'
    if wait_message is not None:
        _ev = getattr(wait_message, "_stop_event", None)
        if _ev is not None:
            _ev.set()
    try:
        if wait_message and edit:
            try:
                sent = edit_with_premium(chat_id, wait_message.message_id, final_text)
                if sent:
                    schedule_deletion(sent.message_id, chat_id)
                    return sent
            except Exception as e:
                print(f"Edit failed, sending new message: {e}")
                try:
                    bot.delete_message(chat_id, wait_message.message_id)
                except:
                    pass
        sent = send_with_premium(chat_id, final_text)
        schedule_deletion(sent.message_id, chat_id)
        return sent
    except Exception as e:
        print(f"Error sending result: {e}")
        return None

load_channels_from_db()

def validate_username(u):
    if not u: return False
    u = u.strip().replace('@', '')
    return bool(re.match(r'^[a-zA-Z0-9_]{5,32}$', u))

def validate_phone(p):
    if not p: return False
    p = re.sub(r'[^\d+]', '', p)
    return bool(re.match(r'^\+?[0-9]{10,15}$', p))

def validate_vehicle(v):
    if not v: return False
    v = v.strip().upper().replace(' ', '')
    return bool(re.match(r'^[A-Z]{2}[0-9]{1,2}[A-Z]{1,2}[0-9]{1,4}$', v))

def validate_upi(upi):
    if not upi: return False
    upi = upi.strip().lower()
    return bool(re.match(r'^[a-zA-Z0-9._-]+@[a-zA-Z0-9]+$', upi))

def validate_ifsc(ifsc):
    if not ifsc: return False
    ifsc = ifsc.strip().upper()
    return bool(re.match(r'^[A-Z]{4}0[A-Z0-9]{6}$', ifsc))

def validate_aadhar(a):
    if not a: return False
    a = re.sub(r'[^\d]', '', a)
    return bool(re.match(r'^\d{12}$', a))

def validate_pan(pan):
    if not pan: return False
    pan = pan.strip().upper()
    return bool(re.match(r'^[A-Z]{5}[0-9]{4}[A-Z]{1}$', pan))

def validate_ip(ip):
    if not ip: return False
    return bool(re.match(r'^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$', ip))

def validate_pincode(pin):
    if not pin: return False
    pin = re.sub(r'[^\d]', '', pin)
    return bool(re.match(r'^\d{6}$', pin))

def validate_channel_url(url):
    if not url: return False
    patterns = [r'^https?://t\.me/[a-zA-Z0-9_]+$', r'^https?://telegram\.me/[a-zA-Z0-9_]+$', r'^@[a-zA-Z0-9_]+$']
    for pattern in patterns:
        if re.match(pattern, url):
            return True
    return False


def is_group_chat(message):
    return message.chat.type in ['group', 'supergroup', 'channel']

def extract_username_from_url(url):
    url = url.strip()
    if url.startswith('@'):
        return url[1:]
    elif 't.me/' in url:
        return url.split('t.me/')[-1]
    elif 'telegram.me/' in url:
        return url.split('telegram.me/')[-1]
    return url

def get_emoji_for_key(key):
    key_lower = key.lower()
    if 'name' in key_lower: return '👤'
    elif 'phone' in key_lower or 'number' in key_lower or 'mobile' in key_lower: return '📞'
    elif 'email' in key_lower: return '📧'
    elif 'address' in key_lower: return '🏠'
    elif 'city' in key_lower or 'state' in key_lower: return '📍'
    elif 'bank' in key_lower: return '🏦'
    elif 'ifsc' in key_lower: return '🔢'
    elif 'vehicle' in key_lower or 'car' in key_lower: return '🚗'
    elif 'owner' in key_lower: return '👨'
    elif 'aadhar' in key_lower: return '🆔'
    elif 'pan' in key_lower: return '📄'
    elif 'upi' in key_lower: return '💳'
    elif 'instagram' in key_lower or 'insta' in key_lower: return '📸'
    elif 'followers' in key_lower: return '👑'
    elif 'ip' in key_lower: return '🌐'
    elif 'pincode' in key_lower: return '📮'
    elif 'git' in key_lower: return '🐙'
    elif 'bgmi' in key_lower: return '🎮'
    elif 'ff' in key_lower: return '🔥'
    elif 'prompt' in key_lower or 'image' in key_lower: return '🎨'
    elif 'generated' in key_lower: return '🖼️'
    elif 'father' in key_lower: return '👨'
    elif 'circle' in key_lower: return '🌍'
    elif 'alt' in key_lower or 'alternate' in key_lower: return '📱'
    elif 'id' in key_lower: return '🆔'
    elif 'truecaller' in key_lower: return '👤'
    elif 'country' in key_lower: return '🌍'
    elif 'code' in key_lower: return '🔢'
    elif 'total' in key_lower: return '📊'
    elif 'result' in key_lower: return '📋'
    else: return '•'

print("Validation functions loaded")

# Persistent-disk secret store for environments where Render API integration is not used.
_SECURITY_KEY_FILE = os.environ.get("SHOWN_SECURITY_KEY_FILE") or (
    "/var/data/shown_security_keys.json" if os.path.isdir("/var/data")
    else os.path.join(os.path.dirname(os.path.abspath(__file__)), "shown_security_keys.json")
)
_SECURITY_KEY_LOCK = threading.RLock()

def _security_key_store_read():
    try:
        with open(_SECURITY_KEY_FILE, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        return data if isinstance(data, dict) else {}
    except FileNotFoundError:
        return {}
    except Exception as exc:
        logging.error("[SECURITY_KEYS] Could not read persistent key store: %s", exc)
        return {}

def _security_key_get(kind):
    env_name = "API_CONFIG_ENCRYPTION_KEY" if kind == "api" else "CLONE_TOKEN_ENCRYPTION_KEY"
    env_value = (os.environ.get(env_name) or "").strip()
    if env_value:
        return env_value, "environment"
    # A disk-managed dedicated clone key takes precedence over the legacy API-key fallback.
    value = str(_security_key_store_read().get(kind) or "").strip()
    if value:
        return value, "persistent disk"
    if kind == "clone":
        api_env = (os.environ.get("API_CONFIG_ENCRYPTION_KEY") or "").strip()
        if api_env:
            return api_env, "environment fallback"
    return "", "missing"

def _security_key_store_write(data):
    directory = os.path.dirname(_SECURITY_KEY_FILE) or "."
    os.makedirs(directory, mode=0o700, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix=".shown_keys_", dir=directory)
    try:
        os.fchmod(fd, 0o600)
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            json.dump(data, fh, ensure_ascii=False)
            fh.flush()
            os.fsync(fh.fileno())
        os.replace(tmp, _SECURITY_KEY_FILE)
        try: os.chmod(_SECURITY_KEY_FILE, 0o600)
        except Exception: pass
    finally:
        try:
            if os.path.exists(tmp): os.remove(tmp)
        except Exception: pass

def _security_key_set(kind, value):
    value = str(value).strip()
    if kind not in ("api", "clone"):
        raise ValueError("Unknown key type.")
    if not value or len(value) > 4096 or any(ord(c) < 32 for c in value):
        raise ValueError("Key is empty, too long, or contains control characters.")
    if kind == "clone":
        from cryptography.fernet import Fernet
        try: Fernet(value.encode("ascii"))
        except Exception as exc: raise ValueError("Clone key must be a valid Fernet key. Generate one with Fernet.generate_key().") from exc
    with _SECURITY_KEY_LOCK:
        data = _security_key_store_read()
        # Host environment variables take precedence and cannot be silently shadowed.
        env_name = "API_CONFIG_ENCRYPTION_KEY" if kind == "api" else "CLONE_TOKEN_ENCRYPTION_KEY"
        if (os.environ.get(env_name) or "").strip():
            raise RuntimeError(f"{env_name} is already set in the host environment. Remove it there before managing the disk copy.")
        old, old_source = _security_key_get(kind)
        old = str(old or "").strip()
        if old and old != value:
            if kind == "clone":
                # Re-encrypt every saved clone token before replacing the key.
                from cryptography.fernet import Fernet
                with _clone_db() as conn:
                    rows = conn.execute("SELECT clone_id,token_cipher FROM clones").fetchall()
                    converted = []
                    old_cipher = Fernet(old.encode("ascii"))
                    new_cipher = Fernet(value.encode("ascii"))
                    for row in rows:
                        token = old_cipher.decrypt(row["token_cipher"].encode("ascii"))
                        converted.append((new_cipher.encrypt(token).decode("ascii"), int(row["clone_id"])))
                    conn.executemany("UPDATE clones SET token_cipher=? WHERE clone_id=?", converted)
            else:
                # Re-encrypt existing API credentials with the replacement API secret.
                import base64, hashlib
                from cryptography.fernet import Fernet
                old_cipher = Fernet(base64.urlsafe_b64encode(hashlib.sha256(old.encode()).digest()))
                new_cipher = Fernet(base64.urlsafe_b64encode(hashlib.sha256(value.encode()).digest()))
                docs = list(_col_api_config.find({}))
                converted = []
                for doc in docs:
                    stored = doc.get("api_key")
                    if stored and str(stored).startswith("enc:"):
                        plain = old_cipher.decrypt(str(stored)[4:].encode("ascii"))
                        converted.append(("enc:" + new_cipher.encrypt(plain).decode("ascii"), doc.get("command_name")))
                for cipher_text, command_name in converted:
                    _col_api_config.update_one({"command_name": command_name}, {"$set": {"api_key": cipher_text}})
        data[kind] = value
        _security_key_store_write(data)

def _security_key_remove(kind):
    if kind not in ("api", "clone"):
        raise ValueError("Unknown key type.")
    env_name = "API_CONFIG_ENCRYPTION_KEY" if kind == "api" else "CLONE_TOKEN_ENCRYPTION_KEY"
    if (os.environ.get(env_name) or "").strip():
        raise RuntimeError(f"{env_name} is set by the host environment; remove it in Render/VPS settings instead.")
    if kind == "clone":
        with _clone_db() as conn:
            count = int(conn.execute("SELECT COUNT(*) FROM clones").fetchone()[0])
        if count:
            raise RuntimeError("Cannot remove the clone key while registered clones exist. Remove the clones first or rotate the key instead.")
    else:
        encrypted = _col_api_config.count_documents({"api_key": {"$regex": "^enc:"}})
        if encrypted:
            raise RuntimeError("Cannot remove the API key while encrypted API credentials exist. Remove those credentials first or rotate the key.")
    with _SECURITY_KEY_LOCK:
        data = _security_key_store_read()
        data.pop(kind, None)
        _security_key_store_write(data)

def _api_key_cipher():
    """Fernet key derived from a dedicated Render secret (recommended)."""
    from cryptography.fernet import Fernet
    import base64, hashlib
    secret, _source = _security_key_get("api")
    if not secret:
        raise RuntimeError("API_CONFIG_ENCRYPTION_KEY is missing. Add it in Admin → Security & Keys.")
    key = base64.urlsafe_b64encode(hashlib.sha256(str(secret).encode("utf-8")).digest())
    return Fernet(key)

def _encrypt_api_key(value):
    return "enc:" + _api_key_cipher().encrypt(str(value).encode("utf-8")).decode("ascii")

def _decrypt_api_key(value):
    if not value:
        return ""
    if not str(value).startswith("enc:"):
        return str(value)  # legacy record compatibility
    try:
        return _api_key_cipher().decrypt(str(value)[4:].encode("ascii")).decode("utf-8")
    except Exception:
        return ""

def get_api_config(command_name):
    """Read the persisted override; decrypt its key only in memory."""
    try:
        doc = _col_api_config.find_one({"command_name": str(command_name).lower()}) or {}
        if doc.get("api_key"):
            doc["api_key"] = _decrypt_api_key(doc["api_key"])
        return doc
    except Exception:
        return {}

def get_api_endpoint(command_name):
    cached = _API_EP_CACHE.get(command_name)
    if cached is not None:
        return cached or None
    try:
        doc = get_api_config(command_name)
        val = doc.get("api_endpoint") if doc.get("enabled", True) else None
        _API_EP_CACHE.set(command_name, val or "")
        return val
    except Exception:
        return None

def set_api_endpoint(command_name, endpoint, admin_id):
    command_name = str(command_name).lower().strip().lstrip('/')
    if command_name not in API_ENDPOINTS:
        return False, "This command has no existing lookup handler. API Manager can reconfigure existing lookups only."
    if endpoint and (not endpoint.startswith('https://') or '{query}' not in endpoint):
        return False, "Endpoint must start with https:// and contain {query}. Use {key} for the API key."
    try:
        _col_api_config.update_one(
            {"command_name": command_name},
            {"$set": {"api_endpoint": endpoint, "enabled": True, "updated_by": admin_id,
                      "updated_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S")}},
            upsert=True
        )
        _API_EP_CACHE.delete(command_name)
        return True, f"API endpoint updated for /{command_name}"
    except Exception as e:
        return False, f"Error: {str(e)[:180]}"

def list_all_apis():
    apis = []
    for cmd, endpoint in API_ENDPOINTS.items():
        apis.append({"command": cmd, "endpoint": endpoint, "is_custom": False})
    try:
        for doc in _col_api_config.find({}):
            apis.append({"command": doc["command_name"], "endpoint": doc["api_endpoint"], "is_custom": True})
    except:
        pass
    return apis

def clean_text(text):
    if isinstance(text, str):
        text = text.replace("@DEVELOPERSTAKEBOT", "").strip()
        text = text.replace("@ and @TATANIUM_ANSH", "@ftgamer2")
        text = text.replace("@InvalidAyush", "").strip()
        text = text.replace("InvalidAyush", "ㅤ⏤͟͟͞͞𝗙ʟɪʀᴛ𝗫ᴏ").strip()
        text = text.replace("developer", f"⏤͟͟͞͞{OWNER_NAME}").strip()
        text = text.replace("Developer", f"⏤͟͟͞͞{OWNER_NAME}").strip()
        text = text.replace("@InvalidAyush ❤️🔥⚡", f"⏤͟͟͞͞{OWNER_NAME} ❤️🔥⚡").strip()
        text = text.replace("❤️🔥⚡", "").strip()
        words = text.split()
        cleaned_words = []
        for word in words:
            if word.startswith('@') and word not in ['@ftgamer2', '@BMW_AURA0', '@flirts_x']:
                continue
            cleaned_words.append(word)
        return ' '.join(cleaned_words)
    return text

def clean_dict(data):
    if isinstance(data, dict):
        cleaned = {}
        for key, value in data.items():
            if key.lower() in ['channel', 'developer', 'by', 'tag', 'key_expiry', 'response_time_ms', 'cached', 'cached_at', 'owner', 'credit', 'message']:
                continue
            if isinstance(value, str):
                cleaned[key] = clean_text(value)
            elif isinstance(value, dict):
                cleaned[key] = clean_dict(value)
            elif isinstance(value, list):
                cleaned[key] = [clean_dict(item) if isinstance(item, dict) else (clean_text(item) if isinstance(item, str) else item) for item in value]
            else:
                cleaned[key] = value
        cleaned['developer'] = 'ㅤ⏤͟͟͞͞𝗙ʟɪʀᴛ𝗫ᴏ'
        cleaned['contact'] = 'http://t.me/flirts_x'
        return cleaned
    elif isinstance(data, list):
        return [clean_dict(item) if isinstance(item, dict) else (clean_text(item) if isinstance(item, str) else item) for item in data]
    elif isinstance(data, str):
        return clean_text(data)
    return data

def is_empty_response(data):
    if not data:
        return True
    if isinstance(data, dict):
        if data.get('status') == 'error' or data.get('error'):
            return True
        all_empty = True
        for key, value in data.items():
            if key in ['status', 'by', 'channel']:
                continue
            if value and str(value).strip() and str(value).lower() not in ['none', 'null', '']:
                all_empty = False
                break
        return all_empty
    return False

_META_JSON_KEYS = {"key_details", "developer", "status_code", "http_status",
                   "usage_tracked", "response_time_ms"}


def _decode_json_stream(text):
    """Some providers return `{payload},{meta}` — two objects, no array wrapper."""
    dec = json.JSONDecoder()
    objs, idx, n = [], 0, len(text or "")
    while idx < n:
        while idx < n and text[idx] in " \r\n\t,":
            idx += 1
        if idx >= n:
            break
        try:
            obj, idx = dec.raw_decode(text, idx)
        except Exception:
            break
        objs.append(obj)
    if not objs:
        return None
    first = objs[0]
    if not isinstance(first, dict):
        return first
    merged = dict(first)
    for extra in objs[1:]:
        if not isinstance(extra, dict):
            continue
        for k, v in extra.items():
            if k in _META_JSON_KEYS:
                continue
            merged.setdefault(k, v)
    return merged


def make_api_request(url, timeout=10):
    """
    timeout = read timeout in seconds.
    Connect timeout is always 5s — if server is unreachable, fail fast
    rather than blocking the entire thread for 20-60 seconds.
    Adapter retries are disabled; fallbacks are handled per-caller.
    """
    cache_key = hashlib.md5(url.encode()).hexdigest()
    cached = API_CACHE.get(cache_key)
    if cached:
        return cached
    try:
        # (connect_timeout, read_timeout) — short connect, generous read
        response = session.get(url, timeout=(5, timeout), verify=False)
        data = None
        try:
            data = response.json()
        except Exception:
            data = _decode_json_stream(getattr(response, "text", "") or "")
        if data is not None and response.status_code == 200:
            if isinstance(data, dict) and data.get('status') != 'error':
                API_CACHE.set(cache_key, data)
            return data
        if isinstance(data, dict):
            msg = data.get("message") or data.get("error")
            if msg:
                return {"status": "error", "message": str(msg), "code": response.status_code}
        return {"status": "error", "message": f"HTTP {response.status_code}"}
    except Exception as e:
        # requests errors embed the full URL (incl. API key) — never surface it
        return {"status": "error", "message": _redact(e)}

def call_phone_api(phone):
    """
    API: (NUM)number=<phone>
    Response: { "success": true, "number": "...", "total": N,
                "results": [{ "mobile", "name", "address", "circle",
                               "alt", "fname", "id", "email",
                               "truecaller_name" }, ...] }
    """
    phone = re.sub(r'[^\d+]', '', phone).lstrip('+')
    try:
        url = ep("num", phone) or f"(NUM)number={phone}"
        data = _norm_provider("num", make_api_request(url, timeout=25))

        if not isinstance(data, dict):
            return {"status": "error", "message": "NO DATA FOUND"}
        if not data.get("success"):
            return {"status": "error", "message": data.get("message", "NO DATA FOUND")}

        # New API uses "results", old used "records"
        raw = data.get("results", data.get("records", []))
        if not raw:
            return {"status": "error", "message": "NO DATA FOUND"}

        records = []
        for r in raw:
            if not isinstance(r, dict):
                continue
            # field name normalisation: new API uses alt/fname, old used alt_number/father
            alt_val = (r.get("alt") or r.get("alt_number") or
                       r.get("alternate") or r.get("altNumber") or "N/A")
            fname   = (r.get("fname") or r.get("father") or
                       r.get("father_name") or r.get("fatherName") or "N/A")
            tc_name = r.get("truecaller_name", "N/A")
            name    = r.get("name", "N/A")
            # ignore placeholder truecaller labels
            if tc_name and tc_name.lower() in ("test label", "n/a", "none", ""):
                tc_name = "N/A"
            records.append({
                "record_no":       len(records) + 1,
                "mobile":          str(r.get("mobile", "N/A")).strip(),
                "name":            name,
                "truecaller_name": tc_name,
                "father_name":     fname,
                "address":         str(r.get("address", "N/A")).replace("!", ", "),
                "circle":          r.get("circle", "N/A"),
                "alternate":       alt_val,
                "id":              str(r.get("id", "N/A")),
                "email":           (r.get("email") if r.get("email") and
                                    r.get("email") not in ("N/A","default@unspecify.com") else "N/A"),
            })

        return clean_dict({
            "status":  "success",
            "number":  data.get("number", phone),
            "total":   data.get("total", data.get("total_records", len(records))),
            "records": records,
        })

    except Exception as e:
        return {"status": "error", "message": str(e)}

def call_tg_api(query):
    """
    Primary API: (TGID)username=<query>
    Response shape:
      { "success": true,
        "response": { "data": [ { "user_id": "...", "username": "@...",
                                   "name": "...", "number": "...",
                                   "country": "...", "country_code": "..." } ] } }
    Falls back to old APIs on failure.
    """
    query = str(query).strip()
    query = query.replace("@", "").replace("t.me/", "").replace("telegram.me/", "")
    is_user_id = query.isdigit()

    def _parse_new_api(data, original_query):
        """Parse the new 100.31 /api/tg response."""
        if not isinstance(data, dict):
            return None
        if data.get("success"):
            inner = data.get("response", {}) or {}
            records = inner.get("data", []) if isinstance(inner, dict) else []
            if not records:
                return None
            r = records[0]
        elif data.get("number"):
            # flat shape: {country, country_code, number, tg_id, msg, ...}
            r = data
        else:
            return None
        tgid     = str(r.get("user_id") or r.get("tg_id") or "").strip() or "N/A"
        username = str(r.get("username", "")).strip().lstrip("@") or "N/A"
        phone    = str(r.get("number",   "")).strip() or None
        name     = str(r.get("name",     "")).strip() or "N/A"
        country  = str(r.get("country",  "")).strip() or "N/A"
        cc       = str(r.get("country_code", "")).strip() or "N/A"
        if not phone:
            return None
        return {
            "status":       "success",
            "query":        original_query,
            "found":        True,
            "tgid":         tgid,
            "username":     username,
            "name":         name,
            "phone":        phone,
            "country":      country,
            "country_code": cc,
            "msg":          "Details fetched",
            "provided_by":  "ㅤ⏤͟͟͞͞𝗙ʟɪʀᴛ𝗫ᴏ",
            "telegram":     "@flirts_x",
        }

    def _parse_old_api(data, original_query):
        if not isinstance(data, dict) or data.get("success") != True:
            return None
        msg = data.get("msg", "")
        if "not found" in msg.lower() or "no data" in msg.lower():
            return None
        phone = data.get("number") or None
        if not phone:
            return None
        tgid = None
        for field in ["tg_id", "user_id", "id", "userid", "userId", "UID"]:
            if field in data and data[field] is not None:
                tgid = data[field]; break
        username = None
        for field in ["username", "user_name", "uname", "tg_username"]:
            if field in data and data[field] is not None:
                username = data[field]; break
        return {
            "status":       "success",
            "query":        original_query,
            "found":        True,
            "tgid":         str(tgid) if tgid else "N/A",
            "username":     str(username) if username else "N/A",
            "name":         "N/A",
            "phone":        str(phone),
            "country":      str(data.get("country") or "N/A"),
            "country_code": str(data.get("country_code") or "N/A"),
            "msg":          msg or "Details fetched",
            "provided_by":  "ㅤ⏤͟͟͞͞𝗙ʟɪʀᴛ𝗫ᴏ",
            "telegram":     "@flirts_x",
        }

    # ── Attempt 0: configured provider (/api/tg) ─────────────────
    # phone  -> number=9876543210, then number=919876543210, then userid=
    # handle -> username=durov, then userid= if the handle is numeric
    _tg_candidates = []
    if query.isdigit():
        if len(query) >= 10:
            _tg_candidates.append(ep("tgnum", query))
            if len(query) == 10:
                _tg_candidates.append(ep("tgnum", "91" + query))
            _tg_candidates.append(ep("tgphone", query))
        _tg_candidates.append(ep("tgid", query))
    else:
        _tg_candidates.append(ep("tguser", query))
    _tg_candidates = [u for u in _tg_candidates if u]

    for _tg_idx, _tg_url in enumerate(_tg_candidates):
        try:
            _tg_data = _norm_provider("tgid", make_api_request(_tg_url, timeout=25))
            _tg_res = _parse_new_api(_tg_data, query) or _parse_old_api(_tg_data, query)
            if not _tg_res and isinstance(_tg_data, dict):
                _inner = (_tg_data.get("response") or {}).get("data") or []
                _r = _inner[0] if _inner else {}
                _tid = str(_r.get("user_id") or "").strip()
                if _tid:
                    _tg_res = {
                        "status":       "success",
                        "query":        query,
                        "found":        True,
                        "tgid":         _tid,
                        "username":     str(_r.get("username") or "N/A"),
                        "name":         str(_r.get("name") or "N/A"),
                        "phone":        str(_r.get("number") or "N/A"),
                        "country":      str(_r.get("country") or "N/A"),
                        "country_code": str(_r.get("country_code") or "N/A"),
                        "msg":          "Details fetched",
                    }
            if _tg_res:
                return _tg_res
        except Exception as _tg_err:
            print(f"[TGID] provider error ({_tg_idx}): {_tg_err}")
        if _tg_idx < len(_tg_candidates) - 1:
            time.sleep(1.2)          # provider allows 5 req/min

    # ── Attempt 1: felix (tg_id numeric only) ─────────────────────
    if is_user_id:
        try:
            url_felix = f"(TGID)tg={query}"
            data_felix = make_api_request(url_felix, timeout=15)
            if isinstance(data_felix, dict):
                phone_f = str(data_felix.get("number", "")).strip()
                tgid_f  = str(data_felix.get("tg_id", query)).strip()
                msg_f   = str(data_felix.get("msg", "")).strip()
                if phone_f and "not found" not in msg_f.lower() and "no data" not in msg_f.lower():
                    cc_f = str(data_felix.get("country_code", "N/A")).strip()
                    # country_code may be "+43" — strip the + for display
                    phone_full = f"{cc_f}{phone_f}" if not phone_f.startswith("+") else phone_f
                    return {
                        "status":       "success",
                        "query":        query,
                        "found":        True,
                        "tgid":         tgid_f,
                        "username":     "N/A",
                        "name":         "N/A",
                        "phone":        phone_full,
                        "number":       phone_f,
                        "country":      str(data_felix.get("country", "N/A")).strip(),
                        "country_code": cc_f,
                        "msg":          msg_f or "Details fetched",
                        "provided_by":  "ㅤ⏤͟͟͞͞𝗙ʟɪʀᴛ𝗫ᴏ",
                        "telegram":     "@flirts_x",
                    }
        except Exception as e_f:
            print(f"[TGID] felix error: {e_f}")

    # ── Attempt 2: new local API ────────────────────────────────────
    try:
        param = query if is_user_id else query
        url1 = f"(TGID)username={param}"
        data1 = make_api_request(url1, timeout=15)
        result = _parse_new_api(data1, query)
        if result:
            return result
    except Exception as e1:
        print(f"[TGID] 68.211 API error: {e1}")

    # ── Attempt 3: rootx ────────────────────────────────────────────
    try:
        prefix = "" if is_user_id else "@"
        url2 = f"(TGID)query={prefix}{query}"
        data2 = make_api_request(url2, timeout=15)
        result = _parse_old_api(data2, query)
        if result:
            return result
    except Exception as e2:
        print(f"[TGID] Attempt 2 error: {e2}")

    # ── Attempt 5: (TGID) fallback ────────────────────────────────────
    try:
        prefix = "" if is_user_id else "@"
        url3 = f"(TGID)info={prefix}{query}"
        data3 = make_api_request(url3, timeout=15)
        result = _parse_old_api(data3, query)
        if result:
            return result
    except Exception as e3:
        print(f"[TGID] Attempt 3 error: {e3}")

    # ── Attempt 6: (TGID) fallback ────────────────────────────────────
    try:
        prefix = "" if is_user_id else "@"
        url4 = f"(TGID)term={prefix}{query}"
        data4 = make_api_request(url4, timeout=15)
        if isinstance(data4, dict) and data4.get("success") == True:
            msg = data4.get("msg", "")
            if "not found" not in msg.lower() and "no data" not in msg.lower():
                phone = data4.get("number") or data4.get("n") or None
                tgid  = data4.get("tg_id") or data4.get("id") or None
                if phone:
                    return {
                        "status":       "success",
                        "query":        query,
                        "found":        True,
                        "tgid":         str(tgid) if tgid else "N/A",
                        "username":     "N/A",
                        "name":         "N/A",
                        "phone":        str(phone),
                        "country":      str(data4.get("country") or data4.get("c") or "N/A"),
                        "country_code": str(data4.get("country_code") or data4.get("cc") or "N/A"),
                        "msg":          msg or "Details fetched",
                        "provided_by":  "ㅤ⏤͟͟͞͞𝗙ʟɪʀᴛ𝗫ᴏ",
                        "telegram":     "@flirts_x",
                    }
    except Exception as e4:
        print(f"[TGID] Attempt 4 error: {e4}")

    # ── Attempt 7: resolve UID → username → retry new API ──────────
    if is_user_id:
        try:
            chat = bot.get_chat(int(query))
            if chat and chat.username:
                uname = chat.username
                url5 = f"(TGID)username={uname}"
                data5 = make_api_request(url5, timeout=15)
                result = _parse_new_api(data5, query)
                if result:
                    result["note"] = f"Resolved UID → @{uname}"
                    return result
        except Exception as e5:
            print(f"[TGID] Attempt 5 error: {e5}")

    return {"status": "error", "message": "NO DATA FOUND"}
def call_aadhar_api(aadhar_number):
    """
    Primary:  {BASE_URL}/api/adhar?adhar=<12-digit>
    Response: { "success": true, "aadhar": "...", "total": N,
                "results": [{mobile, name, address, circle, aadhar}, ...] }
    Fallback: old 100.31 and felix endpoints.
    """
    aadhar = re.sub(r'[^\d]', '', aadhar_number)
    new_ip = BASE_URL

    def _normalise(raw, aadhar_val):
        # new API uses "results", old APIs used "records"
        raw_list = raw.get("results", raw.get("records", []))
        if not isinstance(raw_list, list) or not raw_list:
            return None
        records = []
        for r in raw_list:
            fname = (r.get("father") or r.get("father_name") or
                     r.get("fname") or r.get("fatherName") or "N/A")
            records.append({
                "record_no":   len(records) + 1,
                "mobile":      str(r.get("mobile", "N/A")).strip(),
                "name":        r.get("name", "N/A"),
                "father_name": fname,
                "address":     str(r.get("address", "N/A")).replace("!", ", "),
                "circle":      r.get("circle", "N/A"),
                "aadhar":      r.get("aadhar", aadhar_val),
                "email":       r.get("email", "N/A") if r.get("email") else "N/A",
            })
        return clean_dict({
            "status":  "success",
            "aadhar":  aadhar_val,
            "total":   raw.get("total", raw.get("total_records", len(records))),
            "records": records,
        })

    # ── Attempt 1: new 68.211 API ───────────────────────────────
    try:
        url1 = ep("adhr", aadhar) or f"(ADHR)adhar={aadhar}"
        data1 = _norm_provider("adhr", make_api_request(url1, timeout=25))
        if isinstance(data1, dict) and data1.get("success"):
            result = _normalise(data1, aadhar)
            if result:
                return result
    except Exception as e1:
        print(f"[ADHR] new API error: {e1}")

    # ── Attempt 2: old 100.31 dead — removed ───────────────────

    # ── Attempt 3: felix fallback ───────────────────────────────
    try:
        url3 = ep("adhr", aadhar) or f"(ADHR)adhar={aadhar}"
        data3 = make_api_request(url3, timeout=15)
        if isinstance(data3, dict) and (data3.get("status") is True or data3.get("success") is True):
            inner3 = data3.get("data", data3)
            if isinstance(inner3, dict):
                result = _normalise(inner3, aadhar)
                if result:
                    return result
    except Exception as e3:
        print(f"[ADHR] felix error: {e3}")

    return {"status": "error", "message": "NO DATA FOUND"}
def build_api_url(endpoint_template, query, command=None):
    """Replace placeholders; command-specific keys override the environment key."""
    import re as _re
    url = endpoint_template
    api_key = API_KEY
    if command:
        cfg = get_api_config(command)
        api_key = cfg.get("api_key") or API_KEY
    else:
        # Legacy handlers that call get_api_endpoint()+build_api_url() still
        # receive the per-command key when their template matches a DB override.
        try:
            for _doc in _col_api_config.find({}):
                if _doc.get("api_endpoint") == endpoint_template and _doc.get("api_key"):
                    api_key = _decrypt_api_key(_doc.get("api_key")) or API_KEY
                    break
        except Exception:
            pass
    url = url.replace("{key}", str(api_key))
    # URL-encode user input so it cannot inject extra query params (&, =, #, /)
    q = _urlquote(str(query), safe="@.+-_~")
    url = url.replace("{query}", q)
    # replace any remaining {word} placeholder with the query value
    url = _re.sub(r'\{[^}]+\}', lambda _m: q, url)
    return url

def ep(command, query):
    """Resolve an admin override first, then the built-in provider template."""
    cfg = get_api_config(command)
    if cfg and not cfg.get("enabled", True):
        return None
    tpl = (cfg.get("api_endpoint") if cfg else None) or (API_ENDPOINTS or {}).get(command)
    if not tpl:
        return None
    return build_api_url(tpl, query, command=command)


def _provider_records(payload):
    """{"0": {...}, "1": {...}} -> [ {...}, {...} ] with lowercase keys."""
    if not isinstance(payload, dict):
        return []
    keys = [k for k in payload if str(k).isdigit()]
    if not keys:
        return []
    out = []
    for k in sorted(keys, key=lambda x: int(x)):
        v = payload.get(k)
        if isinstance(v, dict):
            out.append({str(kk).lower(): vv for kk, vv in v.items()})
    return out


def _fix_email(value):
    e = str(value or "").strip()
    if "@" in e and " " in e:
        head, _, tail = e.partition("@")
        if "." not in tail and tail:
            e = head.replace(" ", "") + "@" + tail.replace(" ", ".")
        else:
            e = e.replace(" ", "")
    return e or "N/A"


def _clean_identity_record(r):
    r = dict(r)
    mobile = r.get("mobile") or r.get("num") or r.get("number") or r.get("phone")
    if mobile:
        r["mobile"] = str(mobile).strip()
    if r.get("address"):
        r["address"] = str(r["address"]).replace("!", ", ").strip(" ,")
    if not r.get("fname"):
        r["fname"] = r.get("father") or r.get("father_name")
    if not r.get("id"):
        r["id"] = r.get("aadhar") or r.get("aadhaar") or r.get("document_number")
    if r.get("email"):
        r["email"] = _fix_email(r["email"])
    return r


def _norm_provider(cmd, data):
    """Map provider payloads onto the shapes the parsers expect."""
    if not isinstance(data, dict):
        return data
    d = dict(data)
    d.pop("key_details", None)

    # ── phone / aadhaar: records keyed "0","1",... with UPPERCASE fields ──
    recs = _provider_records(d)
    if recs and cmd in ("num", "num2", "adhr"):
        recs = [_clean_identity_record(r) for r in recs]
        out = {"success": True, "total": len(recs), "records": recs, "results": recs}
        if cmd in ("num", "num2"):
            out["number"] = str(recs[0].get("mobile") or d.get("query") or "")
        else:
            out["aadhar"] = str(d.get("query") or d.get("aadhar") or "")
        return out

    # ── leak / osint: blocks of {title, description, records[]} ──
    if cmd in ("leak", "osint"):
        blocks = d.get("data") if isinstance(d.get("data"), dict) else {}
        if not blocks:
            blocks = {k: v for k, v in d.items()
                      if str(k).lower().startswith("source") and isinstance(v, dict)}
        if blocks:
            records = []
            for key, blk in blocks.items():
                if not isinstance(blk, dict):
                    continue
                title = blk.get("title") or key
                for r in (blk.get("records") or []):
                    if not isinstance(r, dict):
                        continue
                    rec = {"source": str(title)}
                    for src_key, dst in (("Phone", "phones"), ("FullName", "name"),
                                         ("FatherName", "father_name"),
                                         ("TheNameOfTheFather", "father_name"),
                                         ("Adres", "address"),
                                         ("DocumentNumber", "document_number"),
                                         ("Region", "region"), ("Email", "email")):
                        if r.get(src_key):
                            rec[dst] = str(r[src_key]).replace("!", ", ")
                    for extra in ("Password", "Nick", "Link", "Name"):
                        if r.get(extra):
                            rec[extra.lower()] = r[extra]
                    if not rec.get("name"):
                        rec["name"] = r.get("name") or r.get("Nick") or "N/A"
                    if not rec.get("phones"):
                        rec["phones"] = str(r.get("number") or r.get("phone") or "N/A")
                    records.append(rec)
            if records:
                return {"status": "success", "number": str(d.get("query") or ""),
                        "total": len(records), "records": records}

    # ── telegram: flat {tg_id, username, phone[]} ──────────────
    if cmd == "tgid":
        tgid = d.get("tg_id") or d.get("tgid") or d.get("user_id")
        if tgid:
            phone = d.get("phone")
            if isinstance(phone, list):
                phone = phone[0] if phone else None
            payload = {
                "user_id":      str(tgid),
                "username":     str(d.get("username") or "").lstrip("@"),
                "name":         d.get("name") or d.get("first_name") or "",
                "number":       str(phone or ""),
                "country":      d.get("country") or "",
                "country_code": d.get("country_code") or d.get("countryCode") or "",
            }
            return {"success": True, "response": {"data": [payload]}}

    # ── snapchat: flat profile ─────────────────────────────────
    if cmd == "snap" and ("exists" in d or "username" in d):
        return {"success": True, "data": d}

    # ── upi: {vpa, valid, psp, handle} ─────────────────────────
    if cmd == "upi" and d.get("vpa"):
        d.setdefault("upi_id", d.get("vpa"))
        d["success"] = True
        return d

    # ── pincode: {records:[{office_name,...}]} -> readable summary ──
    if cmd == "pin":
        recs2 = d.get("records")
        if isinstance(recs2, list) and recs2:
            offices = []
            for r in recs2:
                if isinstance(r, dict):
                    name = str(r.get("office_name") or r.get("name") or "").strip()
                    if name:
                        offices.append(name)
            first = recs2[0] if isinstance(recs2[0], dict) else {}
            return {
                "status": "success",
                "pincode": d.get("pincode"),
                "total_offices": d.get("total", len(offices)),
                "state": first.get("state_name"),
                "division": first.get("division_name"),
                "offices": ", ".join(offices[:40]) + (" ..." if len(offices) > 40 else ""),
            }

    return d

def call_name_api(name):
    try:
        custom_endpoint = get_api_endpoint('name')
        if custom_endpoint:
            url = build_api_url(custom_endpoint, name)
        else:
            url = ep("name", name) or f"(NAME)name={_urlquote(str(name), safe='@.+-_~')}"
        data = make_api_request(url, timeout=15)
        if isinstance(data, dict):
            if 'channel' in data: del data['channel']
            if is_empty_response(data):
                return {"status": "error", "message": "NO DATA FOUND"}
            return clean_dict(data)
        return {"status": "error", "message": "NO DATA FOUND"}
    except:
        return {"status": "error", "message": "NO DATA FOUND"}

def call_pan_api(pan):
    pan = pan.strip().upper()
    try:
        custom_endpoint = get_api_endpoint('pan')
        if custom_endpoint:
            url = build_api_url(custom_endpoint, pan)
        else:
            url = ep("pan", pan) or f"(PAN)pan={pan}"
        data = make_api_request(url, timeout=15)
        if isinstance(data, dict):
            if 'channel' in data: del data['channel']
            if is_empty_response(data):
                return {"status": "error", "message": "NO DATA FOUND"}
            return clean_dict(data)
        return {"status": "error", "message": "NO DATA FOUND"}
    except:
        return {"status": "error", "message": "NO DATA FOUND"}

def call_vehicle_api(vehicle):
    """
    Primary: {BASE_URL}/api/veh?vehicle=<RC>
    Response (flat): { success, vehicle, chassis_number, engine_number,
                       mobile_number, owner_name, response_time_ms }
    Fallback: old 100.31 endpoint, then custom/base endpoint.
    """
    vehicle = vehicle.strip().upper().replace(' ', '')
    new_ip = BASE_URL

    def _normalise_veh(raw):
        """Normalise flat new-API response to a consistent dict."""
        if not isinstance(raw, dict) or not raw.get("success"):
            return None
        d = {
            "status":         "success",
            "vehicle":        str(raw.get("vehicle", "N/A")),
            "owner_name":     str(raw.get("owner_name", raw.get("owner", "N/A"))),
            "mobile_number":  str(raw.get("mobile_number", raw.get("mobile", "N/A"))),
            "chassis_number": str(raw.get("chassis_number", "N/A")),
            "engine_number":  str(raw.get("engine_number", "N/A")),
        }
        return d

    # ── Attempt 1: new 68.211 API ───────────────────────────────
    try:
        url1 = ep("vech", vehicle) or f"(VECH)vehicle={vehicle}"
        data1 = make_api_request(url1, timeout=20)
        r = _normalise_veh(data1)
        if r:
            return clean_dict(r)
    except Exception as e1:
        print(f"[VECH] new API error: {e1}")

    # ── Attempt 2: old 100.31 dead — removed ───────────────────

    # ── Attempt 3: custom / base endpoint ───────────────────────
    try:
        custom_endpoint = get_api_endpoint('vech')
        url3 = build_api_url(custom_endpoint, vehicle) if custom_endpoint else f"(VECH)vehicle={vehicle}"
        data3 = make_api_request(url3, timeout=15)
        if isinstance(data3, dict):
            data3.pop('channel', None)
            if not is_empty_response(data3):
                return clean_dict(data3)
    except Exception as e3:
        print(f"[VECH] base API error: {e3}")

    return {"status": "error", "message": "NO DATA FOUND"}

def call_rc_api(vehicle):
    vehicle = vehicle.strip().upper().replace(' ', '')
    try:
        # NEW API: (VECHRC)
        url = ep("vechrc", vehicle) or f"(VECHRC)vehicle={vehicle}"
        data = make_api_request(url, timeout=20)
        if isinstance(data, dict) and data.get('status') != 'error' and not is_empty_response(data):
            return clean_dict(data)
    except Exception as e:
        print(f"New RC API failed: {e}")

    try:
        new_url = f"(VECHRC)number={vehicle}"
        data = make_api_request(new_url, timeout=20)
        if isinstance(data, dict) and data.get('status') != 'error' and not is_empty_response(data):
            return clean_dict(data)
    except Exception as e:
        print(f"Fallback RC API failed: {e}")

    try:
        custom_endpoint = get_api_endpoint('vechrc')
        if custom_endpoint:
            url = build_api_url(custom_endpoint, vehicle)
        else:
            url = f"(VECHRC)owner={vehicle}"
        data = make_api_request(url, timeout=15)
        if isinstance(data, dict):
            if 'channel' in data: del data['channel']
            if is_empty_response(data):
                return {"status": "error", "message": "NO DATA FOUND"}
            return clean_dict(data)
        return {"status": "error", "message": "NO DATA FOUND"}
    except:
        return {"status": "error", "message": "NO DATA FOUND"}

def save_result_to_json(command, query, result):
    try:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        safe_q = re.sub(r'[^\w.-]', '_', str(query))[:60].strip('.') or "q"
        filename = f"result_{command}_{safe_q}_{timestamp}_{random.randint(1000, 9999)}.json"
        filepath = os.path.join("/tmp", filename)
        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(result, f, indent=2, ensure_ascii=False, default=str)
        _DELAYED.schedule(6 * 3600, _safe_remove, filepath)   # stop /tmp filling up
        return filepath
    except Exception as e:
        print(f"Error saving JSON: {e}")
        return None

def send_multi_result(chat_id, message_parts, wait_message=None, json_file=None):
    if not message_parts:
        return None
    if wait_message:
        try:
            bot.delete_message(chat_id, wait_message.message_id)
        except:
            pass
    sent_messages = []
    for idx, part in enumerate(message_parts):
        markup = None
        if idx == len(message_parts) - 1 and json_file:
            file_id = hashlib.md5(json_file.encode()).hexdigest()[:16]
            JSON_FILES[file_id] = json_file
            markup = InlineKeyboardMarkup(row_width=2)
            markup.add(create_primary_button("📥 Download JSON", callback_data=f"dljson_{file_id}"))
            markup.add(create_default_button("Back", callback_data="back_to_result"))
        try:
            msg = send_with_premium(chat_id, part, reply_markup=markup)
            if msg:
                sent_messages.append(msg)
                schedule_deletion(msg.message_id, chat_id)
        except Exception as e:
            print(f"Error sending part {idx+1}: {e}")
    return sent_messages[-1] if sent_messages else None

def call_num2_api(phone):
    phone = re.sub(r'[^\d+]', '', phone).lstrip('+')
    try:
        url = ep("num2", phone) or f"(NUM2)number={phone}"
        data = _norm_provider("num2", make_api_request(url, timeout=25))
        if isinstance(data, dict):
            if isinstance(data, dict) and data.get('results'):
                cleaned_data = {
                    "status": "success",
                    "number": data.get('number', phone),
                    "total": data.get('total', 0),
                    "records": []
                }
                for idx, result in enumerate(data.get('results', []), 1):
                    alt_val = (result.get('alt')
                               or result.get('alternate')
                               or result.get('alt_number')
                               or result.get('altNumber')
                               or result.get('alt_num')
                               or 'N/A')
                    fname_val = (result.get('fname')
                                 or result.get('father_name')
                                 or result.get('father')
                                 or result.get('fatherName')
                                 or result.get('Father Name')
                                 or 'N/A')
                    # aadhar — try multiple possible field names from API
                    aadhar_val = (result.get('aadhar')
                                  or result.get('adhar')
                                  or result.get('aadhaar')
                                  or result.get('aadhar_number')
                                  or result.get('adharCard')
                                  or 'N/A')
                    record = {
                        "record_no": idx,
                        "mobile": result.get('mobile', 'N/A'),
                        "name": result.get('name', 'N/A'),
                        "address": str(result.get('address', 'N/A')).replace('!', ', '),
                        "circle": result.get('circle', 'N/A'),
                        "alternate": alt_val,
                        "father_name": fname_val,
                        "id": result.get('id', 'N/A'),
                        "email": result.get('email', 'Not Available'),
                        "truecaller_name": result.get('truecaller_name', 'N/A'),
                        "aadhar": str(aadhar_val) if aadhar_val and aadhar_val != 'N/A' else 'N/A',
                    }
                    cleaned_data['records'].append(record)
                return clean_dict(cleaned_data)
            elif data.get('success') == True and data.get('total', 0) == 0:
                return {"status": "error", "message": "NO DATA FOUND"}
            return {"status": "error", "message": "NO DATA FOUND"}
        return {"status": "error", "message": "NO DATA FOUND"}
    except Exception as e:
        return {"status": "error", "message": str(e)}

def call_family_api(aadhar):
    """
    Primary: (FAMILY)id=<aadhar>
    Response: { success, aadhaar, aadhaar_masked, ration_card, scheme,
                state, district, address, rc, fps_id, total_members,
                members: [{name, relation, member_id, uid}, ...] }
    Falls back to old IP on failure.
    """
    aadhar = re.sub(r'[^\d]', '', str(aadhar))

    # ── Attempt 1: (FAMILY) API ──────────────────────────────────
    try:
        url1 = ep("family", aadhar) or f"(FAMILY)id={aadhar}"
        data1 = make_api_request(url1, timeout=15)
        if isinstance(data1, dict) and data1.get("success"):
            data1.pop("by", None); data1.pop("channel", None)
            data1.pop("response_time_ms", None)
            data1["status"] = "success"
            return clean_dict(data1)
    except Exception as e1:
        print(f"[FAMILY] new API error: {e1}")

    # ── Attempt 2: old 54.152 fallback ──────────────────────────
    try:
        url2 = f"(FAMILY)aadhaar={aadhar}"
        data2 = make_api_request(url2, timeout=15)
        if isinstance(data2, dict):
            data2.pop("channel", None)
            if not is_empty_response(data2):
                return clean_dict(data2)
    except Exception as e2:
        print(f"[FAMILY] old API error: {e2}")

    return {"status": "error", "message": "NO DATA FOUND"}

def call_ip_api(ip):
    try:
        custom_endpoint = get_api_endpoint('ip')
        if custom_endpoint:
            url = build_api_url(custom_endpoint, ip)
        else:
            url = ep("ip", ip) or f"(IP)ip={ip}"
        data = make_api_request(url, timeout=15)
        if isinstance(data, dict):
            if 'channel' in data: del data['channel']
            if is_empty_response(data):
                return {"status": "error", "message": "NO DATA FOUND"}
            return clean_dict(data)
        return {"status": "error", "message": "NO DATA FOUND"}
    except:
        return {"status": "error", "message": "NO DATA FOUND"}

def _generic_get(cmd, query, timeout=25):
    """Shared fetch for endpoints rendered by format_api_result."""
    try:
        custom = get_api_endpoint(cmd)
        url = build_api_url(custom, query) if custom else ep(cmd, query)
        if not url:
            return {"status": "error", "message": "NO DATA FOUND"}
        data = _norm_provider(cmd, make_api_request(url, timeout=timeout))
        if isinstance(data, dict):
            if data.get("status") == "error":
                return data
            data.pop("channel", None)
            if is_empty_response(data):
                return {"status": "error", "message": "NO DATA FOUND"}
            return clean_dict(data)
        return {"status": "error", "message": "NO DATA FOUND"}
    except Exception as e:
        return {"status": "error", "message": str(e)}


def call_domain_api(domain):
    return _generic_get("domain", str(domain).strip().lower())


def call_imei_api(imei):
    return _generic_get("imei", re.sub(r"[^\d]", "", str(imei)))


def call_osint_api(term):
    data = _generic_get("osint", str(term).strip())
    if data.get("status") == "error":
        return data
    records = data.get("records") if isinstance(data, dict) else None
    if isinstance(records, list):
        return {"status": "success", "query": str(term), "total": len(records),
                "records": records[:40]}
    return data


def call_pincode_api(pin):
    try:
        custom_endpoint = get_api_endpoint('pin')
        if custom_endpoint:
            url = build_api_url(custom_endpoint, pin)
        else:
            url = ep("pin", pin) or f"(PIN)pin={pin}"
        data = _norm_provider("pin", make_api_request(url, timeout=20))
        if isinstance(data, dict):
            if 'channel' in data: del data['channel']
            if is_empty_response(data):
                return {"status": "error", "message": "NO DATA FOUND"}
            return clean_dict(data)
        return {"status": "error", "message": "NO DATA FOUND"}
    except:
        return {"status": "error", "message": "NO DATA FOUND"}

def call_git_api(username):
    try:
        custom_endpoint = get_api_endpoint('git')
        if custom_endpoint:
            url = build_api_url(custom_endpoint, username)
        else:
            url = ep("git", username) or f"(GIT)username={username}"
        data = make_api_request(url, timeout=15)
        if isinstance(data, dict):
            if 'channel' in data: del data['channel']
            if is_empty_response(data):
                return {"status": "error", "message": "NO DATA FOUND"}
            return clean_dict(data)
        return {"status": "error", "message": "NO DATA FOUND"}
    except:
        return {"status": "error", "message": "NO DATA FOUND"}

def call_bgmi_api(uid):
    try:
        custom_endpoint = get_api_endpoint('bgmi')
        if custom_endpoint:
            url = build_api_url(custom_endpoint, uid)
        else:
            url = ep("bgmi", uid) or f"(BGMI)uid={uid}"
        data = make_api_request(url, timeout=15)
        if isinstance(data, dict):
            if 'channel' in data: del data['channel']
            if is_empty_response(data):
                return {"status": "error", "message": "NO DATA FOUND"}
            return clean_dict(data)
        return {"status": "error", "message": "NO DATA FOUND"}
    except:
        return {"status": "error", "message": "NO DATA FOUND"}

def call_ff_api(uid):
    try:
        custom_endpoint = get_api_endpoint('ff')
        if custom_endpoint:
            url = build_api_url(custom_endpoint, uid)
        else:
            url = ep("ff", uid) or f"(FF)uid={uid}"
        data = make_api_request(url, timeout=15)
        if isinstance(data, dict):
            if 'channel' in data: del data['channel']
            if is_empty_response(data):
                return {"status": "error", "message": "NO DATA FOUND"}
            return clean_dict(data)
        return {"status": "error", "message": "NO DATA FOUND"}
    except:
        return {"status": "error", "message": "NO DATA FOUND"}

def call_upi_api(upi_id):
    """
    Primary: (UPI)upi=<id>
    Response: { "success": true, "upi_id", "name", "username", "handle",
                "valid", "account_type", "bank", "bank_id", "app",
                "handle_bank" }
    """
    upi_id = upi_id.strip()
    # ── Attempt 1: (UPI) API ─────────────────────────────────────
    try:
        url1 = ep("upi", upi_id) or f"(UPI)upi={upi_id}"
        data1 = _norm_provider("upi", make_api_request(url1, timeout=20))
        if isinstance(data1, dict) and data1.get("success"):
            data1.pop("by", None); data1.pop("channel", None)
            data1["status"] = "success"
            return clean_dict(data1)
    except Exception as e1:
        print(f"[UPI] ftosint error: {e1}")

    # ── Attempt 2: old custom/base endpoint ─────────────────────
    try:
        custom_endpoint = get_api_endpoint('upi')
        url2 = build_api_url(custom_endpoint, upi_id) if custom_endpoint else f"(UPI)upi={upi_id}"
        data2 = make_api_request(url2, timeout=15)
        if isinstance(data2, dict):
            data2.pop('channel', None)
            if not is_empty_response(data2):
                data2["status"] = "success"
                return clean_dict(data2)
    except Exception as e2:
        print(f"[UPI] base error: {e2}")

    return {"status": "error", "message": "NO DATA FOUND"}

def call_ifsc_api(ifsc):
    try:
        custom_endpoint = get_api_endpoint('ifsc')
        if custom_endpoint:
            url = build_api_url(custom_endpoint, ifsc)
        else:
            url = ep("ifsc", ifsc) or f"(IFSC)ifsc={ifsc}"
        data = make_api_request(url, timeout=15)
        if isinstance(data, dict):
            if 'channel' in data: del data['channel']
            if is_empty_response(data):
                return {"status": "error", "message": "NO DATA FOUND"}
            return clean_dict(data)
        return {"status": "error", "message": "NO DATA FOUND"}
    except:
        return {"status": "error", "message": "NO DATA FOUND"}

def call_insta_api(username):
    try:
        url = ep("insta", username) or f"(INSTA)username={username}"
        data = make_api_request(url, timeout=20)
        if isinstance(data, dict):
            if data.get('success') == False or data.get('status') == 'error':
                return {"status": "error", "message": data.get('message', 'API Error')}
            return clean_dict(data)
        return {"status": "error", "message": "NO DATA FOUND"}
    except Exception as e:
        return {"status": "error", "message": str(e)}

def call_leak_api(phone):
    """
    New API: {BASE_URL}/api/leak?number=<phone>
    Response: { "records": [{Phone, Phone2-10, Adres, Adres2-8, FullName,
                              FatherName, DocumentNumber, Region}, ...] }
    Falls back to old 100.31 endpoint on failure.
    """
    phone = re.sub(r'[^\d+]', '', phone).lstrip('+')
    new_ip = BASE_URL

    def _parse_chain_records(chain_block, source_label):
        """Parse one chain/icmr block into normalised record dicts."""
        raw_recs = chain_block.get("records", [])
        title    = chain_block.get("title", source_label)
        out = []
        for r in raw_recs:
            if not isinstance(r, dict):
                continue
            # phones — new API goes up to Phone15
            phones = []
            for k in (["Phone"] + [f"Phone{i}" for i in range(2, 16)]):
                v = str(r.get(k, "")).strip()
                if v and v.upper() not in ("NA", "N/A", "") and len(v) >= 7:
                    phones.append(v)
            # addresses — up to Adres8
            addrs = []
            for k in (["Adres"] + [f"Adres{i}" for i in range(2, 9)]):
                v = str(r.get(k, "")).strip()
                if v:
                    addrs.append(v.replace("!", ", "))
            # ICMR records use lowercase keys
            name    = r.get("FullName") or r.get("name", "N/A")
            father  = r.get("FatherName") or r.get("father", "N/A")
            doc_no  = str(r.get("DocumentNumber", r.get("aadhar", "N/A"))).strip()
            region  = str(r.get("Region", r.get("state", "N/A"))).strip()
            age_val = str(r.get("age", "N/A")).strip()
            gender  = str(r.get("gender", "N/A")).strip()
            district= str(r.get("district", "N/A")).strip()

            rec = {
                "source":          title,
                "phones":          ", ".join(phones) if phones else "N/A",
                "name":            name,
                "father_name":     father,
                "address":         addrs[0] if addrs else r.get("address", "N/A"),
                "all_addresses":   " | ".join(addrs[1:]) if len(addrs) > 1 else "",
                "document_number": doc_no,
                "region":          region,
            }
            if age_val    not in ("N/A", "None", ""): rec["age"]      = age_val
            if gender     not in ("N/A", "None", ""): rec["gender"]   = gender
            if district   not in ("N/A", "None", ""): rec["district"] = district
            out.append(rec)
        return out

    def _normalise_leak(raw, query_num):
        """
        New API: response has top-level "chain" and "icmr" blocks.
        Old API: top-level "records" list.
        Merge all into one flat list.
        """
        all_records = []

        # ── New API: chain block ────────────────────────────────
        chain = raw.get("chain")
        if isinstance(chain, dict):
            all_records.extend(_parse_chain_records(chain, "HiTeckGroop"))

        # ── New API: icmr block ─────────────────────────────────
        icmr = raw.get("icmr")
        if isinstance(icmr, dict):
            all_records.extend(_parse_chain_records(icmr, "ICMR 2025"))

        # ── Old flat API: top-level records/results ─────────────
        if not all_records:
            flat = raw.get("records", raw.get("results", raw.get("data", [])))
            if isinstance(flat, list):
                all_records.extend(_parse_chain_records({"records": flat}, "LeakDB"))

        if not all_records:
            return None

        return {
            "status":    "success",
            "number":    query_num,
            "total":     len(all_records),
            "records":   all_records[:40],      # leakpro ships 400+ rows, 40 is enough
            "truncated": len(all_records) > 40,
        }

    # ── Attempt 1: new 68.211 API ───────────────────────────────
    try:
        leak_q = phone if len(phone) > 10 else "91" + phone   # leakpro wants 91XXXXXXXXXX
        url1 = ep("leak", leak_q) or f"(LEAK)number={phone}"
        data1 = _norm_provider("leak", make_api_request(url1, timeout=60))
        if isinstance(data1, dict) and data1.get("status") == "error":
            return data1
        if isinstance(data1, dict) and data1.get("status") == "success" \
                and isinstance(data1.get("records"), list) and data1["records"]:
            _grand = len(data1["records"])
            data1["grand_total"] = _grand
            data1["records"] = data1["records"][:15]     # leakpro ships 400+ rows
            data1["total"] = _grand
            return clean_dict(data1)
        if isinstance(data1, dict) and data1.get("success") is not False:
            result = _normalise_leak(data1, phone)
            if result:
                return clean_dict(result)
    except Exception as e1:
        print(f"[LEAK] new API error: {e1}")

    # ── Attempt 2: old 100.31 dead — removed ───────────────────

    return {"status": "error", "message": "NO DATA FOUND"}

def format_leak_result(result, query, credits_left):
    """Format /leak response — all data in blockquote, paginated if > 1024 chars."""
    import time as _time
    e = NUM_EMOJIS
    divider = build_num_divider()
    start_ts = _time.time()

    # ── error ──
    def _err(msg_text):
        txt = (
            divider
            + f"{te(e['phone_title'], '📞')}  <b>𝗟𝗘𝗔𝗞 𝗗𝗕 𝗟𝗢𝗢𝗞𝗨𝗣</b>  {te(e['phone_title'], '📞')}\n"
            + divider
            + f"\n<blockquote>"
            + f"{te(e['query'], '🔭')} <b>Qᴜᴇʀʏ</b>  : <code>{query}</code>\n"
            + f"{te(e['status_ok'], '❌')} {msg_text}"
            + f"</blockquote>\n\n"
            + divider
            + f"{te(e['credits'], '🧱')} <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: {credits_left}\n"
            + divider
        )
        return [(txt, None)]

    if not result or result.get("status") == "error":
        return _err(result.get("message", "NO DATA FOUND") if result else "NO DATA FOUND")

    # ── flatten whatever array the API returns ──
    records = []
    if isinstance(result.get("results"), list):
        records = result["results"]
    elif isinstance(result.get("data"), list):
        records = result["data"]
    elif isinstance(result.get("records"), list):
        records = result["records"]
    elif isinstance(result, list):
        records = result

    # if still empty, try to render the raw dict as a single record
    if not records:
        if isinstance(result, dict) and result.get("status") != "error":
            records = [result]
        else:
            return _err("NO DATA FOUND")

    total = len(records)
    _grand = result.get("grand_total") or total if isinstance(result, dict) else total
    _shown_label = f"{total} of {_grand}" if _grand and _grand > total else str(total)

    RECORDS_PER_PAGE = 3
    pages_data = [records[i:i+RECORDS_PER_PAGE] for i in range(0, total, RECORDS_PER_PAGE)]
    total_pages = len(pages_data)

    SKIP_KEYS = {'status', 'success', 'channel', 'message', 'by', 'credit', 'latency',
                 'response_metadata', 'developer', 'contact', 'key_expiry', 'owner'}

    def _fv(val):
        """Format a field value — return cleaned string or dash."""
        if val is None:
            return "—"
        s = str(val).strip()
        return s if s and s.lower() not in ("none", "null", "", "n/a", "na", "-") else "—"

    def _render_record(rec, idx, abs_total):
        """Render a single record dict into HTML lines inside a <blockquote>."""
        lines = [
            f"━━━━━━━━━━━━━━━━━━",
            f"{te(e['record_badge'], '📰')} <b>Rᴇᴄᴏʀᴅ {idx}/{abs_total}</b>",
            f"━━━━━━━━━━━━━━━━━━",
            f"<blockquote>",
        ]
        if not isinstance(rec, dict):
            lines.append(str(rec))
            lines.append("</blockquote>")
            return "\n".join(lines)

        # priority fields first
        PRIORITY = [
            # ── Normalised fields from new 68.211 API ──────────────
            ("phones",          e["number"],       "📲", "Pʜᴏɴᴇꜱ"),
            ("name",            e["name"],         "👤", "Nᴀᴍᴇ"),
            ("father_name",     e["father"],       "👥", "Fᴀᴛʜᴇʀ"),
            ("address",         e["address"],      "🏡", "Aᴅᴅʀᴇꜱꜱ"),
            ("all_addresses",   e["address"],      "🏡", "Aʟʟ Aᴅᴅʀᴇꜱꜱᴇꜱ"),
            ("document_number", e["id_card"],      "💳", "Dᴏᴄᴜᴍᴇɴᴛ No"),
            ("region",          e["circle"],       "🔎", "Rᴇɢɪᴏɴ"),
            # ── Legacy / old API fields ────────────────────────────
            ("mobile",          e["number"],       "📲", "Mᴏʙɪʟᴇ"),
            ("number",          e["number"],       "📲", "Nᴜᴍʙᴇʀ"),
            ("phone",           e["number"],       "📲", "Pʜᴏɴᴇ"),
            ("fname",           e["name"],         "👤", "Fɪʀꜱᴛ Nᴀᴍᴇ"),
            ("first_name",      e["name"],         "👤", "Fɪʀꜱᴛ Nᴀᴍᴇ"),
            ("last_name",       e["name"],         "👤", "Lᴀꜱᴛ Nᴀᴍᴇ"),
            ("father",          e["father"],       "👥", "Fᴀᴛʜᴇʀ"),
            ("email",           e["email"],        "📧", "Eᴍᴀɪʟ"),
            ("city",            e["circle"],       "🔎", "Cɪᴛʏ"),
            ("state",           e["circle"],       "🔎", "Sᴛᴀᴛᴇ"),
            ("pincode",         e["circle"],       "🔎", "Pɪɴᴄᴏᴅᴇ"),
            ("dob",             e["id_card"],      "💳", "DOB"),
            ("id",              e["id_card"],      "💳", "ID"),
            ("aadhar",          e["id_card"],      "💳", "Aᴀᴅʜᴀʀ"),
            ("pan",             e["id_card"],      "💳", "PAN"),
            ("alternate",       e["alt_num"],      "📞", "Aʟᴛ Nᴜᴍ"),
            ("alt",             e["alt_num"],      "📞", "Aʟᴛ Nᴜᴍ"),
            ("circle",          e["circle"],       "🔎", "Cɪʀᴄʟᴇ"),
            ("source",          e["record_badge"], "📰", "Sᴏᴜʀᴄᴇ"),
            ("breach",          e["record_badge"], "📰", "Bʀᴇᴀᴄʜ"),
            ("age",             e["id_card"],      "🗓️", "Aɢᴇ"),
            ("gender",          e["name"],         "👤", "Gᴇɴᴅᴇʀ"),
            ("district",        e["circle"],       "🔎", "Dɪꜱᴛʀɪᴄᴛ"),
            ("password",        e["id_card"],      "💳", "Pᴀꜱꜱᴡᴏʀᴅ"),
            ("hash",            e["id_card"],      "💳", "Hᴀꜱʜ"),
            ("username",        e["name"],         "👤", "Uꜱᴇʀɴᴀᴍᴇ"),
        ]
        rendered_keys = set()
        for field, emoji_key, fb, label in PRIORITY:
            if field in rec and field not in rendered_keys:
                v = _fv(rec[field])
                if v != "—":
                    lines.append(f"{te(emoji_key, fb)} <b>{label}</b>: {v}")
                    rendered_keys.add(field)

        # remaining keys not already shown
        for k, v in rec.items():
            if k in rendered_keys or k in SKIP_KEYS:
                continue
            sv = _fv(v)
            if sv != "—":
                display = k.replace("_", " ").title()
                lines.append(f"{te(e['record_badge'], '📰')} <b>{display}</b>: {sv}")

        lines.append("</blockquote>")
        return "\n".join(lines)

    out_pages = []
    for page_idx, page_records in enumerate(pages_data):
        page_num = page_idx + 1
        record_start = page_idx * RECORDS_PER_PAGE + 1

        header = (
            divider
            + f"{te(e['phone_title'], '📞')}  <b>𝗟𝗘𝗔𝗞 𝗗𝗕 𝗟𝗢𝗢𝗞𝗨𝗣</b>  "
            f"{te(e['phone_title'], '📞')}\n"
            + divider
            + f"\n<blockquote>"
            f"{te(e['status_ok'], '✅')} Lᴇᴀᴋᴇᴅ Dᴀᴛᴀʙᴀꜱᴇ ✅\n\n"
            f"{te(e['query'], '🔭')} <b>Qᴜᴇʀʏ</b>   : <code>{query}</code>\n"
            f"{te(e['records'], '✍️')} <b>Rᴇᴄᴏʀᴅꜱ</b> : {_shown_label} | Page {page_num}/{total_pages}"
            f"</blockquote>\n\n"
        )

        body_parts = []
        for r_idx, record in enumerate(page_records):
            abs_num = record_start + r_idx
            body_parts.append(_render_record(record, abs_num, total))

        elapsed = round(_time.time() - start_ts, 2)
        try:
            bot_username = f"@{bot.get_me().username}"
        except Exception:
            bot_username = "@YourBot"

        footer = (
            divider
            + f"{te(e['speed'], '🚀')} <b>Sᴩᴇᴇᴅ</b>: {elapsed}s\n"
            + f"{te(e['credits'], '🧱')} <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: {credits_left}\n"
            + divider
            + f"{te(e['bot_icon'], '🤖')} <b>Pᴏᴡᴇʀᴇᴅ Bʏ</b>: <b>{bot_username}</b>  {te(e['star'], '🌟')}\n"
            + divider
        )

        full_txt = header + "\n".join(body_parts) + "\n\n" + footer

        # ── paginate if > 4096 ──
        if len(full_txt) <= 4096:
            markup = None
            if total_pages > 1:
                markup = InlineKeyboardMarkup(row_width=3)
                btns = []
                if page_idx > 0:
                    btns.append(create_primary_button("◀ Prev", callback_data=f"leak_page_{page_idx - 1}_{0}"))
                btns.append(create_success_button(f"{page_num}/{total_pages}", callback_data="noop"))
                if page_idx < total_pages - 1:
                    btns.append(create_danger_button("Next ▶", callback_data=f"leak_page_{page_idx + 1}_{0}"))
                markup.row(*btns)
            out_pages.append((full_txt, markup))
        else:
            # split at record boundaries
            sub_parts = [header]
            for part in body_parts:
                candidate = "".join(sub_parts) + part + "\n\n"
                if len(candidate + footer) > 4096 and len(sub_parts) > 1:
                    sub_parts.append(footer)
                    out_pages.append(("".join(sub_parts), None))
                    sub_parts = [header, part + "\n\n"]
                else:
                    sub_parts.append(part + "\n\n")
            sub_parts.append(footer)
            out_pages.append(("".join(sub_parts), None))

    return out_pages if out_pages else [(_err("NO DATA FOUND")[0][0], None)]

def format_number_result(result, query, credits_left):
    import time as _time

    divider = build_num_divider()
    e = NUM_EMOJIS

    def _err(msg_text):
        txt = (
            divider
            + f"{te(e['phone_title'], '📞')}  <b>𝗡𝗨𝗠𝗕𝗘𝗥 𝗜𝗡𝗙𝗢</b>  {te(e['phone_title'], '📞')}\n"
            + divider
            + f"\n<blockquote>"
            + f"{te(e['query'], '🔭')} Qᴜᴇʀʏ  : <code>{query}</code>\n"
            + f"{te(e['status_ok'], '❌')} {msg_text}"
            + f"</blockquote>\n\n"
            + divider
            + f"{te(e['credits'], '🧱')} Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ: <b>{credits_left}</b>\n"
            + divider
        )
        return [(txt, None)]

    if not result or result.get("status") == "error":
        return _err(result.get("message", "NO DATA FOUND") if result else "NO DATA FOUND")

    records = result.get("records", [])
    total   = result.get("total", len(records))

    if not records:
        return _err("NO DATA FOUND")

    RECORDS_PER_PAGE = 2
    pages_data = [records[i:i+RECORDS_PER_PAGE] for i in range(0, len(records), RECORDS_PER_PAGE)]
    total_pages = len(pages_data)

    start_ts = _time.time()
    out = []

    for page_idx, page_records in enumerate(pages_data):
        page_num    = page_idx + 1
        record_start = page_idx * RECORDS_PER_PAGE + 1

        txt  = divider
        txt += (
            f"{te(e['phone_title'], '📞')}  <b>𝗡𝗨𝗠𝗕𝗘𝗥 𝗜𝗡𝗙𝗢</b>  "
            f"{te(e['phone_title'], '📞')}\n"
        )
        txt += divider

        txt += (
            f"\n<blockquote>"
            f"{te(e['status_ok'], '✅')} Nᴜᴍʙᴇʀ Dᴀᴛᴀʙᴀꜱᴇ ✅\n\n"
            f"{te(e['query'],   '🔭')} Qᴜᴇʀʏ    : <code>{result.get('number', query)}</code>\n"
            f"{te(e['records'], '✍️')} Rᴇᴄᴏʀᴅꜱ  : {total} | Page {page_num}/{total_pages}"
            f"</blockquote>\n\n"
        )

        for r_idx, record in enumerate(page_records):
            abs_num = record_start + r_idx
            txt += (
                f"━━━━━━━━━━━━━━━━━━\n"
                f"{te(e['record_badge'], '📰')} Rᴇᴄᴏʀᴅ {abs_num}/{total}\n"
                f"━━━━━━━━━━━━━━━━━━\n"
            )

            def _field(val):
                return val if val and str(val).strip() not in ("N/A", "None", "null", "") else "—"

            txt += f"<blockquote>"
            txt += f"{te(e['number'],  '📲')} <b>Nᴜᴍʙᴇʀ</b>    : <code>{_field(record.get('mobile'))}</code>\n"
            txt += f"{te(e['name'],    '👤')} <b>Nᴀᴍᴇ</b>      : {_field(record.get('name'))}\n"
            _tc = _field(record.get('truecaller_name'))
            if _tc != "—": txt += f"{te(e['name'], '📛')} <b>TC Nᴀᴍᴇ</b>   : {_tc}\n"
            txt += f"{te(e['father'],  '👥')} <b>Fᴀᴛʜᴇʀ</b>    : {_field(record.get('father_name'))}\n"
            txt += f"{te(e['alt_num'], '📞')} <b>Aʟᴛ Nᴜᴍ</b>   : <code>{_field(record.get('alternate'))}</code>\n"
            txt += f"{te(e['circle'],  '🔎')} <b>Cɪʀᴄʟᴇ</b>    : {_field(record.get('circle'))}\n"
            txt += f"{te(e['address'], '🏡')} <b>Aᴅᴅʀᴇꜱꜱ</b>  : {_field(record.get('address'))}\n"
            txt += f"{te(e['id_card'], '💳')} <b>Iᴅ</b>        : <code>{_field(record.get('id'))}</code>\n"
            txt += f"{te(e['email'],   '📧')} <b>Eᴍᴀɪʟ</b>     : {_field(record.get('email'))}\n"
            txt += f"</blockquote>\n\n"

        elapsed = round(_time.time() - start_ts, 2)
        bot_username = "@YourBot"
        try:
            bot_username = f"@{bot.get_me().username}"
        except Exception:
            pass

        txt += divider
        txt += (
            f"{te(e['speed'],    '🚀')} ʀᴇꜱᴩᴏɴꜱᴇ ᴛɪᴍᴇ: {elapsed}s\n"
            f"{te(e['credits'],  '🧱')} ᴄʀᴇᴅɪᴛꜱ ʟᴇꜰᴛ: <b>{credits_left}</b>\n"
        )
        txt += divider
        txt += (
            f"{te(e['bot_icon'], '🤖')} Pᴏᴡᴇʀᴇᴅ Bʏ: <b>{bot_username}</b>  "
            f"{te(e['star'], '🌟')}\n"
        )
        txt += divider

        markup = None
        if total_pages > 1:
            markup = InlineKeyboardMarkup(row_width=3)
            buttons = []

            if page_num > 1:
                buttons.append(
                    create_primary_button(
                        "Prev",
                        callback_data=f"num_page_{page_num - 1}_{query}",
                        icon_custom_emoji_id="5246794802560774143"
                    )
                )

            buttons.append(
                create_success_button(
                    f"{page_num}/{total_pages}",
                    callback_data="num_page_noop",
                    icon_custom_emoji_id="5422537279400868395"
                )
            )

            if page_num < total_pages:
                buttons.append(
                    create_danger_button(
                        "Next",
                        callback_data=f"num_page_{page_num + 1}_{query}",
                        icon_custom_emoji_id="6192763368139397161"
                    )
                )

            markup.row(*buttons)

            if page_num == total_pages:
                markup.add(
                    InlineKeyboardButton("Download JSON", callback_data="num_dl_json")
                )

        out.append((txt, markup))

    return out
def format_aadhar_result(result, query, credits_left):
    import time as _time

    e       = ADHR_EMOJIS
    divider = build_adhr_divider()

    def _field(val):
        return val if val and str(val).strip() not in ("N/A", "None", "null", "", "—") else "—"

    def _err(msg_text):
        txt = (
            divider
            + f"{te(e['adhr_title'], '🪪')}  <b>𝗔𝗔𝗗𝗛𝗔𝗥 𝗜𝗡𝗙𝗢</b>  {te(e['adhr_title'], '🪪')}\n"
            + divider
            + f"\n<blockquote>"
            + f"{te(e['query'], '🔭')} <b>Qᴜᴇʀʏ</b>  : <code>{query}</code>\n"
            + f"{te(e['status_ok'], '❌')} {msg_text}"
            + f"</blockquote>\n\n"
            + divider
            + f"{te(e['credits'], '📊')} <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: {credits_left}\n"
            + divider
        )
        return [(txt, None)]

    if not result or result.get("status") == "error":
        return _err(result.get("message", "NO DATA FOUND") if result else "NO DATA FOUND")

    records = result.get("records", [])
    total   = result.get("total", len(records))

    if not records:
        return _err("NO DATA FOUND")

    RECORDS_PER_PAGE = 4
    pages_data  = [records[i:i + RECORDS_PER_PAGE] for i in range(0, len(records), RECORDS_PER_PAGE)]
    total_pages = len(pages_data)
    start_ts    = _time.time()
    out         = []

    for page_idx, page_records in enumerate(pages_data):
        page_num     = page_idx + 1
        record_start = page_idx * RECORDS_PER_PAGE + 1

        # ── header ──
        txt  = divider
        txt += f"{te(e['adhr_title'], '🪪')}  <b>𝗔𝗔𝗗𝗛𝗔𝗥 𝗜𝗡𝗙𝗢</b>  {te(e['adhr_title'], '🪪')}\n"
        txt += divider
        txt += (
            f"<blockquote>"
            f"{te(e['status_ok'], '✅')} Aᴀᴅʜᴀʀ Dᴀᴛᴀʙᴀꜱᴇ ✅\n\n"
            f"{te(e['query'],   '🔭')} <b>Qᴜᴇʀʏ</b>   : <code>{query}</code>\n"
            f"{te(e['records'], '✍️')} <b>Rᴇᴄᴏʀᴅꜱ</b> : {total} | Page {page_num}/{total_pages}"
            f"</blockquote>\n\n"
        )

        # ── records ──
        for r_idx, record in enumerate(page_records):
            abs_num   = record_start + r_idx
            email_val = _field(record.get('email'))

            txt += (
                f"<blockquote>"
                f"━━━━━━━━━━━━━━━━━━\n"
                f"{te(e['record_badge'], '📰')} <b>Rᴇᴄᴏʀᴅ {abs_num}/{total}</b>\n"
                f"━━━━━━━━━━━━━━━━━━\n"
                f"{te(e['mobile'],  '📲')} <b>Mᴏʙɪʟᴇ</b>   : <code>{_field(record.get('mobile'))}</code>\n"
                f"{te(e['name'],    '👤')} <b>Nᴀᴍᴇ</b>     : {_field(record.get('name'))}\n"
                f"{te(e['father'],  '👥')} <b>Fᴀᴛʜᴇʀ</b>   : {_field(record.get('father_name'))}\n"
                f"{te(e['circle'],  '🛜')} <b>Cɪʀᴄʟᴇ</b>   : {_field(record.get('circle'))}\n"
                f"{te(e['address'], '🏡')} <b>Aᴅᴅʀᴇꜱꜱ</b> : {_field(record.get('address'))}\n"
                f"{te(e['id_card'], '💳')} <b>Aᴀᴅʜᴀᴀʀ</b>  : <code>{_field(record.get('aadhar'))}</code>\n"
                + (f"{te(e['email'], '📧')} <b>Eᴍᴀɪʟ</b>    : {email_val}\n" if email_val != "—" else "")
                + f"</blockquote>\n\n"
            )

        # ── footer ──
        elapsed      = round(_time.time() - start_ts, 2)
        bot_username = "@YourBot"
        try:
            bot_username = f"@{bot.get_me().username}"
        except Exception:
            pass

        txt += divider
        txt += (
            f"<blockquote>"
            f"{te(e['speed'],    '🚀')} <b>ʀᴇꜱᴩᴏɴꜱᴇ ᴛɪᴍᴇ</b>:- {elapsed}s\n"
            f"{te(e['credits'],  '📊')} <b>ᴄʀᴇᴅɪᴛꜱ ʟᴇꜰᴛ</b>:- {credits_left}\n"
            f"</blockquote>\n"
        )
        txt += divider
        txt += (
            f"<blockquote>"
            f"{te(e['bot_icon'], '🤖')} Pᴏᴡᴇʀᴇᴅ Bʏ: <b>{bot_username}</b>  {te(e['star'], '🌟')}\n"
            f"</blockquote>\n"
        )
        txt += divider

        # ── pagination buttons ──
        markup = None
        if total_pages > 1:
            markup  = InlineKeyboardMarkup(row_width=3)
            buttons = []
            if page_num > 1:
                buttons.append(create_primary_button(
                    "Prev",
                    callback_data=f"num_page_{page_num - 1}_{query}",
                    icon_custom_emoji_id="5246794802560774143"
                ))
            buttons.append(create_success_button(
                f"{page_num}/{total_pages}",
                callback_data="num_page_noop",
                icon_custom_emoji_id="5422537279400868395"
            ))
            if page_num < total_pages:
                buttons.append(create_danger_button(
                    "Next",
                    callback_data=f"num_page_{page_num + 1}_{query}",
                    icon_custom_emoji_id="6192763368139397161"
                ))
            markup.row(*buttons)
            if page_num == total_pages:
                markup.add(InlineKeyboardButton("Download JSON", callback_data="num_dl_json"))

        out.append((txt, markup))

    return out


# ============================================================
# VEHICLE / RC FORMATTER WITH PAGINATION
# ============================================================

VECH_PAGINATION = {}   # user_id -> {"pages": [str], "current": int, "query": str, "json_file": str}

def _vfield(data, *keys, default="N/A"):
    """Safely extract nested dict values."""
    for k in keys:
        if isinstance(data, dict):
            data = data.get(k)
        else:
            return default
    return data if data is not None and str(data).strip() not in ("", "None", "null", "N/A") else default

def _vfmt(val):
    return str(val) if val and str(val).strip() not in ("", "None", "null", "N/A", "—") else "N/A"

def format_vehicle_result_v2(result, query, credits_left):
    """
    Format /vech response.
    Handles both new flat API (success/vehicle/owner_name/mobile_number/
    chassis_number/engine_number) and old nested API structures.
    All output in <blockquote> blocks, premium emoji, paginated if > 1024 chars.
    """
    import time as _time
    e = VECH_EMOJIS
    divider = build_vech_divider()

    def _err(msg_text):
        txt = (
            divider
            + f"{te(e['veh_title'], '🪪')}  <b>𝗩𝗘𝗛𝗜𝗖𝗟𝗘 𝗜𝗡𝗙𝗢</b>  {te(e['veh_title'], '🪪')}\n"
            + divider
            + f"\n<blockquote>"
            + f"{te(e['query'], '🔭')} <b>Qᴜᴇʀʏ</b>   : <code>{query}</code>\n"
            + f"{te(e['status_ok'], '❌')} {msg_text}"
            + f"</blockquote>\n\n"
            + divider
            + f"{te(e['credits'], '🧱')} <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: {credits_left}\n"
            + divider
        )
        return [txt]

    if not result or result.get("status") == "error":
        return _err(result.get("message", "NO DATA FOUND") if result else "NO DATA FOUND")

    def _f(val):
        v = str(val).strip() if val is not None else ""
        return v if v and v.lower() not in ("n/a", "none", "null", "—", "") else "—"

    start_ts = _time.time()

    # ── New flat API response ────────────────────────────────────────
    # Keys: status, vehicle, owner_name, mobile_number, chassis_number, engine_number
    if result.get("vehicle") and (result.get("owner_name") or result.get("mobile_number")):
        owner      = _f(result.get("owner_name"))
        mobile     = _f(result.get("mobile_number"))
        chassis    = _f(result.get("chassis_number"))
        engine     = _f(result.get("engine_number"))
        rc_num     = _f(result.get("vehicle", query))
        elapsed    = round(_time.time() - start_ts, 2)
        try:
            bot_username = "@" + bot.get_me().username
        except Exception:
            bot_username = "@YourBot"

        txt = (
            divider
            + f"{te(e['veh_title'], '🪪')}  <b>𝗩𝗘𝗛𝗜𝗖𝗟𝗘 𝗜𝗡𝗙𝗢</b>  {te(e['veh_title'], '🪪')}\n"
            + divider
            + f"\n<blockquote>"
            + f"{te(e['query'],   '🔭')} <b>Qᴜᴇʀʏ</b>      : <code>{query}</code>\n"
            + f"{te(e['status_ok'],'✅')} <b>Sᴛᴀᴛᴜꜱ</b>     : ᴅᴀᴛᴀ ꜰᴏᴜɴᴅ ✅\n"
            + f"</blockquote>\n\n"
            + f"<blockquote>"
            + f"{te(e['rc_number'],  '🚗')} <b>Vᴇʜɪᴄʟᴇ</b>    : <code>{rc_num}</code>\n"
            + f"{te(e['owner'],      '👨‍🦰')} <b>Oᴡɴᴇʀ</b>      : {owner}\n"
            + f"{te(e['mobile'],     '📲')} <b>Mᴏʙɪʟᴇ</b>     : <code>{mobile}</code>\n"
            + f"{te(e['chassis'],    '🔧')} <b>Cʜᴀꜱꜱɪꜱ</b>    : <code>{chassis}</code>\n"
            + f"{te(e['engine'],     '⚙️')} <b>Eɴɢɪɴᴇ</b>     : <code>{engine}</code>\n"
            + f"</blockquote>\n\n"
            + divider
            + f"{te(e['speed'],   '🚀')} <b>Sᴩᴇᴇᴅ</b>: {elapsed}s\n"
            + f"{te(e['credits'], '🧱')} <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: {credits_left}\n"
            + divider
            + f"{te(e['bot_icon'],'🤖')} <b>Pᴏᴡᴇʀᴇᴅ Bʏ</b>: <b>{bot_username}</b>  {te(e['star'],'🌟')}\n"
            + divider
        )
        return [txt]

    # ── Old nested API response — parse deep structure ───────────────
    d = result
    if "result" in result and isinstance(result["result"], dict):
        d = result["result"]
    if "data" in d and isinstance(d["data"], dict):
        d = d["data"]

    mobile_top = str(d.get("mobile", "")).strip() if isinstance(d, dict) else ""

    s1 = {}; s2 = {}; a2 = {}
    try: s1 = d["vehicle_info"]["results"]["api1"]["result"]["source1"]["details"]
    except Exception: pass
    try: s2 = d["vehicle_info"]["results"]["api1"]["result"]["source2"]["data"]["Nexus2"]
    except Exception: pass
    try: a2 = d["vehicle_info"]["results"]["api2"]["data"]["data"]
    except Exception: pass

    def _g(*keys, srcs=(s1, s2, a2), default="N/A"):
        for src in srcs:
            if not isinstance(src, dict): continue
            val = src
            for k in keys:
                val = val.get(k) if isinstance(val, dict) else None
                if val is None: break
            if val is not None and str(val).strip() not in ("", "None", "null", "N/A", "—"):
                return str(val).strip()
        return default

    def _g2(key, srcs=(s1, s2, a2), default="N/A"):
        for src in srcs:
            if not isinstance(src, dict): continue
            for k in (key, " " + key, key + " ", " " + key + " "):
                if k in src:
                    v = src[k]
                    if v is not None and str(v).strip() not in ("", "None", "null", "N/A", "—"):
                        return str(v).strip()
        return default

    owner      = _g2("Reg Owner") or _g2("Owner Name") or _g2("owner")
    mobile_num = mobile_top or _g2("Mobile Number") or _g2("Mobile No")
    chassis    = _g2("Chassis Number") or _g2("Chassis No") or _g2("chassis")
    engine     = _g2("Engine Number") or _g2("Engine No") or _g2("engine")
    reg_date   = _g2("Registration Date") or _g2("Reg Date")
    fuel_type  = _g2("Fuel Type") or _g2("fuel_type")
    vehicle_cls= _g2("Vehicle Category") or _g2("Class of Vehicle")
    mfg_yr     = _g2("Year of Manufacture") or _g2("Manufacture Year")
    color      = _g2("Colour") or _g2("Color")
    ins_co     = _g2("Insurance Company Name") or _g2("Insurance Company")
    ins_valid  = _g2("Insurance Upto") or _g2("Insurance Valid")
    rto_name   = _g2("RTO Name") or _g2("Registered RTO")
    state      = _g2("State") or _g2("state")
    father     = _g2("Father") or _g2("father_name")
    address    = _g2("Present Address") or _g2("address")

    elapsed = round(_time.time() - start_ts, 2)
    try:
        bot_username = "@" + bot.get_me().username
    except Exception:
        bot_username = "@YourBot"

    def _row(emoji_key, fb, label, val):
        if val and val not in ("N/A", "—"):
            return f"{te(e.get(emoji_key, e['query']), fb)} <b>{label}</b>: {val}\n"
        return ""

    txt = (
        divider
        + f"{te(e['veh_title'], '🪪')}  <b>𝗩𝗘𝗛𝗜𝗖𝗟𝗘 𝗜𝗡𝗙𝗢</b>  {te(e['veh_title'], '🪪')}\n"
        + divider
        + f"\n<blockquote>"
        + f"{te(e['query'],   '🔭')} <b>Qᴜᴇʀʏ</b>   : <code>{query}</code>\n"
        + f"{te(e['status_ok'],'✅')} <b>Sᴛᴀᴛᴜꜱ</b>  : ᴅᴀᴛᴀ ꜰᴏᴜɴᴅ ✅\n"
        + f"</blockquote>\n\n"
        + f"<blockquote>"
        + _row('rc_number', '🚗', 'Vᴇʜɪᴄʟᴇ', query)
        + _row('owner', '👨‍🦰', 'Oᴡɴᴇʀ', owner)
        + _row('mobile', '📲', 'Mᴏʙɪʟᴇ', mobile_num)
        + _row('chassis', '🔧', 'Cʜᴀꜱꜱɪꜱ', chassis)
        + _row('engine', '⚙️', 'Eɴɢɪɴᴇ', engine)
        + _row('fuel', '⛽', 'Fᴜᴇʟ', fuel_type)
        + _row('vclass', '🚗', 'Cʟᴀꜱꜱ', vehicle_cls)
        + _row('mfg_year', '📅', 'Mꜰɢ Yᴇᴀʀ', mfg_yr)
        + _row('reg_date', '📅', 'Rᴇɢ Dᴀᴛᴇ', reg_date)
        + _row('colour', '🎨', 'Cᴏʟᴏᴜʀ', color)
        + _row('father', '👥', 'Fᴀᴛʜᴇʀ', father)
        + _row('address', '🏡', 'Aᴅᴅʀᴇꜱꜱ', address)
        + f"</blockquote>\n\n"
        + f"<blockquote>"
        + _row('insurance', '🛡', 'Iɴꜱᴜʀᴀɴᴄᴇ', ins_co)
        + _row('ins_status', '📅', 'Iɴꜱ Vᴀʟɪᴅ', ins_valid)
        + _row('rto_code', '🗺', 'RTO', rto_name)
        + _row('registration', '📍', 'Sᴛᴀᴛᴇ', state)
        + f"</blockquote>\n\n"
        + divider
        + f"{te(e['speed'],   '🚀')} <b>Sᴩᴇᴇᴅ</b>: {elapsed}s\n"
        + f"{te(e['credits'], '🧱')} <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: {credits_left}\n"
        + divider
        + f"{te(e['bot_icon'],'🤖')} <b>Pᴏᴡᴇʀᴇᴅ Bʏ</b>: <b>{bot_username}</b>  {te(e['star'],'🌟')}\n"
        + divider
    )
    return [txt]

def format_rc_result_v2(result, query, credits_left):
    """Format /vechrc response — parses flat sectioned JSON."""
    import time as _time
    e = VECH_EMOJIS
    divider = build_vech_divider()

    def _err(msg_text):
        txt = (
            divider
            + f"{te(e['veh_title'], '🪪')}  <b>𝗥𝗖 𝗜𝗡𝗙𝗢</b>  {te(e['veh_title'], '🪪')}\n"
            + divider
            + f"\n<blockquote>"
            + f"{te(e['query'], '🔭')} <b>Qᴜᴇʀʏ</b>  : <code>{query}</code>\n"
            + f"{te(e['status_ok'], '❌')} {msg_text}"
            + f"</blockquote>\n\n"
            + divider
            + f"{te(e['credits'], '🧱')} <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: {credits_left}\n"
            + divider
        )
        return [txt]

    if not result or result.get("status") == "error":
        return _err(result.get("message", "NO DATA FOUND") if result else "NO DATA FOUND")

    d = result
    if "result" in result and isinstance(result["result"], dict):
        d = result["result"]

    def _sec(name):
        return d.get(name, {}) if isinstance(d, dict) else {}

    def _v(val, default="N/A"):
        return str(val).strip() if val is not None and str(val).strip() not in ("", "None", "null", "N/A", "—") else default

    own = _sec("Ownership Details")
    veh = _sec("Vehicle Details")
    ins = _sec("Insurance Information")
    dates = _sec("Important Dates & Validity")
    other = _sec("Other Information")
    card = _sec("Basic Card Info")
    alert = _sec("Insurance Alert")
    reg_num = _v(d.get("registration_number", query))

    rc_num      = _v(own.get("Registration Number", reg_num))
    owner_name  = _v(own.get("Owner Name", card.get("Owner Name")))
    rto_name    = _v(own.get("Registered RTO"))

    make        = _v(veh.get("Model Name", card.get("Modal Name")))
    model       = _v(veh.get("Maker Model", veh.get("Model Name")))
    vclass      = _v(veh.get("Vehicle Class"))
    fuel        = _v(veh.get("Fuel Type"))
    chassis_no  = _v(veh.get("Chassis Number"))
    engine_no   = _v(veh.get("Engine Number"))

    ins_expiry  = _v(ins.get("Insurance Expiry", ins.get("If your insurance has expired, renew it")))
    ins_company = _v(ins.get("Insurance Company"))
    policy_no   = _v(ins.get("Insurance No"))

    reg_date    = _v(dates.get("Registration Date"))
    vehicle_age = _v(dates.get("Vehicle Age"))
    fitness     = _v(dates.get("Fitness Upto"))
    ins_upto    = _v(dates.get("Insurance Upto"))
    ins_alert   = _v(dates.get("Insurance Expiry In"))

    financer    = _v(other.get("Financer Name"))
    cc_val      = _v(other.get("Cubic Capacity"))
    seating     = _v(other.get("Seating Capacity"))
    permit      = _v(other.get("Permit Type"))
    blacklist   = _v(other.get("Blacklist Status"))
    noc         = _v(other.get("NOC Details"))

    city        = _v(card.get("City Name"))
    phone       = _v(card.get("Phone"))
    website     = _v(card.get("Website"))
    address     = _v(card.get("Address"))
    code        = _v(card.get("Code"))

    expired_days = _v(alert.get("Expired Days"))

    start_ts = _time.time()

    lines = []
    lines.append(divider)
    lines.append(f"{te(e['veh_title'], '🪪')}  <b>𝗥𝗖 𝗜𝗡𝗙𝗢</b>  {te(e['veh_title'], '🪪')}")
    lines.append(divider)
    lines.append("")
    lines.append(f"{te(e['rc_number'], '🚗')} <b>Rᴄ Nᴜᴍʙᴇʀ</b>  : <code>{rc_num}</code>")
    lines.append(f"{te(e['source'], '💎')} <b>Sᴏᴜʀᴄᴇ</b>    : ꜰᴇʟɪxᴀᴩɪ {te(e['status_ok'], '✅')}")
    lines.append("")

    # Vehicle Details
    lines.append("━━━━━━━━━━━━━━━━━━━━━")
    lines.append(f"{te(e['vehicle'], '🚗')} <b>Vᴇʜɪᴄʟᴇ Dᴇᴛᴀɪʟꜱ</b>")
    lines.append("━━━━━━━━━━━━━━━━━━━━━")
    lines.append(f"  {te(e['make'], '🏭')} <b>Mᴀᴋᴇ</b>         : {make}")
    lines.append(f"  {te(e['vehicle'], '🚗')} <b>Mᴏᴅᴇʟ</b>        : {model}")
    lines.append(f"  {te(e['vclass'], '👿')} <b>Cʟᴀꜱꜱ</b>         : {vclass}")
    lines.append(f"  {te(e['fuel'], '⚡️')} <b>Fᴜᴇʟ</b>         : {fuel}")
    lines.append(f"  {te(e['cc'], '⚙️')} <b>Cᴄ</b>            : {cc_val}")
    lines.append(f"  {te(e['seating'], '🐸')} <b>Sᴇᴀᴛɪɴɢ</b>      : {seating}")
    lines.append(f"  {te(e['chassis'], '🔧')} <b>Cʜᴀꜱꜱɪꜱ</b>     : <code>{chassis_no}</code>")
    lines.append(f"  {te(e['engine'], '⚙️')} <b>Eɴɢɪɴᴇ</b>       : <code>{engine_no}</code>")
    lines.append("")

    # Owner Info
    lines.append("━━━━━━━━━━━━━━━━━━━━━")
    lines.append(f"{te(e['body'], '🏎')} <b>Oᴡɴᴇʀ Iɴꜰᴏ</b>")
    lines.append("━━━━━━━━━━━━━━━━━━━━━")
    lines.append(f"  {te(e['owner'], '👨‍🦰')} <b>Nᴀᴍᴇ</b>         : {owner_name}")
    lines.append(f"  {te(e['address'], '🏡')} <b>Aᴅᴅʀᴇꜱꜱ</b>      : {address}")
    lines.append(f"  {te(e['rto'], '🗺')} <b>Cɪᴛʏ</b>          : {city}")
    lines.append(f"  {te(e['mobile'], '📲')} <b>Pʜᴏɴᴇ</b>        : {phone}")
    lines.append("")

    # Registration
    lines.append("━━━━━━━━━━━━━━━━━━━━━")
    lines.append(f"{te(e['registration'], '0️⃣')} <b>𝗥𝗘𝗚𝗜𝗦𝗧𝗥𝗔𝗧𝗜𝗢𝗡</b>")
    lines.append("━━━━━━━━━━━━━━━━━━━━━")
    lines.append(f"  {te(e['reg_date'], '🗓️')} <b>Rᴇɢ Dᴀᴛᴇ</b>     : {reg_date}")
    lines.append(f"  {te(e['rto'], '🗺')} <b>Rᴛᴏ</b>           : {rto_name}")
    lines.append(f"  {te(e['rto_code'], '🔢')} <b>Rᴛᴏ Cᴏᴅᴇ</b>    : {code}")
    lines.append(f"  {te(e['financer'], '🏢')} <b>Fɪɴᴀɴᴄᴇʀ</b>     : {financer}")
    lines.append(f"  {te(e['reg_date'], '🗓️')} <b>Fɪᴛɴᴇꜱꜱ Uᴘᴛᴏ</b> : {fitness}")
    lines.append(f"  {te(e['status_ok'], '✅')} <b>Bʟᴀᴄᴋʟɪꜱᴛ</b>   : {blacklist}")
    lines.append(f"  {te(e['status_ok'], '✅')} <b>NOC</b>          : {noc}")
    lines.append(f"  {te(e['reg_date'], '🗓️')} <b>Vᴇʜɪᴄʟᴇ Aɢᴇ</b>  : {vehicle_age}")
    lines.append("")

    # Insurance
    lines.append("━━━━━━━━━━━━━━━━━━━━━")
    lines.append(f"{te(e['insurance'], '🏎')} <b>𝗜𝗡𝗦𝗨𝗥𝗔𝗡𝗖𝗘</b>")
    lines.append("━━━━━━━━━━━━━━━━━━━━━")
    lines.append(f"  {te(e['ins_status'], '🛡')} <b>Sᴛᴀᴛᴜꜱ</b>        : {ins_alert}")
    lines.append(f"  {te(e['financer'], '🏢')} <b>Cᴏᴍᴩᴀɴʏ</b>      : {ins_company}")
    lines.append(f"  {te(e['colour'], '📋')} <b>Pᴏʟɪᴄʏ ɴᴏ.</b>  : <code>{policy_no}</code>")
    lines.append(f"  {te(e['reg_date'], '🗓️')} <b>Eхᴘɪʀʏ</b>       : {ins_expiry}")
    lines.append(f"  {te(e['reg_date'], '🗓️')} <b>Eхᴘɪʀᴇᴅ Dᴀʏꜱ</b> : {expired_days}")
    lines.append("")

    # Other Info
    lines.append("━━━━━━━━━━━━━━━━━━━━━")
    lines.append(f"{te(e['technical'], '⚙️')} <b>𝗢𝗧𝗛𝗘𝗥 𝗜𝗡𝗙𝗢</b>")
    lines.append("━━━━━━━━━━━━━━━━━━━━━")
    lines.append(f"  {te(e['commercial'], '💎')} <b>Pᴇʀᴍɪᴛ</b>       : {permit}")
    lines.append(f"  {te(e['rto'], '🗺')} <b>Wᴇʙꜱɪᴛᴇ</b>      : {website}")
    lines.append("")

    # Footer
    elapsed = round(_time.time() - start_ts, 2)
    try:
        bot_username = f"@{bot.get_me().username}"
    except Exception:
        bot_username = "@YourBot"

    lines.append(f"{te(e['credits'], '🧱')} <b>ᴄʀᴇᴅɪᴛꜱ ʟᴇꜰᴛ</b>:- {credits_left}")
    lines.append(divider)
    lines.append(f"{te(e['bot_icon'], '🤖')} <b>Pᴏᴡᴇʀᴇᴅ Bʏ</b>: <b>{bot_username}</b>  {te(e['star'], '🌟')}")
    lines.append(divider)

    full_text = "\n".join(lines)

    wrapped = f"<blockquote>{full_text}</blockquote>"
    if len(wrapped) <= 4096 and len(full_text) <= 3500:
        return [wrapped]

    # Split at section boundaries
    sec_markers = [
        "━━━━━━━━━━━━━━━━━━━━━\n  🏭 <b>Mᴀᴋᴇ</b>",         # vehicle details start
        "━━━━━━━━━━━━━━━━━━━━━\n  👨‍🦰 <b>Nᴀᴍᴇ</b>",         # owner info start
        "━━━━━━━━━━━━━━━━━━━━━\n  🗓️ <b>Rᴇɢ Dᴀᴛᴇ</b>",     # registration start
        "━━━━━━━━━━━━━━━━━━━━━\n  🛡 <b>Sᴛᴀᴛᴜꜱ</b>",        # insurance start
        "━━━━━━━━━━━━━━━━━━━━━\n  💎 <b>Pᴇʀᴍɪᴛ</b>",        # other info start
        "🧱 <b>ᴄʀᴇᴅɪᴛꜱ ʟᴇꜰᴛ</b>",                           # footer start
    ]

    split_positions = [0]
    for marker in sec_markers:
        pos = full_text.find(marker)
        if pos != -1 and pos not in split_positions:
            split_positions.append(pos)
    split_positions.sort()
    split_positions.append(len(full_text))

    pages = []
    for i in range(len(split_positions) - 1):
        page_text = full_text[split_positions[i]:split_positions[i+1]].rstrip("\n")
        if page_text:
            pages.append(page_text)

    merged = []
    current = ""
    for page in pages:
        test = current + ("\n" if current else "") + page
        if len(test) <= 1024:
            current = test
        else:
            if current:
                merged.append(current)
            current = page
    if current:
        merged.append(current)

    final_pages = []
    for i, page in enumerate(merged, 1):
        if len(merged) > 1:
            page += f"\n{te(e['records'], '✍️')} <b>Page {i}/{len(merged)}</b>"
        final_pages.append(f"<blockquote>{page}</blockquote>")

    return final_pages if final_pages else [f"<blockquote>{full_text}</blockquote>"]


def send_paginated_vech(chat_id, user_id, pages, json_file, query, wait_message=None, command="vech", posts_username=None):
    """Send paginated result with Prev/Next buttons; optionally add Instagram See Post."""
    if wait_message:
        try:
            bot.delete_message(chat_id, wait_message.message_id)
        except:
            pass

    VECH_PAGINATION[user_id] = {
        "pages": pages,
        "current": 0,
        "query": query,
        "json_file": json_file,
        "command": command,
        "posts_username": posts_username,
    }

    _send_vech_page(chat_id, user_id, 0)


def _send_vech_page(chat_id, user_id, page_idx):
    state = VECH_PAGINATION.get(user_id)
    if not state:
        return

    pages = state["pages"]
    if page_idx < 0 or page_idx >= len(pages):
        return

    state["current"] = page_idx
    text = pages[page_idx]

    markup = InlineKeyboardMarkup(row_width=3)
    buttons = []

    if len(pages) > 1:
        if page_idx > 0:
            buttons.append(create_primary_button(
                "◀ Prev",
                callback_data=f"vech_page_{page_idx - 1}_{user_id}",
                icon_custom_emoji_id="5246794802560774143"
            ))

        buttons.append(create_success_button(
            f"{page_idx + 1}/{len(pages)}",
            callback_data=f"vech_noop_{user_id}",
            icon_custom_emoji_id="5422537279400868395"
        ))

        if page_idx < len(pages) - 1:
            buttons.append(create_danger_button(
                "Next ▶",
                callback_data=f"vech_page_{page_idx + 1}_{user_id}",
                icon_custom_emoji_id="6192763368139397161"
            ))

        markup.row(*buttons)

    if state.get("posts_username"):
        markup.add(create_primary_button(
            "📸 See Post",
            callback_data=f"viewall_{state['posts_username']}",
            icon_custom_emoji_id=SEE_POST_EMOJI_ID,
        ))

    # JSON download on last page
    json_file = state.get("json_file")
    if page_idx == len(pages) - 1 and json_file:
        file_id = hashlib.md5(json_file.encode()).hexdigest()[:16]
        JSON_FILES[file_id] = json_file
        markup.add(InlineKeyboardButton("📥 Download JSON", callback_data=f"dljson_{file_id}"))

    markup.add(create_default_button("🔙 Back", callback_data="back_to_result", icon_custom_emoji_id="5307517685846785869"))

    sent = send_with_premium(chat_id, text, reply_markup=markup)
    if sent:
        schedule_deletion(sent.message_id, chat_id)
        send_random_media(chat_id, sent.message_id)



def format_insta_result_compact(result, query, credits_left):
    """Exact compact Instagram layout supplied by the user."""
    e = INSTA_EMOJIS
    p = result
    username = str(p.get("username", query) or query)
    full_name = str(p.get("full_name", p.get("name", "N/A")) or "N/A")
    user_id = str(p.get("user_id", p.get("pk", p.get("id", "N/A"))) or "N/A")
    followers = p.get("follower_count", p.get("followers", 0)) or 0
    following = p.get("following_count", p.get("following", 0)) or 0
    posts_value = p.get("posts")
    posts_count = posts_value if isinstance(posts_value, (int, float)) and not isinstance(posts_value, bool) else p.get("posts_count", p.get("media_count", 0))
    bio = str(p.get("biography", p.get("bio", "")) or "").replace("\n", " ")
    bio = bio[:170] + ("…" if len(bio) > 170 else "")
    status = "🔒 Private" if p.get("is_private") else "🌍 Public"
    verified = "✅" if p.get("is_verified") else "❌"
    divider11 = te(e["header_divider"], "➿") * 11
    divider14 = te(e["header_divider"], "➿") * 14
    divider20 = te(e["header_divider"], "➿") * 20
    lines = [
        "<blockquote>",
        f"⏤͟͟͞͞{OWNER_NAME}:",
        divider11,
        "",
        te(e["insta_title"], "📸") + "  <b>𝗜𝗡𝗦𝗧𝗔𝗚𝗥𝗔𝗠 𝗜𝗡𝗙𝗢</b>",
        te(e["username"], "👤") + " <b>Username</b>: @" + _html.escape(username) + " " + verified,
        te(e["name"], "👑") + " <b>Name</b>: " + _html.escape(full_name),
        te(e["user_id"], "🆔") + " <b>ID</b>:",
        _html.escape(user_id),
        divider14,
        te(e["status"], "🔒") + " <b>Status</b>: " + status,
        te(e["followers"], "👥") + " <b>Followers</b>: " + format_number(followers),
        te(e["following"], "🔄") + " <b>Following</b>: " + format_number(following),
        te(e["posts"], "📱") + " <b>Posts</b>: " + format_number(posts_count),
        divider20,
        "🗒 <b>Bio</b>: " + _html.escape(bio),
        te(e["credits"], "🧱") + " <b>Credits Left</b>: " + str(credits_left),
        "</blockquote>",
    ]
    return "\n".join(lines)



def format_insta_result_v3(result, query, credits_left):
    """Format /insta response from (INSTA) API with premium emojis."""
    import time as _time
    e = INSTA_EMOJIS
    divider = build_insta_divider()
    start_ts = _time.time()

    # The new API is flat. Use a compact one-message layout so photo captions
    # retain premium emoji and blockquote formatting under Telegram's 1024 limit.
    if isinstance(result, dict) and result.get("username") and not isinstance(result.get("result"), dict):
        return format_insta_result_compact(result, query, credits_left)

    def _err(msg_text):
        lines = []
        lines.append("<blockquote>")
        lines.append(divider)
        lines.append(te(e["insta_title"], "📸") + "  <b>𝗜𝗡𝗦𝗧𝗔𝗚𝗥𝗔𝗠 𝗜𝗡𝗙𝗢</b>  " + te(e["insta_title"], "📸"))
        lines.append(divider)
        lines.append("")
        lines.append(te(e["username"], "⭐") + " <b>Qᴜᴇʀʏ</b>  : <code>" + str(query) + "</code>")
        lines.append(te(e["status"], "❌") + " " + str(msg_text))
        lines.append("")
        lines.append(divider)
        lines.append(te(e["credits"], "🧱") + " <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: " + str(credits_left))
        lines.append(divider)
        lines.append("</blockquote>")
        return chr(10).join(lines)

    if not result or result.get("status") == "error":
        return _err(result.get("message", "NO DATA FOUND") if result else "NO DATA FOUND")

    raw_profile = result.get("result", {}).get("profile", {}) if isinstance(result.get("result"), dict) else {}
    if not raw_profile:
        raw_profile = result.get("profile", {})
    # New /api/insta response keeps profile fields at the top level.
    # Keep the old nested-schema support above for existing/fallback APIs.
    if not raw_profile and result.get("username"):
        raw_profile = result
    if not raw_profile:
        return _err("NO DATA FOUND")

    p = raw_profile
    username      = str(p.get("username", query) or query)
    full_name     = str(p.get("full_name", p.get("name", "N/A")) or "N/A")
    user_id       = str(p.get("id", p.get("user_id", p.get("pk", "N/A"))) or "N/A")
    is_private    = bool(p.get("is_private", False))
    is_business   = bool(p.get("is_business_account", p.get("is_business", False)))
    is_verified   = bool(p.get("is_verified", False))
    is_professional = bool(p.get("is_professional_account", False))
    joined_year   = str(p.get("account_creation_year", p.get("joined", "N/A")) or "N/A")
    followers     = p.get("followers", p.get("follower_count", 0)) or 0
    following     = p.get("following", p.get("following_count", 0)) or 0
    # New API uses `posts` for the full post list, so never print that list as the count.
    posts_value   = p.get("posts")
    posts_count   = posts_value if isinstance(posts_value, (int, float)) and not isinstance(posts_value, bool) else p.get("posts_count", p.get("media_count", 0))
    posts_count   = posts_count or 0
    bio           = str(p.get("biography", p.get("bio", "")) or "")
    external_url  = str(p.get("external_url", "") or "")
    category_name = str(p.get("category_name", "") or "")

    if is_business:
        acc_type = "💼 ʙᴜꜱɪɴᴇꜱꜱ"
    elif is_professional:
        acc_type = "💼 ᴩʀᴏꜰᴇꜱꜱɪᴏɴᴀʟ"
    else:
        acc_type = "👤 ᴩᴇʀꜱᴏɴᴀʟ"

    status_icon = "🔒" if is_private else "🌍"
    status_text = "ᴩʀɪᴠᴀᴛᴇ" if is_private else "ᴩᴜʙʟɪᴄ"
    verified_badge = "✅" if is_verified else "❌"

    elapsed = round(_time.time() - start_ts, 2)
    try:
        bot_username = "@" + bot.get_me().username
    except Exception:
        bot_username = "@YourBot"

    lines = []
    lines.append("<blockquote>")
    # Header
    lines.append(divider)
    lines.append(te(e["insta_title"], "📸") + "  <b>𝗜𝗡𝗦𝗧𝗔𝗚𝗥𝗔𝗠 𝗜𝗡𝗙𝗢</b>  " + te(e["insta_title"], "📸"))
    lines.append(divider)
    lines.append("")
    # Profile info
    lines.append(te(e["username"], "⭐") + " <b>ᴜꜱᴇʀɴᴀᴍᴇ</b>  » @" + username + " " + verified_badge)
    lines.append(te(e["name"], "👑") + " <b>Nᴀᴍᴇ</b>      » " + full_name)
    lines.append(te(e["user_id"], "🆔") + " <b>ᴜꜱᴇʀ ɪᴅ</b>   » " + user_id)
    lines.append(te(e["status"], "🔒") + " <b>ꜱᴛᴀᴛᴜꜱ</b>    » " + status_icon + " " + status_text)
    lines.append(te(e["acc_type"], "💼") + " <b>ᴀᴄᴄ ᴛʏᴩᴇ</b>  » " + acc_type)
    lines.append(te(e["joined"], "📅") + " <b>ᴊᴏɪɴᴇᴅ</b>     » " + joined_year)
    if bio:
        lines.append(te(e["name"], "👑") + " <b>ʙɪᴏ</b>        » " + bio[:150])
    if external_url:
        lines.append(te(e["profile"], "❔") + " <b>ʟɪɴᴋ</b>       » " + external_url[:50])
    if category_name and category_name.lower() != "none":
        lines.append(te(e["acc_type"], "💼") + " <b>ᴄᴀᴛᴇɢᴏʀʏ</b>  » " + category_name)
    lines.append("")
    # Stats
    lines.append(divider)
    lines.append(te(e["followers"], "👥") + " <b>ꜰᴏʟʟᴏᴡᴇʀꜱ</b> » " + format_number(followers))
    lines.append(te(e["following"], "🔄") + " <b>ꜰᴏʟʟᴏᴡɪɴɢ</b> » " + format_number(following))
    lines.append(te(e["posts"], "📱") + " <b>ᴩᴏꜱᴛꜱ</b>     » " + format_number(posts_count))
    lines.append("")
    # Footer
    lines.append(divider)
    lines.append(te(e["speed"], "🚀") + " <b>ʀᴇꜱᴩᴏɴꜱᴇ ᴛɪᴍᴇ</b>:- " + str(elapsed) + "s")
    lines.append(te(e["credits"], "🧱") + " <b>ᴄʀᴇᴅɪᴛꜱ ʟᴇꜰᴛ</b>:- " + str(credits_left))
    lines.append(divider)
    lines.append(te(e["bot_icon"], "🤖") + " <b>Pᴏᴡᴇʀᴇᴅ Bʏ</b>: <b>" + bot_username + "</b>  " + te(e["star"], "🌟"))
    lines.append(divider)
    lines.append("</blockquote>")
    return chr(10).join(lines)

# ── TGID formatter emoji dict ────────────────────────────────────
TG_EMOJIS = {
    "header_divider": "5467641505525016018",
    "tg_title":       "6172503852785342178",   # ✈️ telegram-style
    "query":          "5379999674193172777",   # 🔭
    "tgid":           "5985796637971191405",   # 💳 (id card)
    "username":       "5425124408786197150",   # 👤
    "name":           "6122805733936342496",   # 📛
    "phone":          "6026092115631543342",   # 📱
    "country":        "5895476993314524652",   # 🌍 (was the 🔭 id — showed wrong icon)
    "type":           "6129812419028982717",   # 🔍 (from EMOJI_TO_PREMIUM)
    "uid":            "5193037303961920951",   # 🆔 (from INSTA_EMOJIS)
    "cc":             "5453965363286925977",   # 🔒
    "status_ok":      "6129812419028982717",   # ✅
    "status_err":     "5296491800423340716",   # ❌
    "note":           "5423183595930422680",   # 💡
    "speed":          "6203911118964924015",   # 🚀
    "credits":        "5326049357332513437",   # 🧱
    "bot_icon":       "5355051922862653659",   # 🤖
    "star":           "6118385795976930086",   # 🌟
}


def _tg_full_phone(phone, cc):
    """Return phone with country code: '7487492' + '+40' -> '+407487492'."""
    if not phone or phone == "—":
        return phone
    p = str(phone).replace(" ", "").replace("-", "")
    if p.startswith("+"):
        return p
    ccd = re.sub(r"\D", "", cc or "") if cc and cc != "—" else ""
    if not ccd:
        return p
    # already contains the country code (e.g. '919876543210' with cc +91)
    if p.startswith(ccd) and len(p) >= len(ccd) + 9:
        return "+" + p
    return f"+{ccd}{p}"


def format_tgid_result(result, query, credits_left, elapsed=None):
    """Compact, modern Telegram ID result card (Telegram controls actual font size)."""
    import html as _html
    def clean(value):
        value = str(value).strip() if value is not None else ""
        return value if value and value.lower() not in ("n/a", "none", "null", "—", "") else "—"
    safe_query = _html.escape(clean(query))
    if not result or result.get("status") != "success":
        reason = clean(result.get("message", "No data found") if result else "No data found")
        return ("<b>🔎 Telegram lookup</b>\n"
                f"<blockquote>Query: <code>{safe_query}</code>\n"
                f"⚠️ {_html.escape(reason)}</blockquote>\n"
                f"💎 Credits left: <b>{_html.escape(str(credits_left))}</b>")
    fields = [
        ("🆔 ID", result.get("tgid")),
        ("👤 Username", ("@" + str(result.get("username")).lstrip("@")) if result.get("username") else None),
        ("📛 Name", result.get("name")),
        ("📱 Phone", result.get("number", result.get("phone"))),
        ("🌍 Country", result.get("country")),
        ("☎️ Country code", result.get("country_code")),
        ("💬 Note", result.get("note")),
    ]
    lines=[]
    for label, value in fields:
        value=clean(value)
        if value != "—":
            lines.append(f"{label}: <code>{_html.escape(value)}</code>")
    details = "\n".join(lines) if lines else "No additional public information available."
    duration = f"\n⚡ {elapsed:.2f}s" if isinstance(elapsed, (int,float)) else ""
    return ("<b>🔎 Telegram lookup</b>\n"
            f"<blockquote>Query: <code>{safe_query}</code>\n{details}</blockquote>"
            f"💎 Credits left: <b>{_html.escape(str(credits_left))}</b>{duration}")

# ── UPI formatter emoji dict ──────────────────────────────────────
UPI_EMOJIS = {
    "header_divider": "5467641505525016018",
    "upi_title":      "5985796637971191405",   # 💳
    "query":          "5379999674193172777",   # 🔭
    "name":           "5425124408786197150",   # 👤
    "bank":           "6305370152145787193",   # 🏦
    "upi":            "5985796637971191405",   # 💳
    "app":            "6122805733936342496",   # 📱
    "valid":          "6129812419028982717",   # ✅
    "invalid":        "5296491800423340716",   # ❌
    "type":           "5197269100878907942",   # ✍️
    "speed":          "6203911118964924015",   # 🚀
    "credits":        "5326049357332513437",   # 🧱
    "bot_icon":       "5355051922862653659",   # 🤖
    "star":           "6118385795976930086",   # 🌟
}


def format_upi_result(result, query, credits_left):
    """
    Rich blockquote UPI formatter.
    Response fields: upi_id, name, username, handle, valid,
                     account_type, bank, bank_id, app, handle_bank
    """
    import time as _time
    e = UPI_EMOJIS
    div_e = te(e["header_divider"], "➿")
    divider = (div_e * 10) + "\n"
    start_ts = _time.time()

    try: bot_username = "@" + bot.get_me().username
    except Exception: bot_username = "@YourBot"

    def _err(msg_text):
        return [(
            divider
            + f"{te(e['upi_title'], '💳')}  <b>𝗨𝗣𝗜 𝗜𝗗 𝗜𝗡𝗙𝗢</b>  {te(e['upi_title'], '💳')}\n"
            + divider
            + f"\n<blockquote>"
            + f"{te(e['query'],   '🔭')} <b>Qᴜᴇʀʏ</b>  : <code>{query}</code>\n"
            + f"{te(e['invalid'], '❌')} {msg_text}"
            + f"</blockquote>\n\n"
            + divider
            + f"{te(e['credits'], '🧱')} <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: {credits_left}\n"
            + divider
        , None)]

    if not result or result.get("status") == "error":
        return _err(result.get("message", "NO DATA FOUND") if result else "NO DATA FOUND")

    def _f(val):
        v = str(val).strip() if val is not None else ""
        return v if v and v.lower() not in ("n/a", "none", "null", "—", "") else "—"

    upi_id    = _f(result.get("upi_id", query))
    name      = _f(result.get("name"))
    username  = _f(result.get("username"))
    handle    = _f(result.get("handle"))
    valid     = result.get("valid", False)
    acc_type  = _f(result.get("account_type"))
    bank      = _f(result.get("bank"))
    app       = _f(result.get("app"))
    hbank     = _f(result.get("handle_bank"))
    valid_str = f"{te(e['valid'], '✅')} ᴠᴀʟɪᴅ" if valid else f"{te(e['invalid'], '❌')} ɪɴᴠᴀʟɪᴅ"
    elapsed   = round(_time.time() - start_ts, 2)

    txt = (
        divider
        + f"{te(e['upi_title'], '💳')}  <b>𝗨𝗣𝗜 𝗜𝗗 𝗜𝗡𝗙𝗢</b>  {te(e['upi_title'], '💳')}\n"
        + divider
        + f"\n<blockquote>"
        + f"{te(e['query'],  '🔭')} <b>Qᴜᴇʀʏ</b>       : <code>{query}</code>\n"
        + f"{te(e['valid'],  '✅')} <b>Sᴛᴀᴛᴜꜱ</b>      : {valid_str}\n"
        + f"</blockquote>\n\n"
        + f"<blockquote>"
        + f"{te(e['upi'],   '💳')} <b>UPI ID</b>       : <code>{upi_id}</code>\n"
        + f"{te(e['name'],  '👤')} <b>Nᴀᴍᴇ</b>        : {name}\n"
        + (f"{te(e['name'], '👤')} <b>Uꜱᴇʀɴᴀᴍᴇ</b>   : {username}\n" if username != "—" else "")
        + (f"{te(e['upi'],  '💳')} <b>Hᴀɴᴅʟᴇ</b>      : @{handle}\n" if handle != "—" else "")
        + f"</blockquote>\n\n"
        + f"<blockquote>"
        + f"{te(e['bank'],  '🏦')} <b>Bᴀɴᴋ</b>        : {bank}\n"
        + (f"{te(e['bank'], '🏦')} <b>Hᴀɴᴅʟᴇ Bᴀɴᴋ</b>: {hbank}\n" if hbank not in ("—", bank) else "")
        + (f"{te(e['type'], '✍️')} <b>Aᴄᴄ Tʏᴩᴇ</b>   : {acc_type}\n" if acc_type != "—" else "")
        + (f"{te(e['app'],  '📱')} <b>Aᴩᴩ</b>         : {app}\n" if app != "—" else "")
        + f"</blockquote>\n\n"
        + divider
        + f"{te(e['speed'],   '🚀')} <b>Sᴩᴇᴇᴅ</b>: {elapsed}s\n"
        + f"{te(e['credits'], '🧱')} <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: {credits_left}\n"
        + divider
        + f"{te(e['bot_icon'],'🤖')} <b>Pᴏᴡᴇʀᴇᴅ Bʏ</b>: <b>{bot_username}</b>  {te(e['star'],'🌟')}\n"
        + divider
    )
    return [(txt, None)]


def format_api_result(result, title, query, credits_left):
    if isinstance(result, dict) and result.get('status') == 'error' and result.get('message') == 'NO DATA FOUND':
        msg = (f"<b>{title}</b>\n"
               f"<blockquote>Query: <code>{query}</code>\n⚠️ No data found</blockquote>"
               f"💎 Credits left: <b>{credits_left}</b>")
        return msg

    SKIP_KEYS = {'status', 'channel', 'by', 'owner', 'credit', 'message', 'success', 'latency',
                 'response_metadata', 'makeData', 'modelData', 'variant', 'less_info', 'masked_name',
                 'developer', 'contact', 'tag', 'key_expiry'}

    DISPLAY_NAMES = {
        'rc_number': 'RC Number', 'registration_number': 'Registration Number',
        'fit_up_to': 'Fitness Valid Upto', 'registration_date': 'Registration Date',
        'owner_name': 'Owner Name', 'father_name': 'Father Name',
        'present_address': 'Present Address', 'mobile_number': 'Mobile Number',
        'vehicle_category': 'Vehicle Category', 'fuel_type': 'Fuel Type', 'color': 'Color',
        'insurance_company': 'Insurance Company', 'manufacturing_date': 'Manufacturing Date',
        'registered_at': 'Registered RTO', 'tax_upto': 'Tax Valid Upto',
        'user_id': 'User ID', 'username': 'Username', 'first_name': 'Name',
        'phone': 'Phone Number', 'email': 'Email', 'address': 'Address',
        'city': 'City', 'state': 'State', 'country': 'Country',
        'pincode': 'Pincode', 'pan': 'PAN Number', 'aadhar': 'Aadhar Number',
        'upi': 'UPI ID', 'ifsc': 'IFSC Code', 'bank': 'Bank Name',
        'branch': 'Branch', 'instagram': 'Instagram ID', 'followers': 'Followers',
        'following': 'Following', 'posts': 'Posts', 'bio': 'Bio',
        'ip': 'IP Address', 'location': 'Location', 'isp': 'ISP',
        'organization': 'Organization', 'asn': 'ASN'
    }

    all_data = []

    def extract_data(data, parent_key=""):
        if isinstance(data, dict):
            for key, value in data.items():
                if key in SKIP_KEYS:
                    continue
                display_key = DISPLAY_NAMES.get(key, key.replace('_', ' ').title())
                if parent_key:
                    display_key = f"{parent_key} {display_key}"
                if isinstance(value, dict):
                    extract_data(value, display_key)
                elif isinstance(value, list):
                    for item in value:
                        if isinstance(item, dict):
                            extract_data(item, display_key)
                        elif item and str(item).strip() and str(item).lower() not in ['none', 'null', '', 'n/a', 'na']:
                            all_data.append((display_key, str(item)))
                else:
                    if value and str(value).strip() and str(value).lower() not in ['none', 'null', '', 'n/a', 'na']:
                        all_data.append((display_key, str(value)))
        elif isinstance(data, list):
            for idx, item in enumerate(data):
                if isinstance(item, dict):
                    extract_data(item, f"Record {idx + 1}")
                elif item and str(item).strip() and str(item).lower() not in ['none', 'null', '', 'n/a', 'na']:
                    all_data.append((f"Item {idx + 1}", str(item)))

    extract_data(result)
    seen = set()
    unique_data = []
    for key, value in all_data:
        if key not in seen:
            seen.add(key)
            unique_data.append((key, value))

    if unique_data:
        formatted = ""
        for key, value in unique_data:
            emoji = get_emoji_for_key(key)
            formatted += f"{emoji} {key}: {value}\n"
    else:
        formatted = "📋 No detailed data available"

    msg = (f"<b>{title}</b>\n"
           f"<blockquote>Query: <code>{query}</code>\n{formatted.strip()}</blockquote>"
           f"💎 Credits left: <b>{credits_left}</b>")
    return msg

def format_number(n):
    try:
        n = int(n)
        if n >= 1000000:
            return f"{n/1000000:.1f}M"
        elif n >= 1000:
            return f"{n/1000:.1f}K"
        return str(n)
    except:
        return str(n)

def format_rc_result(result, query, credits_left):
    e = NUM_EMOJIS
    divider = build_num_divider()

    if isinstance(result, dict) and result.get('status') == 'error':
        lines = []
        lines.append(divider)
        lines.append(te(e['phone_title'], '📞') + "  <b>𝗥𝗖 𝗗𝗘𝗧𝗔𝗜𝗟𝗦</b>  " + te(e['phone_title'], '📞'))
        lines.append(divider)
        lines.append("")
        lines.append("<blockquote>")
        lines.append(te(e['query'], '🔭') + " <b>Qᴜᴇʀʏ</b>  : <code>" + str(query) + "</code>")
        lines.append(te(e['status_ok'], '❌') + " " + str(result.get('message', 'NO DATA FOUND')))
        lines.append("</blockquote>")
        lines.append("")
        lines.append(divider)
        lines.append(te(e['credits'], '🧱') + " <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: " + str(credits_left))
        lines.append(divider)
        return [chr(10).join(lines)]

    if result.get('success') == True and result.get('vehicle_data'):
        vd = result.get('vehicle_data', {})
        rto = vd.get('rtoData', {})

        lines1 = []
        lines1.append(divider)
        lines1.append(te(e['phone_title'], '📞') + "  <b>𝗥𝗖 𝗗𝗘𝗧𝗔𝗜𝗟𝗦</b>  " + te(e['phone_title'], '📞'))
        lines1.append(divider)
        lines1.append("")
        lines1.append("<blockquote>")
        lines1.append(te(e['number'], '📲') + " <b>Vᴇʜɪᴄʟᴇ</b>    : <code>" + str(result.get('vehicle_number', query)) + "</code>")
        lines1.append(te(e['id_card'], '💳') + " <b>Eɴɢɪɴᴇ</b>     : <code>" + str(result.get('engine_number', 'N/A')) + "</code>")
        lines1.append(te(e['id_card'], '💳') + " <b>Cʜᴀꜱꜱɪꜱ</b>    : <code>" + str(result.get('chassis_number', 'N/A')) + "</code>")
        lines1.append(te(e['alt_num'], '📞') + " <b>Mᴏʙɪʟᴇ</b>     : <code>" + str(result.get('mobile_number', 'N/A')) + "</code>")
        lines1.append("</blockquote>")
        lines1.append("")
        lines1.append("<blockquote>")
        lines1.append(te(e['name'], '👤') + " <b>Oᴡɴᴇʀ</b>      : " + str(vd.get('owner', 'N/A')))
        lines1.append(te(e['father'], '👥') + " <b>Fᴀᴛʜᴇʀ</b>     : " + str(vd.get('ownerFatherName', 'N/A')))
        lines1.append(te(e['address'], '🏡') + " <b>Aᴅᴅʀᴇꜱꜱ</b>   : " + str(vd.get('presentAddress', 'N/A')))
        lines1.append(te(e['circle'], '🔎') + " <b>Pɪɴᴄᴏᴅᴇ</b>    : " + str(vd.get('pincode', 'N/A')))
        lines1.append("</blockquote>")
        lines1.append("")
        lines1.append("<blockquote>")
        lines1.append(te(e['name'], '🚗') + " <b>Vᴇʜɪᴄʟᴇ</b>    : " + str(vd.get('vehicle', 'N/A')))
        lines1.append(te(e['name'], '🏭') + " <b>Mᴀɴᴜꜰᴀᴄᴛᴜʀᴇʀ</b> : " + str(vd.get('manufacturer', 'N/A')))
        lines1.append(te(e['name'], '⚙️') + " <b>Vᴀʀɪᴀɴᴛ</b>    : " + str(vd.get('variant', 'N/A')))
        lines1.append(te(e['name'], '⛽') + " <b>Fᴜᴇʟ</b>       : " + str(vd.get('fuelType', 'N/A')))
        lines1.append(te(e['name'], '📅') + " <b>Rᴇɢ Dᴀᴛᴇ</b>   : " + str(vd.get('regDate', 'N/A')))
        lines1.append(te(e['name'], '📅') + " <b>Mꜰɢ Yᴇᴀʀ</b>   : " + str(vd.get('manufacturerYear', 'N/A')))
        lines1.append("</blockquote>")
        lines1.append(divider)

        lines2 = []
        lines2.append(divider)
        lines2.append(te(e['phone_title'], '📞') + "  <b>𝗥𝗖 𝗗𝗘𝗧𝗔𝗜𝗟𝗦 (𝗖𝗼𝗻𝘁𝗶𝗻𝘂𝗲𝗱)</b>  " + te(e['phone_title'], '📞'))
        lines2.append(divider)
        lines2.append("")
        lines2.append("<blockquote>")
        lines2.append(te(e['name'], '🏛️') + " <b>RTO</b>        : " + str(rto.get('rtoName', 'N/A')))
        lines2.append(te(e['name'], '📍') + " <b>Sᴛᴀᴛᴇ</b>      : " + str(rto.get('statename', 'N/A')))
        lines2.append("</blockquote>")
        lines2.append("")
        lines2.append("<blockquote>")
        lines2.append(te(e['name'], '🏦') + " <b>Iɴꜱᴜʀᴀɴᴄᴇ</b>  : " + str(vd.get('insuranceCompanyName', 'N/A')))
        lines2.append(te(e['id_card'], '📋') + " <b>Pᴏʟɪᴄʏ</b>     : <code>" + str(vd.get('insurancePolicyNumber', 'N/A')) + "</code>")
        lines2.append(te(e['name'], '📅') + " <b>Vᴀʟɪᴅ Uᴘᴛᴏ</b> : " + str(vd.get('insuranceUpto', 'N/A')))
        lines2.append("</blockquote>")
        lines2.append("")
        lines2.append("<blockquote>")
        lines2.append(te(e['id_card'], '✅') + " <b>PUCC</b>       : <code>" + str(vd.get('puccNumber', 'N/A')) + "</code>")
        lines2.append(te(e['name'], '📅') + " <b>PUCC Vᴀʟɪᴅ</b> : " + str(vd.get('puccValidUpto', 'N/A')))
        lines2.append("</blockquote>")
        lines2.append("")
        lines2.append(divider)
        lines2.append(te(e['credits'], '🧱') + " <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: " + str(credits_left))
        lines2.append(divider)
        return [chr(10).join(lines1), chr(10).join(lines2)]

    return [format_api_result(result, "📋 RC DETAILS", query, credits_left)]

def auto_delete_post(chat_id, message_id, delay=120):
    _DELAYED.schedule(delay, bot.delete_message, chat_id, message_id)

def send_all_posts(chat_id, username, posts):
    """Send cached Instagram posts as Telegram photos only; never expose post URLs."""
    if not posts:
        send_with_premium(chat_id, "❌ No posts found!")
        return

    info_msg = send_with_premium(chat_id, f"📸 Sending {len(posts)} posts for @{username}...")
    auto_delete_post(chat_id, info_msg.message_id, 30)

    sent_count = 0
    for i, post in enumerate(posts, 1):
        image_url = post.get('img') or post.get('display_url') or post.get('thumbnail')
        if not image_url:
            print(f"Instagram post #{i} has no image URL")
            continue
        try:
            response = session.get(image_url, timeout=20, headers={"User-Agent": "Mozilla/5.0"})
            response.raise_for_status()
            photo = io.BytesIO(response.content)
            photo.name = f"instagram_post_{i}.jpg"
            caption = f"📸 <b>POST #{i}</b>\n\n@{username}\n\n⏰ This post will auto-delete in 2 minutes"
            sent_msg = bot.send_photo(chat_id, photo, caption=caption, parse_mode='HTML')
            auto_delete_post(chat_id, sent_msg.message_id)
            sent_count += 1
            time.sleep(0.4)
        except Exception as e:
            print(f"Instagram post photo send failed #{i} in chat {chat_id}: {e}")

    complete_msg = send_with_premium(chat_id, f"✅ {sent_count} post photo(s) sent for @{username}")
    auto_delete_post(chat_id, complete_msg.message_id, 60)

def format_insta_result_v2(result, username, credits_left):
    e = NUM_EMOJIS
    divider = build_num_divider()

    if result.get('success') == False or result.get('status') == 'error':
        lines = []
        lines.append(divider)
        lines.append(te(e['phone_title'], '📞') + "  <b>𝗜𝗡𝗦𝗧𝗔𝗚𝗥𝗔𝗠 𝗢𝗦𝗜𝗡𝗧</b>  " + te(e['phone_title'], '📞'))
        lines.append(divider)
        lines.append("")
        lines.append("<blockquote>")
        lines.append(te(e['status_ok'], '❌') + " " + str(result.get('message', 'NO DATA FOUND')))
        lines.append("</blockquote>")
        lines.append("")
        lines.append(divider)
        lines.append(te(e['credits'], '🧱') + " <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: " + str(credits_left))
        lines.append(divider)
        return chr(10).join(lines), None, []

    profile = result.get('profile', {})
    recent_posts = result.get('recent_posts', [])
    osint_data = result.get('osint', {})

    if not profile and result.get('username'):
        profile = result
    if not recent_posts:
        recent_posts = result.get('posts', result.get('media', []))
    if not osint_data:
        osint_data = result.get('osint_data', result.get('records', {}))

    username_display = profile.get('username') or username
    full_name = profile.get('name') or 'N/A'
    user_id_insta = profile.get('id') or 'N/A'
    bio = profile.get('bio') or 'No bio'
    followers = profile.get('followers') or 0
    following = profile.get('following') or 0
    posts_count = profile.get('posts') or 0
    is_verified = '✅' if profile.get('verified') else '❌'
    is_private = '🔒' if profile.get('private') else '🌍'
    profile_pic = profile.get('pic') or ''
    external_url = profile.get('external_url', '')
    business = '✅' if profile.get('is_business', False) else '❌'
    category = profile.get('category_name', 'N/A')

    lines = []
    lines.append(divider)
    lines.append(te(e['phone_title'], '📞') + "  <b>𝗜𝗡𝗦𝗧𝗔𝗚𝗥𝗔𝗠 𝗢𝗦𝗜𝗡𝗧</b>  " + te(e['phone_title'], '📞'))
    lines.append(divider)
    lines.append("")
    lines.append("<blockquote>")
    lines.append(te(e['name'], '👤') + " <b>Uꜱᴇʀɴᴀᴍᴇ</b>  : @" + str(username_display))
    lines.append(te(e['name'], '📛') + " <b>Nᴀᴍᴇ</b>      : " + str(full_name if full_name else 'Not provided'))
    lines.append(te(e['id_card'], '🆔') + " <b>ID</b>        : " + str(user_id_insta))
    lines.append(te(e['status_ok'], '📝') + " <b>Bɪᴏ</b>       : " + str(bio[:300] if bio else 'No bio'))
    lines.append("")
    lines.append(te(e['records'], '📊') + " <b>𝗦𝗧𝗔𝗧𝗦</b>")
    lines.append(te(e['name'], '👥') + " <b>Fᴏʟʟᴏᴡᴇʀꜱ</b> : " + str(format_number(followers)))
    lines.append(te(e['name'], '➡️') + " <b>Fᴏʟʟᴏᴡɪɴɢ</b> : " + str(format_number(following)))
    lines.append(te(e['name'], '🖼️') + " <b>Pᴏꜱᴛꜱ</b>     : " + str(format_number(posts_count)))
    lines.append(te(e['status_ok'], '✅') + " <b>Vᴇʀɪꜰɪᴇᴅ</b>  : " + str(is_verified))
    lines.append(te(e['status_ok'], '🔒') + " <b>Pʀɪᴠᴀᴛᴇ</b>   : " + str(is_private))
    lines.append(te(e['name'], '🏢') + " <b>Bᴜꜱɪɴᴇꜱꜱ</b>  : " + str(business))
    lines.append(te(e['name'], '📂') + " <b>Cᴀᴛᴇɢᴏʀʏ</b>  : " + str(category))
    lines.append("</blockquote>")

    if external_url:
        lines.append("")
        lines.append("<blockquote>" + te(e['status_ok'], '🔗') + " <b>Exᴛᴇʀɴᴀʟ URL</b>: " + str(external_url) + "</blockquote>")

    if osint_data.get('available') and osint_data.get('records'):
        records = osint_data.get('records', [])
        lines.append("")
        lines.append("<blockquote>" + te(e['status_ok'], '🔍') + " <b>𝗢𝗦𝗜𝗡𝗧 𝗥𝗘𝗖𝗢𝗥𝗗𝗦</b> (" + str(len(records)) + " found)</blockquote>")
        for idx_rec, record in enumerate(records, 1):
            lines.append("")
            lines.append("<blockquote>" + te(e['record_badge'], '📰') + " <b>Rᴇᴄᴏʀᴅ #" + str(idx_rec) + "</b>")
            if record.get('name'): lines.append("   " + te(e['name'], '👤') + " <b>Nᴀᴍᴇ</b>: " + str(record.get('name')))
            if record.get('email'): lines.append("   " + te(e['email'], '📧') + " <b>Eᴍᴀɪʟ</b>: " + str(record.get('email')))
            if record.get('phone'): lines.append("   " + te(e['number'], '📲') + " <b>Pʜᴏɴᴇ</b>: " + str(record.get('phone')))
            if record.get('address'): lines.append("   " + te(e['address'], '🏡') + " <b>Aᴅᴅʀᴇꜱꜱ</b>: " + str(record.get('address')[:200]))
            if record.get('city'): lines.append("   " + te(e['circle'], '🏙️') + " <b>Cɪᴛʏ</b>: " + str(record.get('city')))
            if record.get('state'): lines.append("   " + te(e['circle'], '🗺️') + " <b>Sᴛᴀᴛᴇ</b>: " + str(record.get('state')))
            if record.get('dob'): lines.append("   " + te(e['name'], '🎂') + " <b>DOB</b>: " + str(record.get('dob')))
            if record.get('aadhar'): lines.append("   " + te(e['id_card'], '🆔') + " <b>Aᴀᴅʜᴀʀ</b>: " + str(record.get('aadhar')))
            if record.get('pan'): lines.append("   " + te(e['id_card'], '📄') + " <b>PAN</b>: " + str(record.get('pan')))
            lines.append("</blockquote>")
        lines.append("")
    else:
        lines.append("")
        lines.append("<blockquote>" + te(e['status_ok'], '🔍') + " <b>𝗢𝗦𝗜𝗡𝗧 𝗥𝗘𝗖𝗢𝗥𝗗𝗦</b></blockquote>")
        lines.append("")
        lines.append(te(e['status_ok'], '❌') + " OSINT data not available")
        lines.append("")

    if recent_posts:
        lines.append("")
        lines.append("<blockquote>" + te(e['phone_title'], '📸') + " <b>𝗥𝗘𝗖𝗘𝗡𝗧 𝗣𝗢𝗦𝗧𝗦</b></blockquote>")
        lines.append("")
        lines.append(te(e['records'], '📊') + " <b>Tᴏᴛᴀʟ</b>: " + str(len(recent_posts)) + " posts")
        for idx_post, post in enumerate(recent_posts[:10], 1):
            likes = post.get('likes', post.get('like_count', 0))
            comments = post.get('comments', post.get('comment_count', 0))
            caption_text = post.get('caption', post.get('text', ''))[:50]
            post_line = "   " + te(e['phone_title'], '🖼️') + " <b>Pᴏꜱᴛ #" + str(idx_post) + "</b>: " + te(e['name'], '❤️') + str(format_number(likes)) + " " + te(e['name'], '💬') + str(format_number(comments))
            if caption_text: post_line += " - " + caption_text + "..."
            lines.append(post_line)
        if len(recent_posts) > 10:
            lines.append("   ... and " + str(len(recent_posts) - 10) + " more posts")
        lines.append(te(e['status_ok'], '💡') + " Click VIEW ALL POSTS button below!")
        lines.append("")
    else:
        lines.append("")
        lines.append("<blockquote>" + te(e['phone_title'], '📸') + " <b>𝗥𝗘𝗖𝗘𝗡𝗧 𝗣𝗢𝗦𝗧𝗦</b></blockquote>")
        lines.append("")
        lines.append(te(e['status_ok'], '❌') + " No recent posts found")
        lines.append("")

    lines.append(divider)
    lines.append(te(e['credits'], '🧱') + " <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: " + str(credits_left))
    lines.append(divider)

    return chr(10).join(lines), profile_pic, recent_posts

@bot.message_handler(commands=['tgid'])
def tgid_cmd(message):
    if not is_recent_command(message):
        return

    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(chat_id, """❌ Use: /tgid [username or user_id]

📝 Examples:
/tgid BMW_AURA1
/tgid @TATANIUM_ANSH
/tgid 8695946179

🔍 Get Telegram user phone info via username OR user ID
""")
        return

    query = parts[1].strip().replace('@', '')
    if 't.me/' in query:
        query = query.split('t.me/')[-1]

    if not query:
        send_with_premium(chat_id, "❌ Invalid username!")
        return

    if not is_group_chat(message):
        if not deduct_credit(user_id):
            send_with_premium(chat_id, "❌ Insufficient credits!")
            return
    credits_left = _pop_deducted_balance(user_id) if not is_group_chat(message) else "∞ (Group)"

    working, status_msg = check_api_status('tgid')
    if not working:
        _refund_credit(user_id, message)
        send_with_premium(chat_id, f"""
<blockquote>🔍 TELEGRAM USER INFO</blockquote>

<blockquote>⚠️ API IS UNDER MAINTENANCE/FIXING
{status_msg or 'Please try again later'}</blockquote>
""")
        return

    try:
        _bg_chat_action(chat_id, 'typing')
    except:
        pass

    wait = send_searching_animation(chat_id)
    _t0 = time.time()
    result = call_tg_api(query)
    _api_elapsed = round(time.time() - _t0, 2)
    wait._stop_event.set()

    formatted_msg = format_tgid_result(result, query, credits_left, elapsed=_api_elapsed)
    json_file = save_result_to_json("tgid", query, result)

    if json_file:
        sent_msg = send_result_with_json(chat_id, formatted_msg, json_file, wait.message_id)
    else:
        sent_msg = send_result(chat_id, formatted_msg, wait)

    if not sent_msg:
        _refund_credit(user_id, message)   # paid but nothing delivered
        print(f"[TGID] result not delivered uid={user_id} — credit refunded")

    if sent_msg:
        send_random_media(chat_id, sent_msg.message_id)

@bot.message_handler(commands=['num'])
def num_cmd(message):
    if not is_recent_command(message):
        return

    user_id  = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(chat_id,
            "❌ Use: /num [phone_number]\n\n"
            "📝 Examples:\n/num 9876543210\n/num +919876543210\n\n"
            "🔍 Get detailed information about any Indian phone number"
        )
        return

    phone = re.sub(r'[^\d+]', '', parts[1].strip())

    if not validate_phone(phone):
        send_with_premium(chat_id, "❌ Invalid phone number! Use 10-15 digits with optional +")
        return

    if not is_group_chat(message):
        if not deduct_credit(user_id):
            send_with_premium(chat_id, "❌ Insufficient credits!")
            return
    credits_left = _pop_deducted_balance(user_id) if not is_group_chat(message) else "∞ (Group)"

    working, status_msg = check_api_status('num')
    if not working:
        _refund_credit(user_id, message)
        send_with_premium(chat_id, f"<blockquote>📱 PHONE NUMBER INFO</blockquote>\n\n"
                                    f"<blockquote>⚠️ API IS UNDER MAINTENANCE\n{status_msg or 'Try later'}</blockquote>")
        return

    try:
        _bg_chat_action(chat_id, 'typing')
    except Exception:
        pass

    wait = send_searching_animation(chat_id)
    result = call_phone_api(phone)
    wait._stop_event.set()

    pages     = format_number_result(result, phone, credits_left)
    json_file = save_result_to_json("num", phone, result)

    NUM_PAGINATION[user_id] = {"pages": pages, "json_file": json_file, "query": phone}

    first_txt, first_markup = pages[0]

    if len(pages) == 1 and json_file:
        if first_markup is None:
            first_markup = InlineKeyboardMarkup()
        file_id = hashlib.md5(json_file.encode()).hexdigest()[:16]
        JSON_FILES[file_id] = json_file
        first_markup.add(InlineKeyboardButton("Download JSON", callback_data=f"dljson_{file_id}"))

    try:
        bot.delete_message(chat_id, wait.message_id)
    except Exception:
        pass

    sent_msg = send_with_premium(chat_id, first_txt, reply_markup=first_markup)
    if sent_msg:
        schedule_deletion(sent_msg.message_id, chat_id)
        send_random_media(chat_id, sent_msg.message_id)

@bot.message_handler(commands=['adhr'])
def adhr_cmd(message):
    if not is_recent_command(message):
        return

    user_id   = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(message.chat.id,
            "❌ Use: /adhr [AADHAR_NUMBER]\n\n"
            "📝 Examples:\n/adhr 942660008471\n/adhr 393933081942\n\n"
            "🔍 Get detailed Aadhar linked information"
        )
        return

    aadhar = re.sub(r'[^\d]', '', parts[1].strip())

    if not validate_aadhar(aadhar):
        send_with_premium(message.chat.id, "❌ Invalid Aadhar number! Use 12 digits only!")
        return

    if not is_group_chat(message):
        if not deduct_credit(user_id):
            send_with_premium(message.chat.id, "❌ Insufficient credits!")
            return
    credits_left = _pop_deducted_balance(user_id) if not is_group_chat(message) else "∞ (Group)"

    working, status_msg = check_api_status('adhr')
    if not working:
        _refund_credit(user_id, message)
        send_with_premium(message.chat.id,
            f"<blockquote>🪪 AADHAR INFO</blockquote>\n\n"
            f"<blockquote>⚠️ API IS UNDER MAINTENANCE\n{status_msg or 'Please try again later'}</blockquote>"
        )
        return

    try:
        _bg_chat_action(chat_id, 'typing')
    except Exception:
        pass

    wait = send_searching_animation(chat_id)
    result    = call_aadhar_api(aadhar)
    wait._stop_event.set()
    json_file = save_result_to_json("adhr", aadhar, result)
    pages     = format_aadhar_result(result, aadhar, credits_left)

    # store in NUM_PAGINATION so the existing num_page_ callback handles navigation
    NUM_PAGINATION[user_id] = {"pages": pages, "json_file": json_file, "query": aadhar}

    first_txt, first_markup = pages[0]

    if len(pages) == 1 and json_file:
        if first_markup is None:
            first_markup = InlineKeyboardMarkup()
        file_id = hashlib.md5(json_file.encode()).hexdigest()[:16]
        JSON_FILES[file_id] = json_file
        first_markup.add(InlineKeyboardButton("Download JSON", callback_data=f"dljson_{file_id}"))

    try:
        bot.delete_message(chat_id, wait.message_id)
    except Exception:
        pass

    sent_msg = send_with_premium(chat_id, first_txt, reply_markup=first_markup)
    if sent_msg:
        schedule_deletion(sent_msg.message_id, chat_id)
        send_random_media(chat_id, sent_msg.message_id)

@bot.message_handler(commands=['tguser'])
def tguser_cmd(message):
    if not is_recent_command(message):
        return

    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(message.chat.id, """❌ Use: /tguser [username]

📝 Examples:
/tguser BMW_AURA1
/tguser @TATANIUM_ANSH

💡 Get any Telegram user's ID
""")
        return

    username = parts[1].strip()
    username = username.replace('@', '')
    if 't.me/' in username:
        username = username.split('t.me/')[-1]

    if not username:
        send_with_premium(message.chat.id, "❌ Invalid username!")
        return

    if not is_group_chat(message):
        if not deduct_credit(user_id):
            send_with_premium(message.chat.id, "❌ Insufficient credits!")
            return
    credits_left = _pop_deducted_balance(user_id) if not is_group_chat(message) else "∞ (Group)"

    _bg_chat_action(chat_id, 'typing')
    wait = send_searching_animation(chat_id)

    try:
        chat = bot.get_chat(f"@{username}")
        wait._stop_event.set()
        target_user_id = chat.id

        msg = f"""
<blockquote>👤 TELEGRAM USER INFO</blockquote>

<blockquote>🔍 Username: @{username}
🆔 User ID: <code>{target_user_id}</code>
📝 First Name: {chat.first_name or 'N/A'}
📛 Last Name: {chat.last_name or 'N/A'}
👑 Is Bot: {'Yes' if chat.is_bot else 'No'}
📌 Chat Type: {chat.type}</blockquote>

💰 Credits Left: {credits_left}
"""
        json_data = {
            "username": username,
            "user_id": target_user_id,
            "first_name": chat.first_name,
            "last_name": chat.last_name,
            "is_bot": chat.is_bot,
            "chat_type": chat.type
        }
        json_file = save_result_to_json("tguser", username, json_data)

        if json_file:
            sent_msg = send_result_with_json(chat_id, msg, json_file, wait.message_id)
        else:
            sent_msg = send_result(chat_id, msg, wait)

        if sent_msg:
            send_random_media(chat_id, sent_msg.message_id)

    except Exception as e:
        error_msg_text = str(e)
        if "user not found" in error_msg_text.lower():
            error_msg_text = "User not found! Make sure the username exists."

        msg = f"""
<blockquote>👤 TELEGRAM USER INFO</blockquote>

<blockquote>🔍 Username: @{username}
❌ {error_msg_text}</blockquote>

💰 Credits Left: {credits_left}
"""
        sent_msg = send_result(chat_id, msg, wait)
        if sent_msg:
            send_random_media(chat_id, sent_msg.message_id)

# ══════════════════════════════════════════════════════════════════
# SNAPCHAT OSINT — call + format
# ══════════════════════════════════════════════════════════════════

def call_snap_api(username):
    """
    API: (SNAP)username=<username>
    Response: { "success": true, "data": {
        "username", "exists", "is_verified", "has_stories",
        "profile_picture_url", "snapcode_url", "profile_url",
        "description", "story_count", "profile_completeness_score" } }
    """
    username = username.strip().lstrip('@').replace(' ', '_')
    try:
        url = ep("snap", username) or f"(SNAP)username={username}"
        data = _norm_provider("snap", make_api_request(url, timeout=20))
        if isinstance(data, dict):
            if not data.get("success"):
                return {"status": "error", "message": data.get("message", "User not found")}
            inner = data.get("data", data)
            if not inner.get("exists"):
                return {"status": "error", "message": "Snapchat user not found"}
            inner.pop("by", None); inner.pop("owner", None)
            return {"status": "success", "data": inner}
        return {"status": "error", "message": "NO DATA FOUND"}
    except Exception as e:
        return {"status": "error", "message": str(e)}


SNAP_EMOJIS = {
    "header_divider": "5467641505525016018",
    "snap_title":     "6235459831302460476",   # 📸 (ghost-ish)
    "username":       "6122805733936342496",   # 👤
    "verified":       "6129812419028982717",   # ✅
    "status":         "6035239240625820254",   # 🔒
    "story":          "5301276827782755360",   # 📱
    "link":           "6305370152145787193",   # ❔
    "score":          "5197269100878907942",   # ✍️
    "speed":          "6203911118964924015",   # 🚀
    "credits":        "5326049357332513437",   # 🧱
    "bot_icon":       "5355051922862653659",   # 🤖
    "star":           "6118385795976930086",   # 🌟
}


def format_snap_result(result, username, credits_left):
    """Format /snap Snapchat result with premium emoji, blockquote."""
    import time as _time
    e = SNAP_EMOJIS
    div_e = te(e["header_divider"], "➿")
    divider = (div_e * 10) + "\n"
    start_ts = _time.time()

    try: bot_username = "@" + bot.get_me().username
    except Exception: bot_username = "@YourBot"

    def _err(msg_text):
        txt = (
            divider
            + f"{te(e['snap_title'], '👻')}  <b>𝗦𝗡𝗔𝗣𝗖𝗛𝗔𝗧 𝗜𝗡𝗙𝗢</b>  {te(e['snap_title'], '👻')}\n"
            + divider
            + f"\n<blockquote>"
            + f"{te(e['username'], '👤')} <b>Qᴜᴇʀʏ</b>   : <code>@{username}</code>\n"
            + f"{te(e['verified'], '❌')} {msg_text}"
            + f"</blockquote>\n\n"
            + divider
            + f"{te(e['credits'], '🧱')} <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: {credits_left}\n"
            + divider
        )
        return (txt, "")

    if not result or result.get("status") == "error":
        return _err(result.get("message", "NO DATA FOUND") if result else "NO DATA FOUND")

    d = result.get("data", {})
    uname      = d.get("username", username)
    is_ver     = d.get("is_verified", False)
    has_story  = d.get("has_stories", False)
    story_cnt  = d.get("story_count", 0)
    score      = d.get("profile_completeness_score", "N/A")
    profile_url= d.get("profile_url", f"https://www.snapchat.com/add/{uname}")
    snapcode   = d.get("snapcode_url", "")
    pic_url    = d.get("profile_picture_url", d.get("direct_url", ""))
    desc       = d.get("description", "")

    ver_badge  = f"✅ ᴠᴇʀɪꜰɪᴇᴅ" if is_ver else "❌ ɴᴏᴛ ᴠᴇʀɪꜰɪᴇᴅ"
    story_txt  = f"✅ ({story_cnt} ꜱᴛᴏʀɪᴇꜱ)" if has_story else "❌ ɴᴏ ꜱᴛᴏʀɪᴇꜱ"
    elapsed    = round(_time.time() - start_ts, 2)

    txt = (
        divider
        + f"{te(e['snap_title'], '👻')}  <b>𝗦𝗡𝗔𝗣𝗖𝗛𝗔𝗧 𝗜𝗡𝗙𝗢</b>  {te(e['snap_title'], '👻')}\n"
        + divider
        + f"\n<blockquote>"
        + f"{te(e['username'], '👤')} <b>Uꜱᴇʀɴᴀᴍᴇ</b>  : @{uname}\n"
        + f"{te(e['verified'], '✅')} <b>Vᴇʀɪꜰɪᴇᴅ</b>   : {ver_badge}\n"
        + f"{te(e['story'],    '📱')} <b>Sᴛᴏʀɪᴇꜱ</b>    : {story_txt}\n"
        + f"{te(e['score'],    '✍️')} <b>Pʀᴏꜰɪʟᴇ %</b>  : {score}%\n"
        + (f"{te(e['link'],   '❔')} <b>Bɪᴏ</b>        : {desc[:200]}\n" if desc else "")
        + f"</blockquote>\n\n"
        + f"<blockquote>"
        + f"{te(e['link'],    '🔗')} <b>Pʀᴏꜰɪʟᴇ</b>    : <a href='{profile_url}'>ᴏᴩᴇɴ ꜱɴᴀᴩᴄʜᴀᴛ</a>\n"
        + (f"{te(e['link'],   '🔗')} <b>Sɴᴀᴩᴄᴏᴅᴇ</b>   : <a href='{snapcode}'>ꜱᴄᴀɴ ᴄᴏᴅᴇ</a>\n" if snapcode else "")
        + (f"{te(e['link'],   '🖼️')} <b>Pɪᴄ</b>         : <a href='{pic_url}'>ᴠɪᴇᴡ ᴩʜᴏᴛᴏ</a>\n" if pic_url else "")
        + f"</blockquote>\n\n"
        + divider
        + f"{te(e['speed'],   '🚀')} <b>Sᴩᴇᴇᴅ</b>: {elapsed}s\n"
        + f"{te(e['credits'], '🧱')} <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: {credits_left}\n"
        + divider
        + f"{te(e['bot_icon'],'🤖')} <b>Pᴏᴡᴇʀᴇᴅ Bʏ</b>: <b>{bot_username}</b>  {te(e['star'],'🌟')}\n"
        + divider
    )
    return txt, pic_url


# ══════════════════════════════════════════════════════════════════
# FAMILY RESULT FORMATTER — rich blockquote, pagination
# ══════════════════════════════════════════════════════════════════

FAM_EMOJIS = {
    "header_divider": "5467641505525016018",
    "fam_title":      "5386435923204382258",   # 👨‍👩‍👧‍👦
    "id_card":        "5985796637971191405",   # 💳
    "address":        "4958485609464202497",   # 🏡
    "name":           "5425124408786197150",   # 👤
    "relation":       "6129700535130922338",   # 👥
    "scheme":         "5197269100878907942",   # ✍️
    "state":          "5379999674193172777",   # 🔭
    "speed":          "6203911118964924015",   # 🚀
    "credits":        "5326049357332513437",   # 🧱
    "bot_icon":       "5355051922862653659",   # 🤖
    "star":           "6118385795976930086",   # 🌟
    "status_ok":      "6129812419028982717",   # ✅
    "query":          "5379999674193172777",   # 🔭
    "record_badge":   "5249231689695115145",   # 📰
}


def format_family_result(result, query, credits_left):
    """
    Format /family response with premium emoji + blockquote.
    Returns list of (text, markup) tuples for pagination.
    New API: members[], ration_card, scheme, state, district, address, total_members.
    Old API: generic fallback.
    """
    import time as _time
    e = FAM_EMOJIS
    div_e = te(e["header_divider"], "➿")
    divider = (div_e * 10) + "\n"
    start_ts = _time.time()

    try: bot_username = "@" + bot.get_me().username
    except Exception: bot_username = "@YourBot"

    def _f(val):
        v = str(val).strip() if val is not None else ""
        return v if v and v.lower() not in ("n/a", "none", "null", "—", "", "to be captured", "rc0000") else "—"

    def _err(msg_text):
        txt = (
            divider
            + f"{te(e['fam_title'], '👨‍👩‍👧‍👦')}  <b>𝗙𝗔𝗠𝗜𝗟𝗬 𝗗𝗘𝗧𝗔𝗜𝗟𝗦</b>  {te(e['fam_title'], '👨‍👩‍👧‍👦')}\n"
            + divider
            + f"\n<blockquote>"
            + f"{te(e['query'], '🔭')} <b>Qᴜᴇʀʏ</b>   : <code>{query}</code>\n"
            + f"{te(e['status_ok'], '❌')} {msg_text}"
            + f"</blockquote>\n\n"
            + divider
            + f"{te(e['credits'], '🧱')} <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: {credits_left}\n"
            + divider
        )
        return [(txt, None)]

    if not result or result.get("status") == "error":
        return _err(result.get("message", "NO DATA FOUND") if result else "NO DATA FOUND")

    members      = result.get("members", [])
    total_m      = result.get("total_members", len(members))
    ration_card  = _f(result.get("ration_card"))
    scheme       = _f(result.get("scheme"))
    state        = _f(result.get("state"))
    district     = _f(result.get("district"))
    address      = _f(result.get("address"))
    rc_num       = _f(result.get("rc"))
    fps_id       = _f(result.get("fps_id"))
    aadhar_m     = _f(result.get("aadhaar_masked", result.get("aadhaar", query)))
    scheme_name  = _f(result.get("scheme"))
    onorc        = _f(result.get("allowed_onorc"))
    elapsed      = round(_time.time() - start_ts, 2)

    # ── Header info block ──────────────────────────────────────
    header = (
        divider
        + f"{te(e['fam_title'], '👨‍👩‍👧‍👦')}  <b>𝗙𝗔𝗠𝗜𝗟𝗬 𝗗𝗘𝗧𝗔𝗜𝗟𝗦</b>  {te(e['fam_title'], '👨‍👩‍👧‍👦')}\n"
        + divider
        + f"\n<blockquote>"
        + f"{te(e['query'],   '🔭')} <b>Aᴀᴅʜᴀʀ</b>      : <code>{aadhar_m}</code>\n"
        + f"{te(e['status_ok'],'✅')} <b>Sᴛᴀᴛᴜꜱ</b>      : ᴅᴀᴛᴀ ꜰᴏᴜɴᴅ ✅\n"
        + (f"{te(e['id_card'],'💳')} <b>Rᴀᴛɪᴏɴ Cᴀʀᴅ</b>: <code>{ration_card}</code>\n" if ration_card != "—" else "")
        + (f"{te(e['scheme'],'✍️')} <b>Sᴄʜᴇᴍᴇ</b>       : {scheme_name}\n" if scheme_name != "—" else "")
        + (f"{te(e['state'], '🔭')} <b>Sᴛᴀᴛᴇ</b>        : {state}\n" if state != "—" else "")
        + (f"{te(e['state'], '🔭')} <b>Dɪꜱᴛʀɪᴄᴛ</b>     : {district}\n" if district != "—" else "")
        + (f"{te(e['address'],'🏡')} <b>Aᴅᴅʀᴇꜱꜱ</b>     : {address}\n" if address != "—" else "")
        + (f"{te(e['id_card'],'💳')} <b>FPS ID</b>       : <code>{fps_id}</code>\n" if fps_id != "—" else "")
        + (f"{te(e['scheme'],'✍️')} <b>ONORC</b>        : {onorc}\n" if onorc not in ("—","N/A") else "")
        + f"{te(e['record_badge'],'📰')} <b>Mᴇᴍʙᴇʀꜱ</b>    : {total_m}\n"
        + f"</blockquote>\n\n"
    )

    footer = (
        divider
        + f"{te(e['speed'],   '🚀')} <b>Sᴩᴇᴇᴅ</b>: {elapsed}s\n"
        + f"{te(e['credits'], '🧱')} <b>Cʀᴇᴅɪᴛꜱ Lᴇꜰᴛ</b>: {credits_left}\n"
        + divider
        + f"{te(e['bot_icon'],'🤖')} <b>Pᴏᴡᴇʀᴇᴅ Bʏ</b>: <b>{bot_username}</b>  {te(e['star'],'🌟')}\n"
        + divider
    )

    if not members:
        # No member data — use generic format_api_result style
        txt = header + footer
        return [(txt, None)]

    MEMBERS_PER_PAGE = 5
    pages_data = [members[i:i+MEMBERS_PER_PAGE] for i in range(0, len(members), MEMBERS_PER_PAGE)]
    total_pages = len(pages_data)
    out = []

    for page_idx, page_members in enumerate(pages_data):
        page_num  = page_idx + 1
        mem_start = page_idx * MEMBERS_PER_PAGE + 1

        body = ""
        for m_idx, m in enumerate(page_members):
            if not isinstance(m, dict):
                continue
            mem_name = _f(m.get("name"))
            mem_rel  = _f(m.get("relation"))
            mem_id   = _f(m.get("member_id"))
            has_uid  = "✅" if m.get("uid") == "Yes" else "❌"
            abs_num  = mem_start + m_idx
            body += (
                f"<blockquote>"
                + f"{te(e['record_badge'],'📰')} <b>Mᴇᴍʙᴇʀ {abs_num}/{total_m}</b>\n"
                + f"{te(e['name'],  '👤')} <b>Nᴀᴍᴇ</b>     : {mem_name}\n"
                + f"{te(e['relation'],'👥')} <b>Rᴇʟᴀᴛɪᴏɴ</b>: {mem_rel}\n"
                + (f"{te(e['id_card'],'💳')} <b>Mᴇᴍʙᴇʀ ID</b>: <code>{mem_id}</code>\n" if mem_id != "—" else "")
                + f"{te(e['status_ok'],'✅')} <b>Uɪᴅ</b>      : {has_uid}\n"
                + f"</blockquote>\n\n"
            )

        txt = header + body + footer

        markup = None
        if total_pages > 1:
            markup = InlineKeyboardMarkup(row_width=3)
            btns = []
            if page_num > 1:
                btns.append(create_primary_button(
                    "◀ Prev",
                    callback_data=f"num_page_{page_num - 1}_{query}",
                    icon_custom_emoji_id="5246794802560774143"
                ))
            btns.append(create_success_button(
                f"{page_num}/{total_pages}",
                callback_data="num_page_noop",
                icon_custom_emoji_id="5422537279400868395"
            ))
            if page_num < total_pages:
                btns.append(create_danger_button(
                    "Next ▶",
                    callback_data=f"num_page_{page_num + 1}_{query}",
                    icon_custom_emoji_id="6192763368139397161"
                ))
            markup.row(*btns)

        out.append((txt, markup))

    return out if out else _err("NO MEMBERS FOUND")


@bot.message_handler(commands=['leak'])
def leak_cmd(message):
    if not is_recent_command(message):
        return

    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(chat_id,
            "❌ Use: /leak [phone_number]\n\n"
            "📝 Examples:\n/leak 9876543210\n/leak +919876543210\n\n"
            "🔍 Search leaked database by phone number"
        )
        return

    phone = re.sub(r'[^\d+]', '', parts[1].strip())

    if not validate_phone(phone):
        send_with_premium(chat_id, "❌ Invalid phone number! Use 10-15 digits with optional +")
        return

    if not is_group_chat(message):
        if not deduct_credit(user_id):
            send_with_premium(chat_id, "❌ Insufficient credits!")
            return
    credits_left = _pop_deducted_balance(user_id) if not is_group_chat(message) else "∞ (Group)"

    working, status_msg = check_api_status('leak')
    if not working:
        _refund_credit(user_id, message)
        send_with_premium(chat_id,
            f"<blockquote>🔍 LEAK DB LOOKUP</blockquote>\n\n"
            f"<blockquote>⚠️ API IS UNDER MAINTENANCE\n{status_msg or 'Please try again later'}</blockquote>"
        )
        return

    try:
        _bg_chat_action(chat_id, 'typing')
    except Exception:
        pass

    wait = send_searching_animation(chat_id)
    result    = call_leak_api(phone)
    wait._stop_event.set()

    pages     = format_leak_result(result, phone, credits_left)
    json_file = save_result_to_json("leak", phone, result)
    total_pages = len(pages)

    NUM_PAGINATION[user_id] = {"pages": pages, "json_file": json_file, "query": phone}

    first_txt, _ = pages[0]

    first_markup = InlineKeyboardMarkup(row_width=3)
    if total_pages > 1:
        btns = []
        btns.append(create_success_button(
            f"1/{total_pages}",
            callback_data="noop",
            icon_custom_emoji_id="5422537279400868395"
        ))
        btns.append(create_danger_button(
            "Next ▶",
            callback_data=f"leak_page_1_{user_id}",
            icon_custom_emoji_id="6192763368139397161"
        ))
        first_markup.row(*btns)
    elif json_file:
        file_id = hashlib.md5(json_file.encode()).hexdigest()[:16]
        JSON_FILES[file_id] = json_file
        first_markup.add(InlineKeyboardButton("📥 Download JSON", callback_data=f"dljson_{file_id}"))

    try:
        bot.delete_message(chat_id, wait.message_id)
    except Exception:
        pass

    markup_to_send = first_markup if first_markup.keyboard else None
    sent_msg = send_with_premium(chat_id, first_txt, reply_markup=markup_to_send)
    if sent_msg:
        schedule_deletion(sent_msg.message_id, chat_id)
        send_random_media(chat_id, sent_msg.message_id)

# ---------- Contact-verification gate (drop-in) ---------------
# Matches the interface expected by send_contact_verification_prompt.
CAPTCHA_EMOJI = {
    # All IDs pulled from existing maps already in this file — no new IDs added.
    "robot":    "5355051922862653659",   # 🤖  NUM_EMOJIS["bot_icon"]
    "shield":   "6300604035527346062",   # 🛡  VECH_EMOJIS["ins_status"]
    "phone":    "6147464060305676048",   # 📱  EMOJI_TO_PREMIUM["📱"]
    "check":    "6129812419028982717",   # ✅  NUM_EMOJIS["status_ok"]
    "cross":    "5296491800423340716",   # ❌  EMOJI_TO_PREMIUM["❌"]
    "warning":  "4956420859771225351",   # ⚠️  EMOJI_TO_PREMIUM["⚠"]
    "spark":    "5359588280205605798",   # ⚡  VECH_EMOJIS["fuel"]
    "party":    "4956560549287560231",   # 🎉  EMOJI_TO_PREMIUM["🎉"]
    "calendar": "5348227245599105972",   # 📅  INSTA_EMOJIS["joined"]
}


def _cv_pe(name, fallback):
    """Premium emoji tag, single-quote safe for HTML."""
    eid = CAPTCHA_EMOJI.get(name)
    if not eid:
        return fallback
    return f'<tg-emoji emoji-id="{eid}">{fallback}</tg-emoji>'


def _cv_delete(chat_id, message_id):
    if not message_id:
        return
    try:
        bot.delete_message(chat_id, message_id)
    except Exception as exc:
        if not any(w in str(exc).lower() for w in
                   ("not found", "message to delete", "can't be deleted", "forbidden")):
            print(f"[CV_DELETE] {chat_id}/{message_id}: {exc}")


def _cv_delete_many(chat_id, message_ids):
    unique = []
    for mid in (message_ids or []):
        if mid and mid not in unique:
            unique.append(mid)
    if not unique:
        return
    try:
        bot.delete_messages(chat_id, unique)
        return
    except Exception:
        pass
    for mid in unique:
        _cv_delete(chat_id, mid)


def _cv_prompt_text():
    return (
        "<blockquote>"
        f"{_cv_pe('robot', '🤖')} <b>ᴠᴇʀɪꜰʏ ʏᴏᴜʀ ᴄᴏɴᴛᴀᴄᴛ</b>\n\n"
        f"{_cv_pe('shield', '🛡️')} Bot continue karne ke liye neeche button se "
        "<b>apna khud ka Telegram contact</b> share karo.\n\n"
        f"{_cv_pe('phone', '📱')} Sirf aapka contact verification ke liye use hoga."
        "</blockquote>"
    )


def send_contact_verification_prompt(uid, ref=None):
    """Show the verification prompt and track message_id for cleanup."""
    if ref:
        _save_pending_ref(uid, ref)

    keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True, one_time_keyboard=True)
    keyboard.add(
        _KB(
            "📱 ᴛᴀᴘ ᴛᴏ ꜱʜᴀʀᴇ ᴄᴏɴᴛᴀᴄᴛ",
            style="success",
            icon_custom_emoji_id=CAPTCHA_EMOJI["phone"],
            request_contact=True,
        )
    )
    try:
        sent = send_with_premium(uid, _cv_prompt_text(), reply_markup=keyboard)
        if sent and getattr(sent, "message_id", None):
            _LAST_CAPCHA_MESSAGE[uid] = sent.message_id
        return sent
    except Exception as exc:
        print(f"[CV_PROMPT] {exc}")
        return None


@bot.message_handler(content_types=["contact"])
def h_contact_verify(msg):
    """Accept user's own Telegram contact — verify and clean old gate cards."""
    try:
        if msg.chat.type != "private" or not msg.contact:
            return

        uid = msg.from_user.id
        contact_uid = getattr(msg.contact, "user_id", None)

        # Reject forwarded / someone-else's contact
        if contact_uid != uid:   # missing user_id = not the user's own contact
            bot.reply_to(
                msg,
                (
                    "<blockquote>"
                    f"{_cv_pe('cross', '❌')} <b>Invalid contact</b>\n"
                    "Please apna khud ka Telegram contact share karo."
                    "</blockquote>"
                ),
                parse_mode="HTML",
            )
            return

        phone = (getattr(msg.contact, "phone_number", None) or "").strip()
        if not phone:
            bot.reply_to(
                msg,
                (
                    "<blockquote>"
                    f"{_cv_pe('warning', '⚠️')} Contact number nahi mila. "
                    "Dobara button tap karke share karo."
                    "</blockquote>"
                ),
                parse_mode="HTML",
            )
            return

        # Persist verification — single clean save, upsert=True inside
        try:
            _mark_contact_verified(uid, phone)
        except Exception as exc:
            print(f"[CV_SAVE] {exc}")

        # Remove reply keyboard silently
        try:
            clr = bot.send_message(
                uid, "\u2060",
                reply_markup=types.ReplyKeyboardRemove(),
            )
            _cv_delete(uid, getattr(clr, "message_id", None))
        except Exception as exc:
            print(f"[CV_KB_REMOVE] {exc}")

        # Restore pending command or referral
        pending = _PENDING_REF.pop(uid, None)
        if isinstance(pending, int):
            # It was a referral id saved by start_cmd gate
            msg.text = f"/start ref_{pending}"
            try:
                start_cmd(msg)
            except Exception as exc:
                print(f"[CV_RESTART_START] {exc}")
        elif isinstance(pending, str) and pending.startswith("/") and not pending.startswith("/start"):
            # It was a real command they tried — re-dispatch it
            msg.text = pending
            try:
                bot.process_new_messages([msg])
            except Exception as exc:
                print(f"[CV_RESTART_CMD] {exc}")
                # Fallback: just open start
                msg.text = "/start"
                try: start_cmd(msg)
                except Exception: pass
        else:
            # Default: open start
            msg.text = "/start"
            try:
                start_cmd(msg)
            except Exception as exc:
                print(f"[CV_RESTART] {exc}")

        # Cleanup old gate messages
        cleanup_ids = []
        old_fj  = _LAST_FJ_MESSAGE.pop(uid, None)
        old_cap = _LAST_CAPCHA_MESSAGE.pop(uid, None)
        if old_fj:
            cleanup_ids.append(old_fj)
        if old_cap:
            cleanup_ids.append(old_cap)
        cleanup_ids.append(getattr(msg, "message_id", None))
        _cv_delete_many(uid, cleanup_ids)

    except Exception as exc:
        print(f"[CONTACT_VERIFY] {exc}")


# ============================================================
# MULTI-BOT CLONE MANAGER — one Render service, isolated bots
# ============================================================
CLONE_INSTANCE = os.environ.get("SHOWN_CLONE_INSTANCE") == "1"
CLONE_MANAGER_DB = os.environ.get("CLONE_MANAGER_DB") or (
    "/var/data/clone_manager.sqlite3" if os.path.isdir("/var/data")
    else os.path.abspath("clone_manager.sqlite3")
)
CLONE_RUNTIME_DIR = os.environ.get("CLONE_RUNTIME_DIR") or (
    "/var/data/clones" if os.path.isdir("/var/data") else os.path.abspath("clones")
)
os.makedirs(CLONE_RUNTIME_DIR, exist_ok=True)
_clone_lock = threading.RLock()
_clone_processes = {}

def _clone_db():
    conn = sqlite3.connect(CLONE_MANAGER_DB, timeout=20)
    conn.row_factory = sqlite3.Row
    conn.execute("""CREATE TABLE IF NOT EXISTS clones (
        clone_id INTEGER PRIMARY KEY AUTOINCREMENT,
        bot_username TEXT NOT NULL,
        bot_name TEXT NOT NULL,
        token_cipher TEXT NOT NULL,
        enabled INTEGER NOT NULL DEFAULT 1,
        created_at TEXT NOT NULL,
        last_error TEXT DEFAULT ''
    )""")
    conn.commit()
    return conn

def _clone_fernet():
    key, _source = _security_key_get("clone")
    if not key:
        raise RuntimeError("Set CLONE_TOKEN_ENCRYPTION_KEY in Render before adding clones.")
    try:
        from cryptography.fernet import Fernet
        return Fernet(key.encode("ascii"))
    except Exception as exc:
        raise RuntimeError("Invalid encryption key or cryptography dependency missing.") from exc

def _clone_encrypt(token):
    return _clone_fernet().encrypt(token.encode("utf-8")).decode("ascii")

def _clone_decrypt(cipher):
    return _clone_fernet().decrypt(cipher.encode("ascii")).decode("utf-8")

def _clone_verify_token(token):
    response = requests.get(
        "https://api.telegram.org/bot" + token + "/getMe", timeout=12
    )
    data = response.json()
    if not response.ok or not data.get("ok") or not data.get("result", {}).get("is_bot"):
        raise ValueError("Telegram rejected this bot token. Check it with BotFather.")
    return data["result"]

def _clone_rows():
    with _clone_db() as conn:
        return [dict(row) for row in conn.execute(
            "SELECT clone_id,bot_username,bot_name,enabled,created_at,last_error FROM clones ORDER BY clone_id"
        )]

def _clone_start(clone_id):
    with _clone_lock:
        rows = _clone_rows()
        row = next((x for x in rows if int(x["clone_id"]) == int(clone_id)), None)
        if not row:
            raise ValueError("Clone not found.")
        proc = _clone_processes.get(int(clone_id))
        if proc and proc.poll() is None:
            return "already running"
        with _clone_db() as conn:
            full = conn.execute("SELECT token_cipher FROM clones WHERE clone_id=?", (clone_id,)).fetchone()
        token = _clone_decrypt(full["token_cipher"])
        db_path = os.path.join(CLONE_RUNTIME_DIR, f"clone_{int(clone_id)}.sqlite3")
        env = os.environ.copy()
        env["BOT_TOKEN"] = token
        env["TG_STORE_DB_PATH"] = db_path
        env["SHOWN_CLONE_INSTANCE"] = "1"
        env["CLONE_MANAGER_DB"] = CLONE_MANAGER_DB
        env["CLONE_RUNTIME_DIR"] = CLONE_RUNTIME_DIR
        script = os.path.abspath(__file__)
        log_path = os.path.join(CLONE_RUNTIME_DIR, f"clone_{int(clone_id)}.log")
        log_handle = open(log_path, "a", encoding="utf-8")
        try:
            proc = subprocess.Popen(
                [sys.executable, script], env=env,
                cwd=os.path.dirname(script) or None,
                stdout=log_handle, stderr=subprocess.STDOUT,
                start_new_session=True
            )
        finally:
            log_handle.close()
        _clone_processes[int(clone_id)] = proc
        with _clone_db() as conn:
            conn.execute("UPDATE clones SET enabled=1,last_error='' WHERE clone_id=?", (clone_id,))
        return f"started (PID {proc.pid})"

def _clone_stop(clone_id):
    with _clone_lock:
        proc = _clone_processes.get(int(clone_id))
        if not proc or proc.poll() is not None:
            with _clone_db() as conn:
                conn.execute("UPDATE clones SET enabled=0 WHERE clone_id=?", (clone_id,))
            return "already stopped"
        proc.terminate()
        try:
            proc.wait(timeout=8)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait(timeout=3)
        _clone_processes.pop(int(clone_id), None)
        with _clone_db() as conn:
            conn.execute("UPDATE clones SET enabled=0 WHERE clone_id=?", (clone_id,))
        return "stopped"

def _clone_add_token(token):
    token = token.strip()
    if len(token) > 256 or not re.fullmatch(r"\d{5,}:[A-Za-z0-9_-]{20,}", token):
        raise ValueError("Token format is invalid.")
    info = _clone_verify_token(token)
    cipher = _clone_encrypt(token)
    with _clone_db() as conn:
        existing = conn.execute("SELECT clone_id FROM clones WHERE bot_username=?", (info["username"],)).fetchone()
        if existing:
            raise ValueError("This bot is already registered.")
        cur = conn.execute(
            "INSERT INTO clones(bot_username,bot_name,token_cipher,enabled,created_at) VALUES(?,?,?,?,?)",
            (info["username"], info.get("first_name") or info["username"], cipher, 1,
             datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
        )
        clone_id = cur.lastrowid
    status = _clone_start(clone_id)
    return clone_id, info, status

def _clone_autostart():
    if CLONE_INSTANCE:
        return
    try:
        with _clone_db() as conn:
            ids = [int(r[0]) for r in conn.execute("SELECT clone_id FROM clones WHERE enabled=1")]
        for clone_id in ids:
            try:
                _clone_start(clone_id)
            except Exception as exc:
                with _clone_db() as conn:
                    conn.execute("UPDATE clones SET last_error=? WHERE clone_id=?", (str(exc)[:500], clone_id))
                print(f"[CLONE_MANAGER] auto-start {clone_id} failed: {exc}")
    except Exception as exc:
        print(f"[CLONE_MANAGER] auto-start unavailable: {exc}")

def _clone_manager_keyboard():
    kb = InlineKeyboardMarkup(row_width=2)
    kb.add(
        InlineKeyboardButton("➕ Add Clone", callback_data="clone_add", style="success"),
        InlineKeyboardButton("📋 List Clones", callback_data="clone_list", style="primary")
    )
    kb.add(InlineKeyboardButton("⬅️ Back to Admin", callback_data="admin_panel", style="primary"))
    return kb

def _clone_list_markup(rows):
    kb = InlineKeyboardMarkup(row_width=2)
    for row in rows:
        cid = int(row["clone_id"])
        state = "🟢" if row["enabled"] else "🔴"
        kb.row(
            InlineKeyboardButton(f"{state} @{row['bot_username']}", callback_data=f"clone_info:{cid}", style="primary"),
            InlineKeyboardButton("⏹ Stop" if row["enabled"] else "▶️ Start",
                                 callback_data=f"clone_toggle:{cid}", style="danger" if row["enabled"] else "success")
        )
    kb.add(InlineKeyboardButton("➕ Add Clone", callback_data="clone_add", style="success"))
    kb.add(InlineKeyboardButton("⬅️ Back", callback_data="clone_home", style="primary"))
    return kb

def _clone_summary():
    rows = _clone_rows()
    if not rows:
        return "🤖 <b>BOT CLONE MANAGER</b>\nNo clones registered yet."
    lines = ["🤖 <b>BOT CLONE MANAGER</b>", f"Registered bots: <code>{len(rows)}</code>", ""]
    for row in rows:
        lines.append(f"{'🟢' if row['enabled'] else '🔴'} <b>#{row['clone_id']} @{_html.escape(row['bot_username'])}</b>")
        if row.get("last_error"):
            lines.append(f"   ⚠️ {_html.escape(row['last_error'][:120])}")
    return "\n".join(lines)



# ============================================================
# SECURITY KEY STATUS — verify host-provided secrets without
# ever displaying their values in Telegram.
# ============================================================
def _security_key_status(kind):
    from cryptography.fernet import Fernet
    raw, source = _security_key_get(kind)
    name = "API_CONFIG_ENCRYPTION_KEY" if kind == "api" else "CLONE_TOKEN_ENCRYPTION_KEY"
    if not raw:
        return name, False, "Missing"
    if kind == "api":
        import base64, hashlib
        cipher = Fernet(base64.urlsafe_b64encode(hashlib.sha256(raw.encode("utf-8")).digest()))
    elif kind == "clone":
        cipher = Fernet(raw.encode("ascii"))
    else:
        raise ValueError("Unknown key type")
    probe = b"shown-legacy-key-check"
    if cipher.decrypt(cipher.encrypt(probe)) != probe:
        return name, False, "Encryption test failed"
    return name, True, f"Configured · valid · {source}"

def _security_keys_text():
    rows = []
    for kind, label in (("api", "API encryption"), ("clone", "Clone token encryption")):
        try:
            name, ok, detail = _security_key_status(kind)
            rows.append(f"{'✅' if ok else '❌'} <b>{label}</b>\n<code>{name}</code> — {_html.escape(detail)}")
        except Exception as exc:
            rows.append(f"❌ <b>{label}</b> — {_html.escape(str(exc)[:150])}")
    return "🔐 <b>SECURITY &amp; ENCRYPTION</b>\n\n" + "\n\n".join(rows) + (
        "\n\n<i>Secret values are never displayed. Disk-managed keys are stored with restricted file permissions on the persistent disk.</i>"
    )

def _security_keys_keyboard():
    kb = InlineKeyboardMarkup(row_width=2)
    kb.row(create_primary_button("🔑 Add / Update API Key", callback_data="keycheck_set_api"),
           create_success_button("🤖 Add / Update Clone Key", callback_data="keycheck_set_clone"))
    kb.row(create_danger_button("🗑 Remove API Key", callback_data="keycheck_remove_api"),
           create_danger_button("🗑 Remove Clone Key", callback_data="keycheck_remove_clone"))
    kb.row(create_primary_button("🔑 Verify API Key", callback_data="keycheck_api"),
           create_success_button("🤖 Verify Clone Key", callback_data="keycheck_clone"))
    kb.add(create_primary_button("🔄 Refresh Status", callback_data="keycheck_all"))
    kb.add(create_primary_button("⬅️ Back to Admin", callback_data="keycheck_back"))
    return kb



# ============================================================
# ADMIN SUITE: monitoring, backup history, audit, broadcast,
# customization. All actions are master-admin/private-chat only.
# ============================================================
_ADMIN_SUITE_START = time.time()

def _admin_audit(action, admin_id, detail=""):
    try:
        with _clone_db() as conn:
            conn.execute("""CREATE TABLE IF NOT EXISTS admin_activity (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                admin_id INTEGER NOT NULL,
                action TEXT NOT NULL,
                detail TEXT NOT NULL DEFAULT '',
                created_at TEXT NOT NULL
            )""")
            conn.execute(
                "INSERT INTO admin_activity(admin_id,action,detail,created_at) VALUES(?,?,?,?)",
                (int(admin_id), str(action)[:100], str(detail)[:500],
                 datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
            )
            conn.execute("DELETE FROM admin_activity WHERE id NOT IN "
                         "(SELECT id FROM admin_activity ORDER BY id DESC LIMIT 500)")
    except Exception as exc:
        print(f"[ADMIN_AUDIT] {exc}")

def _admin_audit_recent(limit=20):
    try:
        with _clone_db() as conn:
            conn.execute("""CREATE TABLE IF NOT EXISTS admin_activity (
                id INTEGER PRIMARY KEY AUTOINCREMENT, admin_id INTEGER NOT NULL,
                action TEXT NOT NULL, detail TEXT NOT NULL DEFAULT '', created_at TEXT NOT NULL)""")
            return [dict(x) for x in conn.execute(
                "SELECT * FROM admin_activity ORDER BY id DESC LIMIT ?", (int(limit),))]
    except Exception:
        return []

def _admin_monitor_text():
    uptime = datetime.now() - BOT_START_TIME
    try:
        import psutil
        cpu = psutil.cpu_percent(interval=0.25)
        ram = psutil.Process(os.getpid()).memory_info().rss / (1024 * 1024)
        total_ram = psutil.virtual_memory().total / (1024 * 1024)
        resource = f"CPU: <code>{cpu:.1f}%</code>\nRAM: <code>{ram:.1f} MB / {total_ram:.0f} MB</code>"
    except Exception:
        try:
            with open("/proc/self/statm", "r", encoding="utf-8") as f:
                pages = int(f.read().split()[1])
            ram = pages * os.sysconf("SC_PAGE_SIZE") / (1024 * 1024)
            resource = f"RAM: <code>{ram:.1f} MB</code>\nCPU: <i>psutil not installed</i>"
        except Exception:
            resource = "CPU/RAM: <i>not available on this host</i>"
    rows = _clone_rows() if not CLONE_INSTANCE else []
    clone_lines = []
    for row in rows[:20]:
        proc = _clone_processes.get(int(row["clone_id"]))
        alive = bool(proc and proc.poll() is None)
        clone_lines.append(f"{'🟢' if alive else '🔴'} @{_html.escape(row['bot_username'])} · {'running' if alive else 'stopped'}")
    if not clone_lines:
        clone_lines = ["<i>No registered clones or this is a clone instance.</i>"]
    return ("<blockquote><b>📡 LIVE BOT MONITOR</b>\n"
            f"Master: <b>{'clone instance' if CLONE_INSTANCE else 'running'}</b>\n"
            f"Uptime: <code>{str(uptime).split('.')[0]}</code>\n{resource}\n"
            f"Process ID: <code>{os.getpid()}</code>\n"
            f"Error count (recent process logs): <i>not instrumented</i>\n\n"
            "<b>CLONES</b>\n" + "\n".join(clone_lines) + "</blockquote>")

def _admin_backup_history():
    cfg = _col_media_set.find_one({"setting_key": "advanced_backup_history"}) or {}
    return list(cfg.get("items") or [])[-10:][::-1]

def _admin_backup_now(chat_id, admin_id):
    fd, path = tempfile.mkstemp(prefix="shownlegacy_manual_", suffix=".sqlite3")
    os.close(fd)
    try:
        dest = sqlite3.connect(path)
        try:
            with _store._lock:
                _store._conn.backup(dest)
        finally:
            dest.close()
        stamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        backup_cfg = _col_media_set.find_one({"setting_key": "auto_backup_config"}) or {}
        destination = backup_cfg.get("chat_id") or chat_id
        with open(path, "rb") as fh:
            sent = bot.send_document(int(destination), fh,
                caption=f"💾 Shown Legacy manual backup · {stamp}")
        history = _admin_backup_history()
        history.append({"date": stamp, "file_id": sent.document.file_id,
                        "file_name": sent.document.file_name or "backup.sqlite3",
                        "size": sent.document.file_size or os.path.getsize(path)})
        _col_media_set.update_one({"setting_key": "advanced_backup_history"},
            {"$set": {"items": history[-50:], "last_backup": stamp, "updated_by": admin_id}}, upsert=True)
        _admin_audit("manual_backup", admin_id, stamp)
        return True
    finally:
        try: os.remove(path)
        except OSError: pass

def _admin_backup_manager_text():
    cfg = _col_media_set.find_one({"setting_key": "auto_backup_config"}) or {}
    history = _admin_backup_history()
    lines = ["<blockquote><b>💾 ADVANCED BACKUP MANAGER</b>",
             f"Automatic backup: <b>{'ON' if cfg.get('enabled') else 'OFF'}</b>",
             f"Destination: <code>{cfg.get('chat_id') or 'not configured'}</code>",
             f"Last automatic backup: <code>{cfg.get('last_backup') or 'none'}</code>",
             f"Last error: <code>{_html.escape(str(cfg.get('last_error') or 'none')[:160])}</code>",
             "", "<b>Recent manual backups</b>"]
    if history:
        for item in history[-10:][::-1]:
            lines.append(f"• { _html.escape(str(item.get('date','unknown'))) } · {int(item.get('size',0))//1024} KB")
    else:
        lines.append("No manual backups recorded yet.")
    lines.append("</blockquote>")
    return "\n".join(lines)

def _admin_customization_text():
    welcome = _col_media_set.find_one({"setting_key": "welcome_config"}) or {}
    editable = _col_media_set.find_one({"setting_key": "editable_bot_texts"}) or {}
    return ("<blockquote><b>🎨 CUSTOMIZATION STUDIO</b>\n"
            f"Welcome mode: <code>{_html.escape(str(welcome.get('mode','default')))}</code>\n"
            f"Help text: <code>{'custom' if editable.get('help_text') else 'default'}</code>\n"
            f"Lookup guide: <code>{'custom' if editable.get('lookup_guide') else 'default'}</code>\n"
            f"Support text: <code>{'custom' if editable.get('support_text') else 'default'}</code>\n\n"
            "Use the controls below to edit existing text and welcome settings. Keyboard layout and button colours remain code-managed.</blockquote>")

def _admin_suite_keyboard(section):
    kb = InlineKeyboardMarkup(row_width=2)
    if section == "monitor":
        kb.add(InlineKeyboardButton("🔄 Refresh", callback_data="suite_monitor", style="primary"))
    elif section == "backup":
        kb.add(InlineKeyboardButton("📸 Backup Now", callback_data="suite_backup_now", style="success"),
               InlineKeyboardButton("📜 Backup History", callback_data="suite_backup_history", style="primary"))
        kb.add(InlineKeyboardButton("⚙️ Auto Backup Settings", callback_data="admin_backup", style="primary"))
        kb.add(InlineKeyboardButton("♻️ Restore Instructions", callback_data="suite_restore_info", style="danger"))
    elif section == "activity":
        kb.add(InlineKeyboardButton("🔄 Refresh Logs", callback_data="suite_activity", style="primary"))
    elif section == "broadcast":
        kb.add(InlineKeyboardButton("👥 All Users", callback_data="suite_bc_all", style="primary"),
               InlineKeyboardButton("🟢 Active 30 Days", callback_data="suite_bc_active", style="success"))
        kb.add(InlineKeyboardButton("🤖 All Clones", callback_data="suite_bc_clones", style="primary"))
    elif section == "custom":
        kb.add(InlineKeyboardButton("👋 Welcome Text", callback_data="admin_welcome_text", style="success"))
        kb.add(InlineKeyboardButton("📝 Edit Help", callback_data="admin_edit_help", style="primary"))
        kb.add(InlineKeyboardButton("📘 Edit Lookup Guide", callback_data="admin_edit_lookup_guide", style="primary"))
        kb.add(InlineKeyboardButton("☎️ Edit Support", callback_data="admin_edit_support_text", style="primary"))
        kb.add(InlineKeyboardButton("🎬 Welcome Media", callback_data="admin_welcome_manager", style="primary"))
    kb.add(InlineKeyboardButton("⬅️ Back to Admin", callback_data="admin_panel", style="primary"))
    return kb


# Every top-level Admin Panel action is also available as a normal reply-keyboard
# button. Nested choices (for example welcome text/photo/video) remain inline inside
# their respective submenu so the persistent keyboard does not become unmanageably large.
_ADMIN_REPLY_ROWS = [
    [("📊 Admin Stats", "admin_stats", "primary"), ("📆 Daily Users", "admin_dau", "success")],
    [("🤖 Clone Manager", "admin_clone_manager", "success")],
    [("📡 Live Monitoring", "admin_live_monitor", "success"), ("💾 Backup Manager", "admin_backup_manager", "primary")],
    [("🖥️ Server & System", "admin_system_manager", "success")],
    [("🧾 Admin Activity", "admin_activity_logs", "primary"), ("📢 Broadcast Manager", "admin_broadcast_manager", "success")],
    [("🎨 Customization Studio", "admin_customization", "primary")],
    [("🔐 Security & Keys", "admin_security_keys", "primary")],
    [("🛡️ Admin Roles", "admin_security_roles", "danger")],
    [("👥 User Manager", "admin_users", "primary"), ("🧾 User History", "admin_user_history", "primary")],
    [("🔌 API Manager", "admin_api_manager", "primary"), ("📦 Total APIs", "admin_total_apis", "primary")],
    [("🔧 API Status", "admin_api_status", "primary"), ("🧪 Test API", "admin_api_test", "success")],
    [("🖼 Media Manager", "admin_addmedia", "primary"), ("💾 Auto Backup", "admin_backup", "success")],
    [("👋 Welcome Manager", "admin_welcome_manager", "success"), ("🎬 Welcome Video", "admin_welcome_video", "success")],
    [("➕ Add Credits", "admin_addcredits", "success"), ("🎁 Add Credits to All", "admin_add_all_credits", "success")],
    [("➖ Remove Credits", "admin_removecredits", "danger"), ("🚫 Block User", "admin_block", "danger")],
    [("✅ Unblock User", "admin_unblock", "success"), ("👑 Make Admin", "admin_makeadmin", "primary")],
    [("🗑 Remove Admin", "admin_removeadmin", "danger"), ("📢 Broadcast", "admin_broadcast_info", "primary")],
    [("📡 BC Channel", "admin_setbc_info", "primary"), ("📝 Edit Help Text", "admin_edit_help", "success")],
    [("📘 Edit Lookup Guide", "admin_edit_lookup_guide", "primary"), ("☎️ Edit Support Text", "admin_edit_support_text", "primary")],
    [("♻️ Reset Editable Text", "admin_reset_editable_text", "danger"), ("🗂 All Commands", "acmd_all", "primary")],
    [("🔄 Reload Bot", "admin_reload", "danger"), ("⬅️ User Menu", "admin_user_menu", "primary")],
]

def _admin_small_caps(value):
    """Convert Latin letters to readable Unicode small-cap glyphs for Telegram buttons."""
    normal = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
    small = (
        "ABCDEFGHIJKLMNOPQRSTUVWXYZ"  # uppercase glyphs remain standard
        "ᴀʙᴄᴅᴇꜰɢʜɪᴊᴋʟᴍɴᴏᴘǫʀꜱᴛᴜᴠᴡxʏᴢ"
    )
    return str(value).translate(str.maketrans(normal, small))

_ADMIN_REPLY_PAGE_SIZE = 6  # six two-button rows per page

_ADMIN_REPLY_LABEL_TO_ACTION = {
    label: action
    for row in _ADMIN_REPLY_ROWS for label, action, _style in row
}
_ADMIN_REPLY_LABEL_TO_ACTION["👤 User Menu"] = "admin_user_menu"
for _plain_label, _target_action in list(_ADMIN_REPLY_LABEL_TO_ACTION.items()):
    _ADMIN_REPLY_LABEL_TO_ACTION[_admin_small_caps(_plain_label)] = _target_action
for _admin_page_no in range(1, (len(_ADMIN_REPLY_ROWS) + _ADMIN_REPLY_PAGE_SIZE - 1) // _ADMIN_REPLY_PAGE_SIZE + 1):
    _ADMIN_REPLY_LABEL_TO_ACTION[f"➡️ Admin Page {_admin_page_no + 1}"] = f"admin_page_{_admin_page_no}"
    _ADMIN_REPLY_LABEL_TO_ACTION[_admin_small_caps(f"➡️ Admin Page {_admin_page_no + 1}")] = f"admin_page_{_admin_page_no}"
    _ADMIN_REPLY_LABEL_TO_ACTION[f"⬅️ Admin Page {_admin_page_no}"] = f"admin_page_{_admin_page_no - 1}"
    _ADMIN_REPLY_LABEL_TO_ACTION[_admin_small_caps(f"⬅️ Admin Page {_admin_page_no}")] = f"admin_page_{_admin_page_no - 1}"


def _admin_reply_keyboard(page=0):
    """Show admin actions on a separate, paginated reply-keyboard page."""
    page_count = max(1, (len(_ADMIN_REPLY_ROWS) + _ADMIN_REPLY_PAGE_SIZE - 1) // _ADMIN_REPLY_PAGE_SIZE)
    page = max(0, min(int(page), page_count - 1))
    kb = types.ReplyKeyboardMarkup(row_width=2, resize_keyboard=True, one_time_keyboard=False)
    start = page * _ADMIN_REPLY_PAGE_SIZE
    for row in _ADMIN_REPLY_ROWS[start:start + _ADMIN_REPLY_PAGE_SIZE]:
        kb.row(*[_KB(_admin_small_caps(label), style=style) for label, _action, style in row])
    nav = []
    if page > 0:
        nav.append(_KB(_admin_small_caps(f"⬅️ Admin Page {page}"), style="primary"))
    if page < page_count - 1:
        nav.append(_KB(_admin_small_caps(f"➡️ Admin Page {page + 2}"), style="primary"))
    if nav:
        kb.row(*nav)
    kb.row(_KB(_admin_small_caps("👤 User Menu"), style="primary"))
    return kb


def _show_admin_reply_page(chat_id, page=0):
    page_count = max(1, (len(_ADMIN_REPLY_ROWS) + _ADMIN_REPLY_PAGE_SIZE - 1) // _ADMIN_REPLY_PAGE_SIZE)
    page = max(0, min(int(page), page_count - 1))
    send_with_premium(
        chat_id,
        f"🛠 <b>ADMIN PANEL — PAGE {page + 1}/{page_count}</b>\nChoose an admin feature from the keyboard below.",
        parse_mode="HTML",
        reply_markup=_admin_reply_keyboard(page),
    )


def _private_main_menu_keyboard(admin_user=False):
    """Private-only user/admin reply keyboard; every section has an API 9.4 colour."""
    kb = types.ReplyKeyboardMarkup(row_width=2, resize_keyboard=True, one_time_keyboard=False)
    rows = [
        [("📱 ɴᴜᴍʙᴇʀ ʟᴏᴏᴋᴜᴘ", "primary"), ("👤 ᴛᴇʟᴇɢʀᴀᴍ ᴜsᴇʀ", "primary")],
        [("🆔 ᴍʏ ᴛᴇʟᴇɢʀᴀᴍ ɪᴅ", "success"), ("📸 ɪɴsᴛᴀɢʀᴀᴍ ʟᴏᴏᴋᴜᴘ", "primary")],
        [("🐙 ɢɪᴛʜᴜʙ ʟᴏᴏᴋᴜᴘ", "primary"), ("🎮 ғʀᴇᴇ ғɪʀᴇ ʟᴏᴏᴋᴜᴘ", "primary")],
        [("🎯 ʙɢᴍɪ ʟᴏᴏᴋᴜᴘ", "primary"), ("🌐 ɪᴘ ʟᴏᴏᴋᴜᴘ", "primary")],
        [("🔗 ᴅᴏᴍᴀɪɴ ʟᴏᴏᴋᴜᴘ", "primary"), ("📮 ᴘɪɴ ᴄᴏᴅᴇ ʟᴏᴏᴋᴜᴘ", "primary")],
        [("📧 ᴇᴍᴀɪʟ ʟᴏᴏᴋᴜᴘ", "primary"), ("🔎 ᴏsɪɴᴛ ʟᴏᴏᴋᴜᴘ", "primary")],
        [("🪪 ɪᴅ ᴠᴇʀɪғɪᴄᴀᴛɪᴏɴ ɢᴜɪᴅᴇ", "success")],
        [("👤 ᴍʏ ᴘʀᴏғɪʟᴇ", "success"), ("💰 ʙᴀʟᴀɴᴄᴇ", "success")],
        [("🎁 ʀᴇғᴇʀ & ᴇᴀʀɴ", "success"), ("🎟 ʀᴇᴅᴇᴇᴍ ᴄᴏᴅᴇ", "success")],
        [("❔ ʜᴇʟᴘ / ᴄᴏᴍᴍᴀɴᴅs", "primary")],
        [("🌟 ᴜsᴇʀ ʜᴜʙ", "success")],
    ]
    if admin_user:
        # Admin features are shown only after tapping Admin Panel.
        rows.append([("🛠 ᴀᴅᴍɪɴ ᴘᴀɴᴇʟ", "primary")])
    for row in rows:
        kb.row(*[_KB(label, style=style) for label, style in row])
    return kb


@bot.message_handler(commands=['start'])
def start_cmd(message):
    if not is_recent_command(message):
        return

    user_id = message.from_user.id
    chat_id = message.chat.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(chat_id, error_msg)
        return

    username = message.from_user.username or "N/A"
    first_name = message.from_user.first_name or "User"
    _save_pending_ref(user_id, extract_referral(message.text))
    if not enforce_force_join(message):
        return
    if not is_admin(user_id) and not _is_contact_verified(user_id):
        _save_pending_ref(user_id, extract_referral(message.text))
        send_contact_verification_prompt(user_id)
        return

    referred = extract_referral(message.text)
    pending_ref = _PENDING_REF.get(user_id)
    if isinstance(pending_ref, int):
        _PENDING_REF.pop(user_id, None)
        if referred is None:
            referred = pending_ref

    create_user(user_id, username, first_name, referred)
    credits = get_credits(user_id)
    safe_first = _html.escape(str(first_name))
    safe_owner = _html.escape(str(OWNER_NAME or "Shown Legacy"))

    # Keep the caption concise enough for Telegram's 1024-character media-caption limit.
    # Compact quoted / small-caps style inspired by the supplied reference.
    # Telegram has no HTML font-size tag; Unicode small caps create the compact look.
    welcome_caption = (
        "<blockquote>"
        f"<b>✨ 𝑺𝒉𝒐𝒘𝒏 𝑳𝒆𝒈𝒂𝒄𝒚 ✨</b>\n"
        f"<i>Welcome, {safe_first}!</i>\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"{te(EMOJI_TO_PREMIUM['💡'], '💡')} <b>ᴡᴇʟᴄᴏᴍᴇ ᴛᴏ ʏᴏᴜʀ ᴅᴀsʜʙᴏᴀʀᴅ</b>\n"
        "<i>Choose a tool below and send the requested input.</i>\n\n"
        f"{te(EMOJI_TO_PREMIUM['❓'], '❔')} <b>ʜᴏᴡ ᴛᴏ ᴜsᴇ</b>\n"
        f"{te(EMOJI_TO_PREMIUM['🔍'], '🔎')} <i>Tap a button · enter a username, game UID or your own ID.</i>\n\n"
        f"{te(EMOJI_TO_PREMIUM['💡'], '💡')} <b>ғᴇᴀᴛᴜʀᴇs</b>\n"
        f"{te(EMOJI_TO_PREMIUM['📞'], '📱')} ɴᴜᴍʙᴇʀ  •  🆔 ᴛᴇʟᴇɢʀᴀᴍ ɪᴅ\n"
        f"{te(EMOJI_TO_PREMIUM['🎮'], '🎮')} ғʀᴇᴇ ғɪʀᴇ  •  📸 ᴘᴜʙʟɪᴄ ɪɴsᴛᴀɢʀᴀᴍ\n"
        f"{te(EMOJI_TO_PREMIUM['🐙'], '🐙')} ɢɪᴛʜᴜʙ  •  {te(EMOJI_TO_PREMIUM['👤'], '👤')} ᴘʀᴏғɪʟᴇ\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"{te(EMOJI_TO_PREMIUM['💰'], '💎')} <b>ᴄʀᴇᴅɪᴛs:</b> <code>{credits}</code>\n"
        f"👑 <b>ᴏᴡɴᴇʀ:</b> {safe_owner}\n"
        "<i>Use /help for the full command guide.</i>"
        "</blockquote>"
    )

    # Inline launcher is attached only in private chat. No lookup/menu buttons
    # are exposed in groups or supergroups.
    is_private = message.chat.type == "private"
    reply_markup = _private_main_menu_keyboard(is_admin(user_id)) if is_private else None

    try:
        welcome_cfg = _col_media_set.find_one({"setting_key": "welcome_config"}) or {}
        mode = welcome_cfg.get("mode", "default")
        file_id = welcome_cfg.get("file_id")
        custom_caption = str(welcome_cfg.get("text", "") or "").strip()

        # One /start produces exactly one welcome message. If a video/photo is
        # configured, attach the reply keyboard to that media message.
        if is_private and file_id and mode == "video":
            caption = welcome_caption
            if custom_caption and custom_caption.lower() not in ("welcome", "welcome!"):
                caption = (_html.escape(custom_caption[:250]) + "\n\n" + welcome_caption)[:1024]
            bot.send_video(chat_id, file_id, caption=caption, parse_mode="HTML", reply_markup=reply_markup)
        elif is_private and file_id and mode == "photo":
            caption = welcome_caption
            if custom_caption and custom_caption.lower() not in ("welcome", "welcome!"):
                caption = (_html.escape(custom_caption[:250]) + "\n\n" + welcome_caption)[:1024]
            bot.send_photo(chat_id, file_id, caption=caption, parse_mode="HTML", reply_markup=reply_markup)
        else:
            # A text welcome still uses the same single-message layout.
            bot.send_message(chat_id, welcome_caption, parse_mode="HTML", reply_markup=reply_markup)
    except Exception as exc:
        print(f"[START_WELCOME] {exc}")
        try:
            bot.send_message(chat_id, welcome_caption, parse_mode="HTML", reply_markup=reply_markup)
        except Exception as fallback_exc:
            print(f"[START_FALLBACK] {fallback_exc}")

@bot.message_handler(commands=['help'])
def help_cmd(message):

    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    # Admin-editable help content. If no custom content is saved, show the built-in help below.
    try:
        help_cfg = _col_media_set.find_one({"setting_key": "editable_bot_texts"}) or {}
        custom_help = str(help_cfg.get("help_text", "")).strip()
        lookup_guide = str(help_cfg.get("lookup_guide", "")).strip()
        support_text = str(help_cfg.get("support_text", "")).strip()
        if custom_help or lookup_guide or support_text:
            sections = []
            if custom_help:
                sections.append(custom_help)
            if lookup_guide:
                sections.append("<b>📘 LOOKUP GUIDE</b>\n" + lookup_guide)
            if support_text:
                sections.append("<b>☎️ SUPPORT</b>\n" + support_text)
            send_with_premium(chat_id, "\n\n━━━━━━━━━━━━━━━━━━━━\n\n".join(sections), parse_mode="HTML")
            return
    except Exception as exc:
        print(f"[EDITABLE_HELP] {exc}")

    credits = get_credits(user_id)
    bot_username = bot.get_me().username

    _h  = lambda eid, fb: te(eid, fb)

    # ── exact IDs from uploaded emoji list ──
    H_FIRE1  = "5370596264205366968"
    H_FIRE2  = "5372804697734260925"
    H_FIRE3  = "5372972326012857961"
    H_FIRE4  = "5370635893868606590"
    H_FIRE5  = "5370660697304741172"
    H_FIRE6  = "5372880070115341091"
    H_FIRE7  = "5370754155793102519"
    H_STAR1  = "5339247212012528642"
    H_STAR2  = "5339511094803195372"
    H_IDICO  = "5888781182249738113"
    H_BADGE  = "6219727185708582935"
    H_DIAM   = "6048770006810893912"
    H_PHONE  = "5318765591014678496"
    H_PLANE  = "5246931953751443616"
    H_PHONE2 = "5285238101344544669"
    H_GROUP  = "5424746868275944727"
    H_CARD1  = "5985796637971191405"
    H_CARD2  = "4967518033061872209"
    H_STAR3  = "5307517685846785869"
    H_CAR    = "6276097566316695791"
    H_FLAG   = "5807750375033278838"
    H_ATM    = "4967738760021148319"
    H_ROCKET = "5233279094531045380"
    H_PIN    = "5992344826715050001"
    H_LAPTOP = "5465637267626271756"
    H_FLAG2  = "6210718384431041299"
    H_FIRE8  = "6048398234441750217"
    H_SMILEY = "5008416661569536895"
    H_FAMILY = "5386435923204382258"
    H_SHRUG  = "5298773244101281960"
    H_PEN    = "6172477863938233258"

    HDV = (
        _h(H_FIRE1,"🔥") + _h(H_FIRE2,"🔥") + _h(H_FIRE3,"🔥") + _h(H_FIRE3,"🔥") +
        _h(H_FIRE4,"🔥") + _h(H_FIRE5,"🔥") + _h(H_FIRE6,"🔥") + _h(H_FIRE7,"🔥") + "\n"
    )
    H_STARS = _h(H_STAR1,"🌟") + " <b>WELCOME TO OSINT BOT</b> " + _h(H_STAR2,"🌟") + "\n"

# ── help_cmd ───────────────────────────────────────────────
    msg = (
        f"<blockquote>"
        f"{HDV}"
        f"{H_STARS}"
        f"{HDV}"
        f"\n"
        f"{_h(H_SMILEY,'😀')} <b>Hᴇʏ !!</b>\n"
        f"{_h(H_IDICO,'🆔')} <b>ID</b>: <code>{user_id}</code>\n"
        f"{_h(H_BADGE,'⚜️')} <b>Cʀᴇᴅɪᴛꜱ</b>: <b>{credits}</b>\n\n"
        f"{HDV}"
        f"{_h(H_DIAM,'💎')} <b>OSINT COMMANDS:</b>\n\n"
        f"{_h(H_PHONE,'☎️')} /num <code>9876543210</code> - Indian Phone\n"
        f"{_h(H_PLANE,'✈️')} /tgid <code>username</code> - Telegram info (Phone lookup)\n"
        f"{_h(H_PHONE2,'📞')} /num2 <code>9876543210</code> - Phone number info (Alternate API)\n"
        f"{_h(H_GROUP,'👥')} /name <code>abhiraaj</code> - Name to details\n"
        f"{_h(H_CARD1,'💳')} /pan <code>AXDPR2606K</code> - PAN Card info\n"
        f"{_h(H_CARD2,'💳')} /adhr <code>393933081942</code> - Aadhar info\n"
        f"{_h(H_STAR3,'🤩')} /vech <code>HR26DA1337</code> - Vehicle info\n"
        f"{_h(H_CAR,'🚘')} /vechrc <code>HR26EV0001</code> - RC info\n"
        f"{_h(H_FLAG,'🇮🇳')} /upi <code>id@bank</code> - UPI ID info\n"
        f"{_h(H_ATM,'🏧')} /ifsc <code>SBIN0001234</code> - Bank info\n"
        f"{_h(H_ROCKET,'🚀')} /ip <code>8.8.8.8</code> - IP info\n"
        f"{_h(H_PIN,'📍')} /pin <code>110001</code> - Pincode info\n"
        f"{_h(H_LAPTOP,'💻')} /git <code>username</code> - GitHub info\n"
        f"{_h(H_FLAG2,'🇮🇳')} /bgmi <code>5121439477</code> - BGMI info\n"
        f"{_h(H_FIRE8,'🔥')} /ff <code>123456789</code> - FreeFire info\n"
        f"{_h(H_SMILEY,'😀')} /insta <code>username</code> - Instagram info\n"
        f"{_h(H_FAMILY,'👨‍👩‍👧‍👦')} /family <code>701984830542</code> - Family Details (Ration Card)\n"
        f"{_h(H_SHRUG,'🤷‍♂️')} /ai <code>prompt</code> - AI Image Generation\n\n"
        f"{HDV}"
        f"{_h(H_PEN,'✍️')} <b>OTHER COMMANDS:</b>\n\n"
        f"/redeem  - Rᴇᴅᴇᴇᴍ ᴄʀᴇᴅɪᴛꜱ\n"
        f"/profile - Yᴏᴜʀ ᴩʀᴏꜰɪʟᴇ\n"
        f"/balance - Cʜᴇᴄᴋ ᴄʀᴇᴅɪᴛꜱ\n"
        f"/refer - Rᴇꜰᴇʀʀᴀʟ ᴄʀᴇᴅɪᴛꜱ\n"
        f"/help - Aʟʟ ᴄᴏᴍᴍᴀɴᴅꜱ\n\n"
        f"{_h(H_STAR1,'🌟')} <b>Oᴡɴᴇʀ</b>: {OWNER_USERNAME}\n"
        f"</blockquote>"
    )

    markup = None
    if message.chat.type == "private":
        markup = InlineKeyboardMarkup()
        markup.add(create_success_button("➕ ADD BOT TO GROUP", url=f"https://t.me/{bot_username}?startgroup=start"))

    try:
        sent = send_with_premium(chat_id, msg, parse_mode='HTML', reply_markup=markup)
        schedule_deletion(sent.message_id, chat_id)
    except Exception as e:
        print(f"Error in help command: {e}")

@bot.message_handler(commands=['profile'])
def profile_cmd(message):
    """Show the caller's own profile using the current MongoDB document schema."""
    user_id = message.from_user.id
    chat_id = message.chat.id
    try:
        error_msg = get_access_error_message(user_id)
        if error_msg:
            send_with_premium(chat_id, error_msg)
            return
        if not enforce_force_join(message):
            return

        doc = get_user(user_id)
        if not doc:
            send_with_premium(chat_id, "❌ Please /start first!")
            return

        # Keep activity timestamps current even when the user only opens a menu.
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        _col_users.update_one({"user_id": user_id}, {"$set": {"last_active": now}})
        referral_total = _col_referrals.count_documents({"referrer_id": user_id})
        successful_referrals = referral_total
        credits = int(doc.get("credits", 0) or 0)
        searches = int(doc.get("total_commands", 0) or 0)
        joined = str(doc.get("join_date", "N/A"))[:19]
        username = doc.get("username") or "N/A"
        if username != "N/A":
            username = "@" + str(username).lstrip("@")
        else:
            username = "N/A"
        name = _html.escape(str(doc.get("first_name") or message.from_user.first_name or "User"))
        referral_link = ""
        try:
            me = bot.get_me()
            referral_link = f"https://t.me/{me.username}?start=ref_{user_id}"
        except Exception:
            pass

        msg = (
            "<blockquote><b>👤 MY PROFILE · SHOWN LEGACY</b>\n"
            "━━━━━━━━━━━━━━━━━━━━\n"
            f"🆔 <b>Telegram ID:</b> <code>{user_id}</code>\n"
            f"👤 <b>Name:</b> {name}\n"
            f"🔗 <b>Username:</b> {_html.escape(username)}\n"
            f"💎 <b>Credits / Points:</b> <code>{credits:,}</code>\n"
            f"🎁 <b>Total referrals:</b> <code>{referral_total:,}</code>\n"
            f"✅ <b>Successful referrals:</b> <code>{successful_referrals:,}</code>\n"
            f"🔎 <b>Searches performed:</b> <code>{searches:,}</code>\n"
            f"📅 <b>Joined:</b> <code>{_html.escape(joined)}</code>\n"
            f"👑 <b>Admin:</b> {'Yes' if doc.get('is_admin') or user_id in ADMIN_IDS else 'No'}\n"
            "━━━━━━━━━━━━━━━━━━━━</blockquote>"
        )
        if referral_link:
            msg += f"\n🎟 <b>Your referral link</b>\n<code>{_html.escape(referral_link)}</code>"
        send_with_premium(chat_id, msg, parse_mode='HTML')
    except Exception as e:
        logger.exception("profile command failed: %s", e)
        send_with_premium(chat_id, "❌ Could not load your profile right now. Please try /profile again.")

@bot.message_handler(commands=['balance'])
def balance_cmd(message):
    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    credits = get_credits(user_id)
    msg = f"""
💰 CREDIT BALANCE

💳 Credits: {credits}
"""
    try:
        sent = send_with_premium(chat_id, msg)
        schedule_deletion(sent.message_id, chat_id)
    except Exception as e:
        print(f"Error in balance command: {e}")

@bot.message_handler(commands=['refer'])
def refer_cmd(message):

    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    bot_user = bot.get_me().username
    link = f"https://t.me/{bot_user}?start=ref_{user_id}"
    msg = f"""
🔗 YOUR REFERRAL LINK

📨 <code>{link}</code>

📋 Rules:
• Friend gets: {REFERRAL_BONUS_NEW} credits
• You gets: {REFERRAL_BONUS_REFERRER} credits
"""
    try:
        sent = send_with_premium(chat_id, msg, parse_mode='HTML')
        schedule_deletion(sent.message_id, chat_id)
    except Exception as e:
        print(f"Error in refer command: {e}")

@bot.message_handler(commands=['redeem'])
def redeem_cmd(message):
    if not is_recent_command(message):
        return

    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    parts = message.text.split()
    if len(parts) < 2:
        msg = """❌ USE: /redeem CODE

💡 EXAMPLE: /redeem ABC123XYZ

⚠️ NOTE: Each code can be used only ONCE per user!

🎫 Get codes from admin: @flirts_x"""
        send_with_premium(chat_id, msg)
        return

    code = parts[1].strip().upper()
    wait_msg = send_with_premium(chat_id, f"🔍 Verifying code: {code}...")
    success, result = redeem_credits(user_id, code)

    if success:
        new_credits = get_credits(user_id)
        match = re.search(r'(\d+)', result)
        amount = match.group(1) if match else "10"

        final_msg = f"""✅ REDEMPTION SUCCESSFUL! ✅

🎫 Code: {code}
💰 Credits Added: +{amount}
💳 New Balance: {new_credits} credits

✨ Use /balance to check your credits
✨ Use /profile to see your stats"""

        try:
            edit_with_premium(chat_id, wait_msg.message_id, final_msg)
        except:
            bot.delete_message(chat_id, wait_msg.message_id)
            send_with_premium(chat_id, final_msg)
    else:
        final_msg = f"""❌ REDEMPTION FAILED ❌

🎫 Code: {code}
❌ Error: {result}

💡 Possible reasons:
• Invalid or expired code
• Code already used by you
• Code max usage reached
• Code doesn't exist

📞 Contact admin: {OWNER_USERNAME}"""

        try:
            edit_with_premium(chat_id, wait_msg.message_id, final_msg)
        except:
            bot.delete_message(chat_id, wait_msg.message_id)
            send_with_premium(chat_id, final_msg)

def handle_api_command(message, command_name, api_func, validate_func, title, query_processor=None):
    if not is_recent_command(message):
        return

    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(chat_id, f"❌ Use: /{command_name} [query]")
        return

    query = parts[1].strip()
    if query_processor:
        query = query_processor(query)
    if validate_func and not validate_func(query):
        send_with_premium(chat_id, f"❌ Invalid {command_name} format!")
        return

    working, status_msg = check_api_status(command_name)
    if not working:
        send_with_premium(chat_id, f"""
<blockquote>{title}</blockquote>

<blockquote>⚠️ API IS UNDER MAINTENANCE/FIXING
{status_msg or 'Please try again later'}</blockquote>
""")
        return

    if not is_group_chat(message):
        if not deduct_credit(user_id):
            send_with_premium(chat_id, "❌ Insufficient credits!")
            return
    credits_left = _pop_deducted_balance(user_id) if not is_group_chat(message) else "∞ (Group)"

    try:
        _bg_chat_action(chat_id, 'typing')
    except:
        pass

    wait = send_searching_animation(chat_id)
    result = api_func(query)
    wait._stop_event.set()

    formatted_msg = format_api_result(result, title, query, credits_left)
    json_file = save_result_to_json(command_name, query, result)

    if json_file:
        sent_msg = send_result_with_json(chat_id, formatted_msg, json_file, wait.message_id)
    else:
        sent_msg = send_result(chat_id, formatted_msg, wait)

    if sent_msg:
        send_random_media(chat_id, sent_msg.message_id)

@bot.message_handler(commands=['name'])
def name_cmd(message):
    handle_api_command(message, 'name', call_name_api, None, "👤 NAME SEARCH")

@bot.message_handler(commands=['pan'])
def pan_cmd(message):
    handle_api_command(message, 'pan', call_pan_api, validate_pan, "📄 PAN CARD INFO", lambda x: x.upper())

@bot.message_handler(commands=['vech'])
def vech_cmd(message):
    if not is_recent_command(message):
        return

    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(chat_id,
            "❌ Use: /vech [VEHICLE_NUMBER]\n\n"
            "📝 Examples:\n/vech MH12AB1234\n/vech DL01AB1234\n\n"
            "🔍 Get detailed vehicle information"
        )
        return

    vehicle = parts[1].strip().upper().replace(' ', '')
    if not validate_vehicle(vehicle):
        send_with_premium(chat_id, "❌ Invalid vehicle number format!")
        return

    working, status_msg = check_api_status('vech')
    if not working:
        send_with_premium(chat_id, f"""
<blockquote>🚗 VEHICLE INFO</blockquote>

<blockquote>⚠️ API IS UNDER MAINTENANCE/FIXING
{status_msg or 'Please try again later'}</blockquote>
""")
        return

    if not is_group_chat(message):
        if not deduct_credit(user_id):
            send_with_premium(chat_id, "❌ Insufficient credits!")
            return
    credits_left = _pop_deducted_balance(user_id) if not is_group_chat(message) else "∞ (Group)"

    try:
        _bg_chat_action(chat_id, 'typing')
    except:
        pass

    wait = send_searching_animation(chat_id)
    result = call_vehicle_api(vehicle)
    wait._stop_event.set()

    pages = format_vehicle_result_v2(result, vehicle, credits_left)
    json_file = save_result_to_json("vech", vehicle, result)

    if len(pages) == 1:
        # Single page - send directly with JSON button
        markup = InlineKeyboardMarkup()
        if json_file:
            file_id = hashlib.md5(json_file.encode()).hexdigest()[:16]
            JSON_FILES[file_id] = json_file
            markup.add(InlineKeyboardButton("📥 Download JSON", callback_data=f"dljson_{file_id}"))
        markup.add(create_default_button("🔙 Back", callback_data="back_to_result", icon_custom_emoji_id="5307517685846785869"))
        try:
            bot.delete_message(chat_id, wait.message_id)
        except:
            pass
        sent = send_with_premium(chat_id, pages[0], reply_markup=markup)
        if sent:
            schedule_deletion(sent.message_id, chat_id)
            send_random_media(chat_id, sent.message_id)
    else:
        # Multi-page with pagination
        send_paginated_vech(chat_id, user_id, pages, json_file, vehicle, wait, command="vech")


@bot.message_handler(commands=['vechrc'])
def vechrc_cmd(message):
    if not is_recent_command(message):
        return

    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(chat_id,
            "❌ Use: /vechrc [VEHICLE_NUMBER]\n\n"
            "📝 Examples:\n/vechrc MH12AB1234\n/vechrc DL01AB1234\n\n"
            "🔍 Get detailed RC (Registration Certificate) information"
        )
        return

    vehicle = parts[1].strip().upper().replace(' ', '')
    if not validate_vehicle(vehicle):
        send_with_premium(chat_id, "❌ Invalid vehicle number format!")
        return

    working, status_msg = check_api_status('vechrc')
    if not working:
        send_with_premium(chat_id, f"""
<blockquote>📋 RC DETAILS</blockquote>

<blockquote>⚠️ API IS UNDER MAINTENANCE/FIXING
{status_msg or 'Please try again later'}</blockquote>
""")
        return

    if not is_group_chat(message):
        if not deduct_credit(user_id):
            send_with_premium(chat_id, "❌ Insufficient credits!")
            return
    credits_left = _pop_deducted_balance(user_id) if not is_group_chat(message) else "∞ (Group)"

    try:
        _bg_chat_action(chat_id, 'typing')
    except:
        pass

    wait = send_searching_animation(chat_id)
    result = call_rc_api(vehicle)
    wait._stop_event.set()

    pages = format_rc_result_v2(result, vehicle, credits_left)
    json_file = save_result_to_json("vechrc", vehicle, result)

    if len(pages) == 1:
        markup = InlineKeyboardMarkup()
        if json_file:
            file_id = hashlib.md5(json_file.encode()).hexdigest()[:16]
            JSON_FILES[file_id] = json_file
            markup.add(InlineKeyboardButton("📥 Download JSON", callback_data=f"dljson_{file_id}"))
        markup.add(create_default_button("🔙 Back", callback_data="back_to_result", icon_custom_emoji_id="5307517685846785869"))
        try:
            bot.delete_message(chat_id, wait.message_id)
        except:
            pass
        sent = send_with_premium(chat_id, pages[0], reply_markup=markup)
        if sent:
            schedule_deletion(sent.message_id, chat_id)
            send_random_media(chat_id, sent.message_id)
    else:
        send_paginated_vech(chat_id, user_id, pages, json_file, vehicle, wait, command="vechrc")

@bot.message_handler(commands=['ip'])
def ip_cmd(message):
    handle_api_command(message, 'ip', call_ip_api, validate_ip, "🌐 IP ADDRESS INFO")

@bot.message_handler(commands=['pin'])
def pin_cmd(message):
    handle_api_command(message, 'pin', call_pincode_api, validate_pincode, "📮 PINCODE INFO")

@bot.message_handler(commands=['git'])
def git_cmd(message):
    handle_api_command(message, 'git', call_git_api, None, "🐙 GITHUB PROFILE", lambda x: x.replace('@', ''))

@bot.message_handler(commands=['bgmi'])
def bgmi_cmd(message):
    handle_api_command(message, 'bgmi', call_bgmi_api, None, "🎮 BGMI PLAYER INFO")

@bot.message_handler(commands=['ff'])
def ff_cmd(message):
    handle_api_command(message, 'ff', call_ff_api, None, "🔥 FREEFIRE PLAYER INFO")


def call_email_api(email_addr):
    return _generic_get("email", str(email_addr).strip().lower())


def call_veh2num_api(vehicle):
    return _generic_get("veh2num", str(vehicle).strip().upper().replace(" ", ""))


@bot.message_handler(commands=['email'])
def email_cmd(message):
    handle_api_command(message, 'email', call_email_api, None, "📧 EMAIL INFO")


@bot.message_handler(commands=['veh2num'])
def veh2num_cmd(message):
    handle_api_command(message, 'veh2num', call_veh2num_api, validate_vehicle,
                       "🔢 VEHICLE → NUMBERS")

@bot.message_handler(commands=['domain'])
def domain_cmd(message):
    handle_api_command(message, 'domain', call_domain_api, None, "\U0001f517 DOMAIN INFO")

@bot.message_handler(commands=['imei'])
def imei_cmd(message):
    handle_api_command(message, 'imei', call_imei_api, None, "\U0001f4f2 IMEI INFO")

@bot.message_handler(commands=['osint'])
def osint_cmd(message):
    handle_api_command(message, 'osint', call_osint_api, None, "\U0001f50e OSINT LOOKUP")

@bot.message_handler(commands=['upi'])
def upi_cmd(message):
    # custom UPI handler — uses rich format_upi_result
    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    if not enforce_force_join(message):
        return
    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(message.chat.id,
            "❌ Use: /upi [upi_id]\n\n📝 Examples:\n/upi elvishrao@okicici\n/upi user@paytm\n\n💳 Get UPI ID details")
        return
    upi_input = parts[1].strip()
    if not validate_upi(upi_input):
        send_with_premium(message.chat.id, "❌ Invalid UPI ID! Format: username@bank")
        return
    working, status_msg = check_api_status('upi')
    if not working:
        send_with_premium(message.chat.id, f"<blockquote>💳 UPI ID INFO</blockquote>\n<blockquote>⚠️ API MAINTENANCE\n{status_msg or 'Try again later'}</blockquote>")
        return
    chat_id = message.chat.id
    if not is_group_chat(message):
        if not deduct_credit(user_id):
            send_with_premium(chat_id, "❌ Insufficient credits!"); return
    credits_left = _pop_deducted_balance(user_id) if not is_group_chat(message) else "∞ (Group)"
    try: _bg_chat_action(chat_id, 'typing')
    except Exception: pass
    wait = send_searching_animation(chat_id)
    result = call_upi_api(upi_input)
    wait._stop_event.set()
    pages = format_upi_result(result, upi_input, credits_left)
    json_file = save_result_to_json("upi", upi_input, result)
    txt, markup = pages[0]
    if markup is None and json_file:
        markup = InlineKeyboardMarkup()
        fid = hashlib.md5(json_file.encode()).hexdigest()[:16]
        JSON_FILES[fid] = json_file
        markup.add(create_primary_button("📥 Download JSON", callback_data=f"dljson_{fid}", icon_custom_emoji_id="5465637267626271756"))
    try: bot.delete_message(chat_id, wait.message_id)
    except Exception: pass
    sent_msg = send_with_premium(chat_id, txt, reply_markup=markup)
    if sent_msg:
        schedule_deletion(sent_msg.message_id, chat_id)
        send_random_media(chat_id, sent_msg.message_id)

@bot.message_handler(commands=['ifsc'])
def ifsc_cmd(message):
    handle_api_command(message, 'ifsc', call_ifsc_api, validate_ifsc, "🏦 BANK INFO", lambda x: x.upper())

@bot.message_handler(commands=['family'])
def family_cmd(message):
    if not is_recent_command(message):
        return

    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(message.chat.id,
            "❌ Use: /family [AADHAR_NUMBER]\n\n"
            "📝 Examples:\n/family 701984830542\n/family 377226634228\n\n"
            "👨‍👩‍👧‍👦 Get family details (Ration Card, Members) via Aadhar"
        )
        return

    aadhar_raw = re.sub(r'[^\d]', '', parts[1].strip())

    if not validate_aadhar(aadhar_raw):
        send_with_premium(message.chat.id, "❌ Invalid Aadhar number! Use 12 digits only.")
        return

    if not is_group_chat(message):
        if not deduct_credit(user_id):
            send_with_premium(message.chat.id, "❌ Insufficient credits!")
            return
    credits_left = _pop_deducted_balance(user_id) if not is_group_chat(message) else "∞ (Group)"

    working, status_msg = check_api_status('family')
    if not working:
        _refund_credit(user_id, message)
        send_with_premium(message.chat.id, f"""
<blockquote>👨‍👩‍👧‍👦 FAMILY DETAILS</blockquote>

<blockquote>⚠️ API IS UNDER MAINTENANCE/FIXING
{status_msg or 'Please try again later'}</blockquote>
""")
        return

    try: _bg_chat_action(chat_id, 'typing')
    except Exception: pass

    wait = send_searching_animation(chat_id)
    result = call_family_api(aadhar_raw)
    wait._stop_event.set()
    pages = format_family_result(result, aadhar_raw, credits_left)
    json_file = save_result_to_json("family", aadhar_raw, result)

    NUM_PAGINATION[user_id] = {"pages": pages, "json_file": json_file, "query": aadhar_raw}
    first_txt, first_markup = pages[0]

    if len(pages) == 1 and json_file and first_markup is None:
        file_id = hashlib.md5(json_file.encode()).hexdigest()[:16]
        JSON_FILES[file_id] = json_file
        first_markup = InlineKeyboardMarkup()
        first_markup.add(InlineKeyboardButton("📥 Download JSON", callback_data=f"dljson_{file_id}"))

    try: bot.delete_message(chat_id, wait.message_id)
    except Exception: pass

    sent_msg = send_with_premium(chat_id, first_txt, reply_markup=first_markup)
    if sent_msg:
        schedule_deletion(sent_msg.message_id, chat_id)
        send_random_media(chat_id, sent_msg.message_id)

@bot.message_handler(commands=['snap'])
def snap_cmd(message):
    if not is_recent_command(message):
        return

    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(chat_id,
            "❌ Use: /snap [snapchat_username]\n\n"
            "📝 Examples:\n/snap john_doe\n/snap @cooluser\n\n"
            "👻 Get Snapchat profile info"
        )
        return

    username = parts[1].strip().lstrip('@').replace(' ', '_')
    if not username:
        send_with_premium(chat_id, "❌ Invalid username!")
        return

    working, status_msg = check_api_status('snap')
    if not working:
        send_with_premium(chat_id,
            f"<blockquote>👻 SNAPCHAT INFO</blockquote>\n\n"
            f"<blockquote>⚠️ API IS UNDER MAINTENANCE\n{status_msg or 'Please try again later'}</blockquote>"
        )
        return

    if not is_group_chat(message):
        if not deduct_credit(user_id):
            send_with_premium(chat_id, "❌ Insufficient credits!")
            return
    credits_left = _pop_deducted_balance(user_id) if not is_group_chat(message) else "∞ (Group)"

    try: _bg_chat_action(chat_id, 'typing')
    except Exception: pass

    wait = send_searching_animation(chat_id)
    result = call_snap_api(username)
    wait._stop_event.set()

    formatted_msg, pic_url = format_snap_result(result, username, credits_left)
    json_file = save_result_to_json("snap", username, result)

    markup = InlineKeyboardMarkup(row_width=1)
    if json_file:
        file_id = hashlib.md5(json_file.encode()).hexdigest()[:16]
        JSON_FILES[file_id] = json_file
        markup.add(create_primary_button("📥 Download JSON",
            callback_data=f"dljson_{file_id}",
            icon_custom_emoji_id="5465637267626271756"))
    markup.add(create_default_button("🔙 Back",
        callback_data="back_to_result",
        icon_custom_emoji_id="5307517685846785869"))

    sent_msg = None
    if pic_url and pic_url.startswith("http"):
        try:
            sent_msg = bot.send_photo(chat_id, pic_url,
                caption=formatted_msg, reply_markup=markup, parse_mode='HTML')
            try: bot.delete_message(chat_id, wait.message_id)
            except Exception: pass
        except Exception:
            if json_file:
                sent_msg = send_result_with_json(chat_id, formatted_msg, json_file, wait.message_id)
            else:
                sent_msg = send_result(chat_id, formatted_msg, wait)
    else:
        if json_file:
            sent_msg = send_result_with_json(chat_id, formatted_msg, json_file, wait.message_id)
        else:
            sent_msg = send_result(chat_id, formatted_msg, wait)

    if sent_msg:
        schedule_deletion(sent_msg.message_id, chat_id)
        send_random_media(chat_id, sent_msg.message_id)


@bot.message_handler(commands=['ai'])
def ai_cmd(message):
    if not is_recent_command(message):
        return

    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    working, status_msg = check_api_status('ai')
    if not working:
        send_with_premium(message.chat.id, f"""
<blockquote>🎨 AI IMAGE GENERATION</blockquote>

<blockquote>⚠️ API IS UNDER MAINTENANCE/FIXING
{status_msg or 'Please try again later'}</blockquote>
""")
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(message.chat.id, """
🎨 AI IMAGE GENERATION

❌ Please provide a prompt!

📝 Usage: `/ai [prompt]`

<blockquote>✨ Examples:
/ai beautiful sunset over mountains
/ai cyberpunk city at night
/ai cute cat wearing sunglasses</blockquote>

⚡ Powered by Pollinations AI
""")
        return

    prompt = parts[1].strip()
    if len(prompt) < 3:
        send_with_premium(message.chat.id, "❌ Prompt too short! Please provide at least 3 characters.")
        return

    if not is_group_chat(message):
        if not deduct_credit(user_id):
            send_with_premium(message.chat.id, "❌ Insufficient credits! Get more via referral or redeem codes.")
            return

    credits_left = _pop_deducted_balance(user_id) if not is_group_chat(message) else "∞ (Group)"

    _bg_chat_action(chat_id, 'upload_photo')
    wait = send_searching_animation(chat_id)
    _bg_chat_action(chat_id, 'upload_photo')

    # provider image API first, Pollinations as fallback
    provider_image = None
    try:
        _img_tpl = ep("image", prompt)
        if _img_tpl:
            _img_data = make_api_request(_img_tpl, timeout=60)
            _imgs = _img_data.get("images") if isinstance(_img_data, dict) else None
            if isinstance(_imgs, list) and _imgs and isinstance(_imgs[0], dict):
                provider_image = _imgs[0].get("url")
    except Exception as _img_err:
        print(f"[AI] provider image error: {_img_err}")

    seed = random.randint(1, 999999)
    encoded_prompt = requests.utils.quote(prompt)
    image_url = provider_image or f"(AI)prompt/{encoded_prompt}?width=1024&height=1024&nologo=true&seed={seed}&model=flux"

    try:
        img_response = session.get(image_url, timeout=(5, 30), headers={'Accept': 'image/*,*/*'})
        wait._stop_event.set()   # stop loader before showing the result
        if img_response.status_code == 200:
            content_type = img_response.headers.get('content-type', '')
            if 'image' in content_type:
                # in-memory upload: no temp file, no name collisions, no leaks
                f = io.BytesIO(img_response.content)
                f.name = "ai_image.png"
                cap_text = f"""
🎨 AI IMAGE GENERATION

🔍 Prompt: {_html.escape(prompt)}

💰 Credits Left: {credits_left}
"""
                caption = replace_with_premium_emojis(cap_text)
                sent_msg = bot.send_photo(chat_id, f, caption=caption, parse_mode='HTML')
                send_random_media(chat_id, sent_msg.message_id)
                _safe_call(bot.delete_message, chat_id, wait.message_id)
            else:
                raise Exception(f"Not an image, content-type: {content_type}")
        else:
            raise Exception(f"HTTP {img_response.status_code}")
    except Exception as e:
        msg = f"""
🎨 AI IMAGE GENERATION

🔍 Prompt: {_html.escape(prompt)}
🖼️ Click to view: {image_url}

💰 Credits Left: {credits_left}

💡 The image was generated but couldn't be downloaded.
   Click the link above to view it!
"""
        sent_msg = send_result(chat_id, msg, wait)
        if sent_msg:
            send_random_media(chat_id, sent_msg.message_id)

@bot.message_handler(commands=['num2'])
def num2_cmd(message):
    if not is_recent_command(message):
        return

    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(message.chat.id, """❌ Use: /num2 [phone_number]

📝 Examples:
/num2 9876543210
/num2 +919876543210

🔍 Get detailed information about any phone number
""")
        return

    phone = parts[1].strip()
    phone = re.sub(r'[^\d+]', '', phone)

    if not validate_phone(phone):
        send_with_premium(message.chat.id, "❌ Invalid phone number! Use 10-15 digits with optional +")
        return

    if not is_group_chat(message):
        if not deduct_credit(user_id):
            send_with_premium(message.chat.id, "❌ Insufficient credits!")
            return
    credits_left = _pop_deducted_balance(user_id) if not is_group_chat(message) else "∞ (Group)"

    _bg_chat_action(chat_id, 'typing')
    wait = send_searching_animation(chat_id)
    result = call_num2_api(phone)
    wait._stop_event.set()
    formatted_msg = format_api_result(result, "📱 PHONE NUMBER INFO (Alt)", phone, credits_left)
    json_file = save_result_to_json("num2", phone, result)

    if json_file:
        sent_msg = send_result_with_json(chat_id, formatted_msg, json_file, wait.message_id)
    else:
        sent_msg = send_result(chat_id, formatted_msg, wait)

    if sent_msg:
        send_random_media(chat_id, sent_msg.message_id)

@bot.message_handler(commands=['insta'])
def insta_cmd(message):
    if not is_recent_command(message):
        return

    user_id = message.from_user.id
    error_msg = get_access_error_message(user_id)
    if error_msg:
        send_with_premium(message.chat.id, error_msg)
        return
    chat_id = message.chat.id

    if not enforce_force_join(message):
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(message.chat.id, "❌ Use: /insta [username]\n\nExample: <code>/insta just_sahil_621</code>")
        return

    username = parts[1].strip().replace('@', '')

    if not is_group_chat(message):
        if not deduct_credit(user_id):
            send_with_premium(message.chat.id, "❌ Insufficient credits!")
            return
        credits_left = _pop_deducted_balance(user_id)
    else:
        credits_left = "∞ (Group)"

    try:
        _bg_chat_action(chat_id, 'typing')
    except:
        pass

    wait = send_searching_animation(chat_id)
    result = call_insta_api(username)
    wait._stop_event.set()

    if result.get('status') == 'error':
        msg = (
            "<blockquote>📸 INSTAGRAM INFO</blockquote>\n\n"
            "<blockquote>❌ Instagram API is currently down. Please try again later.</blockquote>\n\n"
            "💰 Credits Left: " + str(credits_left)
        )
        sent_msg = send_result(chat_id, msg, wait)
        if sent_msg:
            send_random_media(chat_id, sent_msg.message_id)
        return

    formatted_msg = format_insta_result_v3(result, username, credits_left)
    json_file = save_result_to_json("insta", username, result)

    # New API returns profile data at the top level; old nested responses remain supported.
    raw_profile = result.get("result", {}).get("profile", {}) if isinstance(result.get("result"), dict) else {}
    if not raw_profile:
        raw_profile = result.get("profile", {})
    if not raw_profile and result.get("username"):
        raw_profile = result
    pic_url = str(raw_profile.get(
        "hd_profile_pic_url",
        raw_profile.get("profile_pic_url", raw_profile.get("profile_pic_url_hd", ""))
    ) or "")

    # Telegram captions/messages are limited to 1024/4096 chars. Use the same
    # Prev/Next pagination flow for long Instagram responses, keeping each page
    # comfortably below Telegram's 1024-character caption limit.
    def _insta_pages(text, limit=950):
        body = text
        if body.startswith("<blockquote>") and body.endswith("</blockquote>"):
            body = body[len("<blockquote>"):-len("</blockquote>")]
        chunks, current = [], []
        current_len = 0
        for line in body.splitlines():
            add_len = len(line) + (1 if current else 0)
            if current and current_len + add_len > limit:
                chunks.append("<blockquote>" + "\n".join(current) + "</blockquote>")
                current, current_len = [], 0
            current.append(line)
            current_len += len(line) + (1 if len(current) > 1 else 0)
        if current:
            chunks.append("<blockquote>" + "\n".join(current) + "</blockquote>")
        return chunks or [text]

    posts = result.get("posts", []) if isinstance(result.get("posts", []), list) else []
    if posts:
        normalized_posts = []
        for post in posts:
            if isinstance(post, dict):
                item = dict(post)
                item["img"] = item.get("img") or item.get("display_url") or item.get("thumbnail")
                normalized_posts.append(item)
        POSTS_CACHE[username] = normalized_posts

    pages = _insta_pages(formatted_msg) if len(formatted_msg) > 1024 else [formatted_msg]

    # Download the CDN image and upload bytes to Telegram. Passing the Instagram
    # URL directly often makes Telegram show a link or fail because of CDN auth.
    profile_photo = None
    if pic_url.startswith("http"):
        try:
            photo_response = session.get(pic_url, timeout=20, headers={"User-Agent": "Mozilla/5.0"})
            photo_response.raise_for_status()
            if photo_response.content:
                profile_photo = io.BytesIO(photo_response.content)
                profile_photo.name = "instagram_profile.jpg"
        except Exception as e:
            print(f"Insta profile photo download failed: {e}")

    # Keep profile photo and response together. Telegram captions are limited
    # to 1024 characters, so long responses use a compact plain-text caption
    # rather than sending a second profile-only message.
    caption_text = formatted_msg
    caption_parse_mode = "HTML"
    if len(_html_to_plain(caption_text)) > 1024:
        # Remove only custom-emoji entities first; keep blockquote/bold HTML.
        caption_text = _downgrade_premium_emojis(caption_text)
    if len(_html_to_plain(caption_text)) > 1024:
        inner = caption_text
        if inner.startswith("<blockquote>") and inner.endswith("</blockquote>"):
            inner = inner[len("<blockquote>"):-len("</blockquote>")]
        caption_text = "<blockquote>" + inner[:980].rstrip() + "…</blockquote>"

    markup = InlineKeyboardMarkup(row_width=1)
    if json_file:
        file_id = hashlib.md5(json_file.encode()).hexdigest()[:16]
        JSON_FILES[file_id] = json_file
        markup.add(create_primary_button("📥 Download JSON", callback_data="dljson_" + file_id, icon_custom_emoji_id="5465637267626271756"))
    if posts:
        markup.add(create_primary_button(
            "📸 See Post",
            callback_data=f"viewall_{username}",
            icon_custom_emoji_id=SEE_POST_EMOJI_ID,
        ))
    markup.add(create_default_button("🔙 Back", callback_data="back_to_result", icon_custom_emoji_id="5307517685846785869"))

    sent_msg = None
    if profile_photo:
        try:
            sent_msg = bot.send_photo(chat_id, profile_photo, caption=caption_text,
                                      reply_markup=markup, parse_mode=caption_parse_mode)
        except Exception as e:
            print(f"Insta profile photo upload failed: {e}")
            try:
                sent_msg = bot.send_photo(chat_id, profile_photo, caption=_downgrade_premium_emojis(caption_text),
                                          reply_markup=markup, parse_mode="HTML")
            except Exception as e2:
                print(f"Insta profile photo fallback failed: {e2}")

    # If CDN bytes were blocked, ask Telegram to fetch the same image URL,
    # still with the response as its caption. No standalone profile message.
    if sent_msg is None and pic_url.startswith("http"):
        try:
            sent_msg = bot.send_photo(chat_id, pic_url, caption=caption_text,
                                      reply_markup=markup, parse_mode=caption_parse_mode)
        except Exception as e:
            print(f"Insta URL photo upload failed: {e}")
            try:
                sent_msg = bot.send_photo(chat_id, pic_url, caption=_downgrade_premium_emojis(caption_text),
                                          reply_markup=markup, parse_mode="HTML")
            except Exception as e2:
                print(f"Insta URL photo fallback failed: {e2}")

    if sent_msg is None:
        try:
            bot.delete_message(chat_id, wait.message_id)
        except:
            pass
        sent_msg = send_with_premium(chat_id, formatted_msg, reply_markup=markup)

    if sent_msg:
        send_random_media(chat_id, sent_msg.message_id)


def admin_panel(message):
    """Full admin panel; inline admin controls are private-chat only."""
    if message.chat.type != "private":
        send_with_premium(message.chat.id, "🔒 Open the bot in private chat to use the Admin Panel.")
        return
    if not is_admin(message.from_user.id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    chat_id = message.chat.id
    stats = get_bot_stats()
    send_with_premium(chat_id, _admin_panel_text(stats), reply_markup=_admin_reply_keyboard(0))


def _admin_panel_text(stats):
    """Premium admin dashboard; values are live stats from the existing store."""
    total_users = stats.get('total_users', 0)
    today_users = stats.get('today_users', 0)
    active_users = stats.get('active_users', 0)
    daily_active_users = stats.get('daily_active_users', 0)
    total_credits = stats.get('total_credits', 0)
    commands_used = stats.get('total_commands', 0)
    referrals = stats.get('total_referrals', 0)

    return (
        "<blockquote>"
        "<b>👑 𝑺𝒉𝒐𝒘𝒏 𝑳𝒆𝒈𝒂𝒄𝒚 · CONTROL CENTER</b>\n"
        "<i>Administrator dashboard</i>\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        "</blockquote>"
        "<blockquote>"
        "<b>📊 LIVE OVERVIEW</b>\n"
        f"👥 <b>Total users</b>       <code>{total_users:,}</code>\n"
        f"🆕 <b>Joined today</b>      <code>{today_users:,}</code>\n"
        f"🟢 <b>Active · 24h</b>      <code>{active_users:,}</code>\n"
        f"📆 <b>Daily active users</b> <code>{daily_active_users:,}</code>\n"
        f"💰 <b>Credits issued</b>    <code>{total_credits:,}</code>\n"
        f"⚡ <b>Commands used</b>     <code>{commands_used:,}</code>\n"
        f"🎁 <b>Referrals</b>         <code>{referrals:,}</code>\n"
        "</blockquote>"
        "<blockquote>"
        "<b>⚙️ QUICK ACTIONS</b>\n"
        "Choose a section below to manage your bot.\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        "<i>Tip: use the Back to Panel button inside each section.</i>"
        "</blockquote>"
    )


def _admin_panel_markup():
    """Premium grouped controls using Telegram's supported primary/success/danger styles.
    Callback IDs intentionally remain unchanged. Actual colours depend on Telegram client support.
    """
    markup = InlineKeyboardMarkup(row_width=2)

    # Overview
    markup.row(
        create_primary_button("📊 Statistics", callback_data="admin_stats", icon_custom_emoji_id="5992344826715050001"),
        create_primary_button("👥 User Manager", callback_data="admin_users", icon_custom_emoji_id="5424746868275944727"),
    )
    markup.row(
        create_success_button("📆 Daily Users", callback_data="admin_dau"),
    )

    # Configuration
    markup.row(
        create_primary_button("🔧 API Status", callback_data="admin_api_status", icon_custom_emoji_id="5465637267626271756"),
    )
    markup.row(
        create_success_button("👋 Welcome", callback_data="admin_welcome_manager"),
        create_success_button("🖼 Media Manager", callback_data="admin_addmedia", icon_custom_emoji_id="5008416661569536895"),
    )
    markup.row(
        create_primary_button("🧾 User History", callback_data="admin_user_history"),
        create_success_button("💾 Auto Backup", callback_data="admin_backup"),
    )
    markup.row(
        create_success_button("🎬 Welcome Video", callback_data="admin_welcome_video"),
    )

    # Credits and access management
    markup.row(
        create_success_button("➕ Add Credits", callback_data="admin_addcredits", icon_custom_emoji_id="6048770006810893912"),
        create_success_button("🎁 Add Credits to All", callback_data="admin_add_all_credits"),
    )
    markup.row(
        create_danger_button("➖ Remove Credits", callback_data="admin_removecredits", icon_custom_emoji_id="5370596264205366968"),
    )
    markup.row(
        create_success_button("✅ Unblock User", callback_data="admin_unblock", icon_custom_emoji_id="5339247212012528642"),
        create_danger_button("🚫 Block User", callback_data="admin_block", icon_custom_emoji_id="5372880070115341091"),
    )
    markup.row(
        create_primary_button("👑 Make Admin", callback_data="admin_makeadmin", icon_custom_emoji_id="6219727185708582935"),
        create_danger_button("🗑 Remove Admin", callback_data="admin_removeadmin", icon_custom_emoji_id="5370635893868606590"),
    )

    # Broadcast and operations
    markup.row(
        create_primary_button("📢 Broadcast", callback_data="admin_broadcast_info", icon_custom_emoji_id="5233279094531045380"),
        create_primary_button("📡 BC Channel", callback_data="admin_setbc_info", icon_custom_emoji_id="5246931953751443616"),
    )
    # Editable bot copy — saved in the existing settings collection.
    markup.row(
        create_success_button("📝 Edit Help Text", callback_data="admin_edit_help"),
        create_primary_button("📘 Edit Lookup Guide", callback_data="admin_edit_lookup_guide"),
    )
    markup.row(
        create_primary_button("☎️ Edit Support Text", callback_data="admin_edit_support_text"),
        create_danger_button("♻️ Reset Editable Text", callback_data="admin_reset_editable_text"),
    )
    markup.row(
        create_primary_button("🗂 All Commands", callback_data="acmd_all", icon_custom_emoji_id="5465637267626271756"),
    )
    markup.row(
        create_danger_button("🔄 Reload Bot", callback_data="admin_reload", icon_custom_emoji_id="5370754155793102519"),
    )
    return markup


@bot.message_handler(commands=['admin'])
def admin_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    admin_panel(message)

@bot.message_handler(commands=['stats'])
def stats_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    stats = get_bot_stats()
    msg = f"""
📊 BOT STATISTICS

👑 Total Users: {stats.get('total_users', 0)}
📅 New Today: {stats.get('today_users', 0)}
🟢 Active (24h): {stats.get('active_users', 0)}
📆 Daily Active Users: {stats.get('daily_active_users', 0)}
💰 Total Credits: {stats.get('total_credits', 0)}
⚡ Commands Used: {stats.get('total_commands', 0)}
👥 Total Referrals: {stats.get('total_referrals', 0)}
"""
    send_with_premium(message.chat.id, msg)

@bot.message_handler(commands=['users'])
def users_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    try:
        total   = _col_users.count_documents({})
        admins  = _col_users.count_documents({"is_admin": 1})
        blocked = _col_users.count_documents({"is_blocked": 1})
        msg = f"""
👥 USER STATISTICS

📊 Total Users: {total}
👑 Admins: {admins}
🚫 Blocked: {blocked}
✅ Active: {total - blocked}
"""
        send_with_premium(message.chat.id, msg)
    except Exception as e:
        send_with_premium(message.chat.id, f"❌ Error: {e}")

@bot.message_handler(commands=['add'])
def add_credits_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    parts = message.text.split()
    if len(parts) < 3:
        send_with_premium(message.chat.id, "❌ Use: /add [user_id] [credits]")
        return
    try:
        target_id = int(parts[1])
        amount = int(parts[2])
        if add_credits(target_id, amount):
            new_balance = get_credits(target_id)
            send_with_premium(message.chat.id, f"✅ Added {amount} credits to {target_id}\n💰 New Balance: {new_balance}")
            try:
                send_with_premium(target_id, f"✅ Admin added {amount} credits!\n💰 New Balance: {new_balance}")
            except:
                pass
        else:
            send_with_premium(message.chat.id, "❌ Failed to add credits!")
    except ValueError:
        send_with_premium(message.chat.id, "❌ Invalid user ID or amount!")

@bot.message_handler(commands=['removecredit'])
def remove_credits_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    parts = message.text.split()
    if len(parts) < 3:
        send_with_premium(message.chat.id, "❌ Use: /removecredit [user_id] [credits]")
        return
    try:
        target_id = int(parts[1])
        amount = int(parts[2])
        with db_lock:
            _col_users.update_one({"user_id": target_id}, {"$inc": {"credits": -amount}})
            new_balance = get_credits(target_id)
            send_with_premium(message.chat.id, f"✅ Removed {amount} credits from {target_id}\n💰 New Balance: {new_balance}")
    except ValueError:
        send_with_premium(message.chat.id, "❌ Invalid user ID or amount!")

@bot.message_handler(commands=['gen'])
def gen_code_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    parts = message.text.split()
    if len(parts) < 4:
        send_with_premium(message.chat.id, "❌ Use: /gen [credits] [max_uses] [days]\nExample: /gen 50 10 30")
        return
    try:
        credits = int(parts[1])
        max_uses = int(parts[2])
        days = int(parts[3])
        code = ''.join(random.choices(string.ascii_uppercase + string.digits, k=12))
        expiry_date = (datetime.now() + timedelta(days=days)).strftime("%Y-%m-%d %H:%M:%S")
        success, result = create_redeem_code(code, credits, max_uses, expiry_date, user_id)
        send_with_premium(message.chat.id, result)
    except ValueError:
        send_with_premium(message.chat.id, "❌ Invalid numbers!")

@bot.message_handler(commands=['deletecode'])
def delete_code_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    parts = message.text.split()
    if len(parts) < 2:
        send_with_premium(message.chat.id, "❌ Usage: `/deletecode [code]`\n💡 Use `/allcodes` to see all codes")
        return
    success, result = delete_redeem_code(parts[1].strip().upper(), user_id)
    send_with_premium(message.chat.id, result)

@bot.message_handler(commands=['allcodes'])
def all_codes_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    try:
        docs = list(_col_codes.find({}).sort("_id", -1).limit(30))
        if not docs:
            send_with_premium(message.chat.id, "📋 No redeem codes found!")
            return
        msg = "🎫 REDEEM CODES\n\n"
        for doc in docs:
            status = "✅" if doc.get("is_active", 1) else "❌"
            msg += f"{status} `{doc['code']}`\n   💰 {doc['credits']} credits | Used: {doc.get('used_count',0)}/{doc['max_uses']}\n"
            if doc.get("expiry_date"):
                msg += f"   📅 Expires: {doc['expiry_date'][:10]}\n"
            msg += "\n"
        msg += "\n💡 Each code can be used only ONCE per user!\n💡 Use `/deletecode [code]` to delete a code"
        send_with_premium(message.chat.id, msg, parse_mode='HTML')
    except Exception as e:
        send_with_premium(message.chat.id, f"❌ Error: {e}")

@bot.message_handler(commands=['promote'])
def promote_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    parts = message.text.split()
    if len(parts) < 2:
        send_with_premium(message.chat.id, "❌ Use: /promote [user_id]")
        return
    try:
        target_id = int(parts[1])
        if target_id in ADMIN_IDS:
            send_with_premium(message.chat.id, "❌ Cannot promote main owner!")
            return
        try:
            _col_users.update_one({"user_id": target_id}, {"$set": {"is_admin": 1}})
            _ADMIN_CACHE.delete(target_id)
            send_with_premium(message.chat.id, f"✅ User {target_id} is now an admin!")
            try:
                send_with_premium(target_id, "✅ You have been promoted to admin!")
            except:
                pass
        except Exception:
            send_with_premium(message.chat.id, "❌ Failed to promote user!")
    except ValueError:
        send_with_premium(message.chat.id, "❌ Invalid user ID!")

@bot.message_handler(commands=['demote'])
def demote_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    parts = message.text.split()
    if len(parts) < 2:
        send_with_premium(message.chat.id, "❌ Use: /demote [user_id]")
        return
    try:
        target_id = int(parts[1])
        if target_id in ADMIN_IDS:
            send_with_premium(message.chat.id, "❌ Cannot demote main owner!")
            return
        try:
            _col_users.update_one({"user_id": target_id}, {"$set": {"is_admin": 0}})
            _ADMIN_CACHE.delete(target_id)
            send_with_premium(message.chat.id, f"✅ User {target_id} is no longer an admin!")
            try:
                send_with_premium(target_id, "❌ You have been demoted from admin!")
            except:
                pass
        except Exception:
            send_with_premium(message.chat.id, "❌ Failed to demote user!")
    except ValueError:
        send_with_premium(message.chat.id, "❌ Invalid user ID!")

@bot.message_handler(commands=['searchuser'])
def search_user_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(message.chat.id, "❌ Use: /searchuser [id or username]")
        return
    query = parts[1].strip()
    try:
        if query.isdigit():
            user = _col_users.find_one({"user_id": int(query)})
        else:
            user = _col_users.find_one({"username": {"$regex": re.escape(query), "$options": "i"}})
        if not user:
            send_with_premium(message.chat.id, "❌ User not found!")
            return
        msg = f"""
👤 USER DETAILS

🆔 ID: `{user['user_id']}`
👤 Username: @{user.get('username') or 'N/A'}
📝 Name: {user.get('first_name') or 'N/A'}
💰 Credits: {user.get('credits', 0)}
👑 Admin: {'✅' if user.get('is_admin') == 1 else '❌'}
👥 Referrals: {user.get('referral_count', 0)}
⚡ Commands: {user.get('total_commands', 0)}
🚫 Blocked: {'✅' if user.get('is_blocked') == 1 else '❌'}
📅 Joined: {str(user.get('join_date', 'N/A'))[:19]}
"""
        send_with_premium(message.chat.id, msg, parse_mode='HTML')
    except Exception as e:
        send_with_premium(message.chat.id, f"❌ Error: {e}")

@bot.message_handler(commands=['block'])
def block_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    parts = message.text.split()
    if len(parts) < 2:
        send_with_premium(message.chat.id, "❌ Use: /block [user_id]")
        return
    try:
        target_id = int(parts[1])
        if target_id in ADMIN_IDS:
            send_with_premium(message.chat.id, "❌ Cannot block owner!")
            return
        if block_user_in_db(target_id):
            send_with_premium(message.chat.id, f"✅ User {target_id} has been blocked!")
            try:
                send_with_premium(target_id, f"🚫 BANNED 🚫\n\n❌ YOU HAVE BEEN BANNED ❌\n\n📞 Contact Admin: {OWNER_USERNAME}")
            except:
                pass
        else:
            send_with_premium(message.chat.id, "❌ Failed to block user!")
    except ValueError:
        send_with_premium(message.chat.id, "❌ Invalid user ID!")

@bot.message_handler(commands=['unblock'])
def unblock_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    parts = message.text.split()
    if len(parts) < 2:
        send_with_premium(message.chat.id, "❌ Use: /unblock [user_id]")
        return
    try:
        target_id = int(parts[1])
        if unblock_user_in_db(target_id):
            send_with_premium(message.chat.id, f"✅ User {target_id} has been unblocked!")
            try:
                send_with_premium(target_id, "✅ You have been unblocked! You can use the bot again.")
            except:
                pass
        else:
            send_with_premium(message.chat.id, "❌ Failed to unblock user!")
    except ValueError:
        send_with_premium(message.chat.id, "❌ Invalid user ID!")

@bot.message_handler(commands=['lock'])
def lock_bot_cmd(message):
    global BOT_LOCKED
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    BOT_LOCKED = True
    send_with_premium(message.chat.id, "🔒 BOT LOCKED 🔒\n\n🔐 BOT IS LOCKED BY ADMIN\n\n⏳ Only admins can use the bot now")

@bot.message_handler(commands=['unlock'])
def unlock_bot_cmd(message):
    global BOT_LOCKED
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    BOT_LOCKED = False
    send_with_premium(message.chat.id, "🔓 BOT UNLOCKED 🔓\n\n✅ BOT IS NOW UNLOCKED\n\n🌟 All users can now use the bot")

@bot.message_handler(commands=['broadcast'])
def broadcast_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return

    # ── mode detection ──────────────────────────────────────────
    # FORWARD mode  : /broadcast  (reply to any message)
    #   → bot.forward_message() — preserves "Forwarded from X" header
    # TEXT mode     : /broadcast <text>  (no reply)
    #   → send_with_premium() — plain text blast
    # ───────────────────────────────────────────────────────────

    use_forward   = False
    forward_from_chat = None
    forward_msg_id    = None
    broadcast_msg     = None

    if message.reply_to_message:
        replied = message.reply_to_message
        use_forward       = True
        forward_from_chat = replied.chat.id
        forward_msg_id    = replied.message_id
    else:
        parts = message.text.split(maxsplit=1)
        if len(parts) < 2:
            send_with_premium(
                message.chat.id,
                "❌ Use:\n"
                "• <b>Reply</b> to any msg + <code>/broadcast</code> — forwards that msg (with Forwarded From tag)\n"
                "• <code>/broadcast &lt;text&gt;</code> — sends plain text blast",
                parse_mode="HTML"
            )
            return
        broadcast_msg = parts[1]

    # ── collect targets ─────────────────────────────────────────
    all_chats = set()
    try:
        for doc in _col_users.find({}, {"user_id": 1}):
            all_chats.add(doc["user_id"])
    except Exception:
        pass

    try:
        for gcid in get_all_group_chats():
            all_chats.add(gcid)
    except:
        pass

    success_count = 0
    fail_count    = 0
    total         = len(all_chats)
    progress_msg  = send_with_premium(
        message.chat.id,
        f"📢 Broadcast started...\n\n📊 Total: {total}\n⏳ Sending..."
    )

    for idx, chat_id in enumerate(all_chats, 1):
        try:
            if use_forward:
                # forward preserves original sender / channel header
                bot.forward_message(
                    chat_id=chat_id,
                    from_chat_id=forward_from_chat,
                    message_id=forward_msg_id,
                    disable_notification=True,
                )
            else:
                send_with_premium(chat_id, broadcast_msg, disable_notification=True)
            success_count += 1
        except Exception:
            fail_count += 1

        if idx % 10 == 0:
            try:
                progress_text = f"📢 Broadcast in progress...\n\n📊 Total: {total}\n✅ Sent: {success_count}\n❌ Failed: {fail_count}\n⏳ Progress: {idx}/{total}"
                edit_with_premium(message.chat.id, progress_msg.message_id, progress_text)
            except:
                pass
        time.sleep(0.1)

@bot.message_handler(commands=['broadcastbtn'])
def broadcast_btn_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return

    if not message.reply_to_message:
        send_with_premium(
            message.chat.id,
            "⭐ Reply to the message you want to broadcast.\n\n"
            "Use:\n"
            "<code>/broadcastbtn Button Text | https://example.com | success | EMOJI_ID</code>\n\n"
            "Styles: primary (blue), success (green), danger (red)\n"
            "Style and premium emoji ID are optional.",
            parse_mode="HTML"
        )
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(
            message.chat.id,
            "❌ Provide button details:\n\n"
            "<code>/broadcastbtn Button Text | https://example.com | success | EMOJI_ID</code>",
            parse_mode="HTML"
        )
        return

    # ── parse "Button Text | URL | style | emoji_id" ──
    args = [p.strip() for p in parts[1].split("|")]
    if len(args) < 2:
        send_with_premium(
            message.chat.id,
            "❌ Invalid format. Use:\n\n"
            "<code>/broadcastbtn Button Text | https://example.com | success | EMOJI_ID</code>",
            parse_mode="HTML"
        )
        return

    btn_text = args[0].strip()
    btn_url  = args[1].strip()

    if not btn_text or not btn_url:
        send_with_premium(message.chat.id, "❌ Button text and URL cannot be empty!")
        return
    if not (btn_url.startswith("http://") or btn_url.startswith("https://") or btn_url.startswith("tg://")):
        send_with_premium(message.chat.id, "❌ URL must start with http://, https:// or tg://")
        return

    style = args[2].strip().lower() if len(args) > 2 and args[2].strip() else "primary"
    if style not in ("primary", "success", "danger"):
        style = "primary"

    emoji_id = args[3].strip() if len(args) > 3 and args[3].strip() else None

    btn_kwargs = {"url": btn_url}
    if emoji_id:
        btn_kwargs["icon_custom_emoji_id"] = emoji_id

    if style == "success":
        btn = create_success_button(btn_text, **btn_kwargs)
    elif style == "danger":
        btn = create_danger_button(btn_text, **btn_kwargs)
    else:
        btn = create_primary_button(btn_text, **btn_kwargs)

    markup = InlineKeyboardMarkup()
    markup.add(btn)

    replied            = message.reply_to_message
    forward_from_chat  = replied.chat.id
    forward_msg_id     = replied.message_id

    # ── collect targets ──────────────────────────────────────────
    all_chats = set()
    try:
        for doc in _col_users.find({}, {"user_id": 1}):
            all_chats.add(doc["user_id"])
    except Exception:
        pass
    try:
        for gcid in get_all_group_chats():
            all_chats.add(gcid)
    except Exception:
        pass

    success_count = 0
    fail_count    = 0
    total         = len(all_chats)
    progress_msg  = send_with_premium(
        message.chat.id,
        f"📢 Broadcast (with button) started...\n\n📊 Total: {total}\n⏳ Sending..."
    )

    # try to copy the replied message's content + attach button.
    # copy_message preserves media/text without the "Forwarded from" header,
    # and lets us attach a reply_markup — forward_message cannot attach buttons.
    for idx, chat_id in enumerate(all_chats, 1):
        try:
            bot.copy_message(
                chat_id=chat_id,
                from_chat_id=forward_from_chat,
                message_id=forward_msg_id,
                reply_markup=markup,
                disable_notification=True,
            )
            success_count += 1
        except Exception:
            fail_count += 1

        if idx % 10 == 0:
            try:
                progress_text = (
                    f"📢 Broadcast (with button) in progress...\n\n"
                    f"📊 Total: {total}\n✅ Sent: {success_count}\n❌ Failed: {fail_count}\n"
                    f"⏳ Progress: {idx}/{total}"
                )
                edit_with_premium(message.chat.id, progress_msg.message_id, progress_text)
            except Exception:
                pass
        time.sleep(0.1)

    try:
        final_text = (
            f"✅ <b>Broadcast (with button) Complete!</b>\n\n"
            f"📊 Total: {total}\n✅ Sent: {success_count}\n❌ Failed: {fail_count}"
        )
        edit_with_premium(message.chat.id, progress_msg.message_id, final_text)
    except Exception:
        pass

@bot.message_handler(commands=['uptime'])
def uptime_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    uptime = datetime.now() - BOT_START_TIME
    msg = f"""
🕐 BOT UPTIME

📅 Days: {uptime.days}
⏰ Hours: {uptime.seconds // 3600}
⏱️ Minutes: {(uptime.seconds % 3600) // 60}
⚡ Seconds: {uptime.seconds % 60}
"""
    send_with_premium(message.chat.id, msg)

@bot.message_handler(commands=['commands'])
def commands_stats_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    try:
        top_users = list(_col_users.find(
            {"total_commands": {"$gt": 0}},
            {"user_id": 1, "username": 1, "total_commands": 1}
        ).sort("total_commands", -1).limit(10))
        agg = list(_col_users.aggregate([{"$group": {"_id": None, "total": {"$sum": "$total_commands"}}}]))
        total_commands = agg[0]["total"] if agg else 0
        msg = "📊 COMMAND USAGE STATS\n\n"
        msg += f"📈 Total Commands: {total_commands}\n\n🏆 TOP USERS:\n"
        for i, u in enumerate(top_users, 1):
            name = f"@{u['username']}" if u.get("username") else str(u["user_id"])
            msg += f"{i}. {name}: {u['total_commands']} commands\n"
        send_with_premium(message.chat.id, msg, parse_mode='HTML')
    except Exception as e:
        send_with_premium(message.chat.id, f"❌ Error: {e}")

@bot.message_handler(commands=['apistatus'])
def apistatus_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    parts = message.text.split(maxsplit=2)
    if len(parts) < 2:
        send_with_premium(message.chat.id, """❌ Usage: `/apistatus [command] [status] [message]`""", parse_mode='HTML')
        return

    command = parts[1].lower()
    if command not in API_STATUS:
        send_with_premium(message.chat.id, f"❌ Invalid command!")
        return

    if len(parts) >= 3:
        status_parts = parts[2].split(maxsplit=1)
        status = status_parts[0].lower()
        msg = status_parts[1] if len(status_parts) > 1 else None

        if status == 'working':
            set_api_status(command, True, None)
            send_with_premium(message.chat.id, f"✅ API `/{command}` is now marked as WORKING")
        elif status == 'fixing':
            set_api_status(command, False, msg)
            send_with_premium(message.chat.id, f"⚠️ API `/{command}` is now marked as FIXING")

# _resolve_channel_from_message removed — /addc now uses chat_id + link directly


def add_force_join_channel_extended(url, username, admin_id, is_private=False, join_by_request=False):
    """Extended version that also stores private/join_request flags."""
    try:
        _col_channels.insert_one({
            "url": url,
            "username": username,
            "enabled": 1,
            "is_private": int(is_private),
            "join_by_request": int(join_by_request),
            "added_by": admin_id,
            "added_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        })
        PROMOTION_CHANNELS.append({
            "url": url,
            "username": username,
            "enabled": True,
            "is_private": is_private,
            "join_by_request": join_by_request,
        })
        _col_media_set.update_one({"setting_key": "force_join_initialized"}, {"$set": {"initialized": True}}, upsert=True)
        return True, "Channel added successfully!"
    except DuplicateKeyError:
        return False, "Channel already exists!"
    except Exception as e:
        return False, f"Error: {str(e)}"


# pending addc state: {user_id: step}
ADDC_STATE = {}
ADDC_LINK_CACHE = {}   # {token: {chat_id, link, is_private}} — holds exact admin-provided link

@bot.message_handler(commands=['addc'])
def add_channel_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    ADDC_STATE[user_id] = {"step": "chat_id"}
    send_with_premium(
        message.chat.id,
        "📋 <b>Step 1/2</b> — Send the <b>Chat ID</b>\n\n"
        "Example: <code>-1001234567890</code>\n\n"
        "To get Chat ID, forward a post from that channel to @userinfobot",
        parse_mode='HTML'
    )

@bot.message_handler(func=lambda m: (
    m.from_user and
    m.from_user.id in ADDC_STATE and
    ADDC_STATE[m.from_user.id].get("step") == "chat_id" and
    m.text and not m.text.startswith('/')
))
def addc_step_chatid(message):
    user_id = message.from_user.id
    raw = message.text.strip()
    try:
        chat_id_num = int(raw)
    except ValueError:
        send_with_premium(message.chat.id,
            "❌ Invalid Chat ID. Send a number like <code>-1001234567890</code>",
            parse_mode='HTML')
        return
    ADDC_STATE[user_id]["chat_id"] = chat_id_num
    ADDC_STATE[user_id]["step"]    = "link"
    send_with_premium(
        message.chat.id,
        "🔗 <b>Step 2/2</b> — Send the <b>Channel Link</b>\n\n"
        "Examples:\n"
        "• Public: <code>https://t.me/mychannel</code>\n"
        "• Private: <code>https://t.me/+abcXYZ123</code>",
        parse_mode='HTML'
    )

@bot.message_handler(func=lambda m: (
    m.from_user and
    m.from_user.id in ADDC_STATE and
    ADDC_STATE[m.from_user.id].get("step") == "link" and
    m.text and not m.text.startswith('/')
))
def addc_step_link(message):
    user_id = message.from_user.id
    link    = message.text.strip()
    state   = ADDC_STATE.pop(user_id, {})
    chat_id_num = state.get("chat_id")

    if not chat_id_num:
        send_with_premium(message.chat.id, "❌ Session expired. Run /addc again.")
        return

    if not link.startswith('http') and not link.startswith('t.me') and not link.startswith('@'):
        send_with_premium(message.chat.id, "❌ Invalid link. Send a valid t.me link.")
        return

    # detect private invite link (+hash / joinchat) vs public
    is_private = '+' in link or 'joinchat' in link

    # store the EXACT link the admin gave — this is authoritative, never regenerate it
    token = hashlib.md5(f"{user_id}{chat_id_num}{link}{time.time()}".encode()).hexdigest()[:10]
    ADDC_LINK_CACHE[token] = {
        "chat_id": chat_id_num,
        "link": link,
        "is_private": is_private,
    }

    markup = InlineKeyboardMarkup()
    markup.row(
        create_success_button("🌍 Normal Join",
            callback_data=f"addc_mode_{token}_0"),
        create_primary_button("🔐 Request to Join",
            callback_data=f"addc_mode_{token}_1")
    )
    markup.add(create_danger_button("❌ Cancel", callback_data="addc_skip"))

    send_with_premium(
        message.chat.id,
        f"⚙️ <b>Select Join Mode</b>\n\n"
        f"🔗 <b>Link</b>: <code>{link}</code>\n"
        f"🆔 <b>Chat ID</b>: <code>{chat_id_num}</code>\n\n"
        f"🌍 <b>Normal Join</b> — bot verifies membership\n"
        f"🔐 <b>Request to Join</b> — user sends request, bot lets through instantly",
        reply_markup=markup,
        parse_mode='HTML'
    )




@bot.chat_join_request_handler()
def handle_join_request(update):
    """
    Fires when a user sends a join request to any channel where the bot is admin.
    We record it in JOIN_REQUESTS_SENT so check_subscription passes for request-mode channels.
    Credit is NOT deducted here — that happens when user runs a command.
    """
    try:
        user_id  = update.from_user.id
        chat_id  = update.chat.id
        username = update.chat.username or str(chat_id)

        # record in memory
        if user_id not in JOIN_REQUESTS_SENT:
            JOIN_REQUESTS_SENT[user_id] = set()
        JOIN_REQUESTS_SENT[user_id].add(username)
        JOIN_REQUESTS_SENT[user_id].add(str(chat_id))   # also store numeric id

        # persist so a restart does not ask the user to request again
        try:
            for ref in {username, str(chat_id)}:
                _col_join_req.update_one(
                    {"user_id": user_id, "chat_ref": ref},
                    {"$setOnInsert": {"at": datetime.now().strftime("%Y-%m-%d %H:%M:%S")}},
                    upsert=True)
        except Exception as e_db:
            print(f"[JOIN_REQUEST] db save error: {e_db}")

        print(f"[JOIN_REQUEST] user {user_id} → channel {username} ({chat_id})")
    except Exception as e:
        print(f"[JOIN_REQUEST] error: {e}")

@bot.message_handler(commands=['removec'])
def remove_channel_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(message.chat.id, "❌ Usage: `/removec [channel_url_or_username]`", parse_mode='HTML')
        return
    success, result = remove_force_join_channel(parts[1].strip(), user_id)
    send_with_premium(message.chat.id, result)

@bot.message_handler(commands=['listc'])
def list_channels_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    channels = list_force_join_channels()
    if not channels:
        send_with_premium(message.chat.id, "📋 No force join channels configured!")
        return
    msg = "\n📢 FORCE JOIN CHANNELS\n\n\n"
    for ch in channels:
        ch_id, url, username, enabled, added_by, added_date = ch
        msg += f"ID: `{ch_id}`\n📢 {url}\n👤 @{username}\n📊 {'✅ Active' if enabled else '❌ Disabled'}\n\n"
    send_with_premium(message.chat.id, msg, parse_mode='HTML')

@bot.message_handler(commands=['exportusers'])
def export_users_cmd(message):
    """Post a readable card for every user into the archive channel."""
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    if not getattr(_store, "sink", None) or not _store.sink.enabled:
        send_with_premium(message.chat.id,
                          "❌ Archive channel not configured.\n"
                          "Set TG_STORE_CHANNEL_ID (bot must be admin there).")
        return
    total = _store["users"].count_documents({})
    send_with_premium(message.chat.id, f"📤 Exporting {total} user cards to the channel...")

    def _run(chat_id):
        try:
            posted = _store.export_collection("users", pace=1.0)
            send_with_premium(chat_id, f"✅ Export finished — {posted} message(s) sent to the channel.")
        except Exception as e:
            logger.error(f"exportusers error: {e}")
            send_with_premium(chat_id, f"❌ Export failed: {e}")

    _BG_EXECUTOR.submit(_run, message.chat.id)


@bot.message_handler(commands=['exportuser'])
def export_one_user_cmd(message):
    """Post one user's card into the archive channel by user id."""
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    if not getattr(_store, "sink", None) or not _store.sink.enabled:
        send_with_premium(message.chat.id, "❌ Archive channel not configured.")
        return
    parts = message.text.split(maxsplit=1)
    if len(parts) < 2 or not parts[1].strip().isdigit():
        send_with_premium(message.chat.id, "❌ Usage: /exportuser <user_id>")
        return
    target = int(parts[1].strip())
    doc = _col_users.find_one({"user_id": target})
    if not doc:
        send_with_premium(message.chat.id, "❌ No such user.")
        return
    card = render_user_card(doc, None)
    if _store.sink.post_chunk(card):
        send_with_premium(message.chat.id, "✅ Card sent to the channel.")
    else:
        send_with_premium(message.chat.id, "❌ Channel post failed.")


@bot.message_handler(commands=['api'])
def list_apis_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    apis = list_all_apis()
    msg = "\n🔗 API ENDPOINTS\n\n\n"
    for api in apis:
        safe_endpoint = _redact(api.get("endpoint", ""))
        msg += f"📌 **/{api['command']}**\n   `{safe_endpoint[:80]}...`\n\n"
    send_with_premium(message.chat.id, msg, parse_mode='HTML')

@bot.message_handler(commands=['apic'])
def change_api_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    parts = message.text.split(maxsplit=2)
    if len(parts) < 3:
        send_with_premium(message.chat.id, """❌ Usage: `/apic [command] [api_url]`""", parse_mode='HTML')
        return
    command = parts[1].strip().lower().replace('/', '')
    api_url = parts[2].strip()
    success, result = set_api_endpoint(command, api_url, user_id)
    send_with_premium(message.chat.id, result)

@bot.message_handler(commands=['lockf'])
def lock_force_join_cmd(message):
    global FORCE_JOIN_ENABLED
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    FORCE_JOIN_ENABLED = False
    send_with_premium(message.chat.id, "🔓 FORCE JOIN DISABLED 🔓")

@bot.message_handler(commands=['unlockf'])
def unlock_force_join_cmd(message):
    global FORCE_JOIN_ENABLED
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    FORCE_JOIN_ENABLED = True
    send_with_premium(message.chat.id, "🔒 FORCE JOIN ENABLED 🔒")

admin_adding_media = {}

@bot.message_handler(commands=['myid'])
def show_my_telegram_id(message):
    uid = message.from_user.id if message.from_user else 0
    status = 'ADMIN' if is_admin(uid) else 'NOT IN ADMIN_IDS'
    send_with_premium(message.chat.id,
        f"🆔 Your Telegram user ID: <code>{uid}</code>\nAccess: <b>{status}</b>\n\nBot admin status in a group does not automatically make your personal account a bot admin.",
        parse_mode='HTML')

@bot.message_handler(commands=['addvideo'])
def add_video_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    admin_adding_media[user_id] = {"type": "video", "files": []}
    send_with_premium(message.chat.id, "🎬 **BULK VIDEO UPLOAD MODE**\n\nSend me videos and send /done when finished.", parse_mode='HTML')

@bot.message_handler(commands=['addphoto'])
def add_photo_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    admin_adding_media[user_id] = {"type": "photo", "files": []}
    send_with_premium(message.chat.id, "🖼️ **BULK PHOTO UPLOAD MODE**\n\nSend me photos and send /done when finished.", parse_mode='HTML')

@bot.message_handler(commands=['done'])
def done_adding_media(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        return
    if user_id not in admin_adding_media:
        send_with_premium(message.chat.id, "❌ No active media session!")
        return
    state = admin_adding_media[user_id]
    files = state["files"]
    media_type = state["type"]
    added = 0
    for idx, file_id in enumerate(files, 1):
        if media_type == "video":
            add_video(file_id, f"Video {idx}", user_id)
        else:
            add_photo(file_id, f"Photo {idx}", user_id)
        added += 1
    del admin_adding_media[user_id]
    send_with_premium(message.chat.id, f"✅ Added {added} {media_type}(s) successfully!")

@bot.message_handler(commands=['cancel'])
def cancel_media_add(message):
    user_id = message.from_user.id
    if user_id in admin_adding_media:
        del admin_adding_media[user_id]
        send_with_premium(message.chat.id, "❌ Cancelled.")

@bot.message_handler(
    content_types=['video', 'photo'],
    func=lambda m: bool(m.from_user and m.from_user.id in admin_adding_media)
)
def handle_bulk_media(message):
    user_id = message.from_user.id
    if not is_admin(user_id) or user_id not in admin_adding_media:
        return
    state = admin_adding_media[user_id]
    if message.video and state["type"] == "video":
        state["files"].append(message.video.file_id)
        send_with_premium(message.chat.id, f"✅ Video #{len(state['files'])} added!")
    elif message.photo and state["type"] == "photo":
        state["files"].append(message.photo[-1].file_id)
        send_with_premium(message.chat.id, f"✅ Photo #{len(state['files'])} added!")

@bot.message_handler(commands=['delvideo'])
def del_video_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        return
    videos = get_all_videos()
    if not videos:
        send_with_premium(message.chat.id, "📋 No videos found!")
        return
    markup = InlineKeyboardMarkup(row_width=1)
    for vid in videos[:20]:
        markup.add(InlineKeyboardButton(f"🗑️ {vid[2][:30]} (ID: {vid[0]})", callback_data=f"delvid_{vid[0]}"))
    send_with_premium(message.chat.id, "🎬 Select video to delete:", reply_markup=markup)

@bot.message_handler(commands=['delphoto'])
def del_photo_cmd(message):
    user_id = message.from_user.id
    if not is_admin(user_id):
        return
    photos = get_all_photos()
    if not photos:
        send_with_premium(message.chat.id, "📋 No photos found!")
        return
    markup = InlineKeyboardMarkup(row_width=1)
    for photo in photos[:20]:
        markup.add(InlineKeyboardButton(f"🗑️ {photo[2][:30]} (ID: {photo[0]})", callback_data=f"delphoto_{photo[0]}"))
    send_with_premium(message.chat.id, "🖼️ Select photo to delete:", reply_markup=markup)

@bot.message_handler(commands=['listvideos'])
def list_videos_cmd(message):
    if not is_admin(message.from_user.id):
        return
    videos = get_all_videos()
    send_with_premium(message.chat.id, f"🎬 Total Videos: {len(videos)}")

@bot.message_handler(commands=['listphotos'])
def list_photos_cmd(message):
    if not is_admin(message.from_user.id):
        return
    photos = get_all_photos()
    send_with_premium(message.chat.id, f"🖼️ Total Photos: {len(photos)}")

@bot.message_handler(commands=['setmode'])
def set_mode_cmd(message):
    if not is_admin(message.from_user.id):
        return
    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        return
    success, result = set_media_mode(parts[1].strip().lower(), message.from_user.id)
    send_with_premium(message.chat.id, result)




# ============================================================
# V2 SECURITY & PERMISSIONS — scoped to the newer management suite.
# Legacy admin commands retain their existing access rules for compatibility.
# ============================================================
def _sec_roles_init():
    with _clone_db() as conn:
        conn.execute("""CREATE TABLE IF NOT EXISTS admin_roles (
            user_id INTEGER PRIMARY KEY,
            role TEXT NOT NULL CHECK(role IN ('super_admin','moderator')),
            assigned_by INTEGER NOT NULL,
            assigned_at TEXT NOT NULL
        )""")


def _sec_role(uid):
    uid = int(uid)
    if uid in ADMIN_IDS:
        return 'owner'
    try:
        _sec_roles_init()
        with _clone_db() as conn:
            row = conn.execute('SELECT role FROM admin_roles WHERE user_id=?', (uid,)).fetchone()
        if row:
            return str(row['role'])
    except Exception:
        pass
    # Backward compatibility: existing legacy admins are treated as super admins.
    return 'super_admin' if is_admin(uid) else 'none'


def _sec_can(uid, permission):
    role = _sec_role(uid)
    rules = {
        'view_system': {'owner','super_admin','moderator'},
        'backup': {'owner','super_admin'},
        'maintenance': {'owner'},
        'restart': {'owner'},
        'clone_control': {'owner','super_admin'},
        'security_keys': {'owner'},
        'audit': {'owner','super_admin'},
    }
    return role in rules.get(permission, {'owner'})


def _sec_roles_text():
    _sec_roles_init()
    lines = ['<blockquote><b>🛡️ ADMIN ROLES & PERMISSIONS</b>',
             'Owner: full control · Super Admin: system/backup/clone operations · Moderator: view-only system status',
             '', '<b>Configured roles</b>']
    with _clone_db() as conn:
        rows = list(conn.execute('SELECT user_id,role,assigned_by,assigned_at FROM admin_roles ORDER BY role,user_id'))
    for uid in ADMIN_IDS:
        lines.append(f'👑 <code>{int(uid)}</code> — Owner')
    for row in rows:
        lines.append(f'• <code>{int(row["user_id"])}</code> — {row["role"].replace("_", " ").title()}')
    if not rows:
        lines.append('No additional role assignments. Existing legacy admins retain Super Admin access until explicitly assigned a role.')
    lines += ['', 'Use Add / Change Role and send: <code>USER_ID super_admin</code> or <code>USER_ID moderator</code>.',
              'Use Remove Role to send a USER_ID. Owner accounts cannot be changed here.', '</blockquote>']
    return '\n'.join(lines)


def _sec_roles_keyboard():
    kb = InlineKeyboardMarkup(row_width=2)
    kb.add(InlineKeyboardButton('➕ Add / Change Role', callback_data='secrole_add', style='success'),
           InlineKeyboardButton('➖ Remove Role', callback_data='secrole_remove', style='danger'))
    kb.add(InlineKeyboardButton('🔄 Refresh', callback_data='secrole_home', style='primary'),
           InlineKeyboardButton('⬅️ Back to Admin', callback_data='secrole_back', style='primary'))
    return kb


_sec_roles_init()


# ============================================================
# SERVER & SYSTEM MANAGER — master-admin-only operational tools
# ============================================================
_SYSTEM_LOG_CANDIDATES = ("bot.log", "logs/bot.log", "whoisshown.log")
_SYSTEM_PENDING_RESTORE = os.path.abspath("pending_restore.sqlite3")


def _sysmgr_is_maintenance():
    try:
        return bool((_col_media_set.find_one({"setting_key": "system_maintenance"}) or {}).get("enabled"))
    except Exception:
        return False


def _sysmgr_db_health():
    try:
        with _store._lock:
            result = _store._conn.execute("PRAGMA quick_check").fetchone()
        return str(result[0]) if result else "no result"
    except Exception as exc:
        return "ERROR: " + str(exc)[:120]


def _sysmgr_storage_text():
    db_path = os.path.abspath(getattr(_store, "db_path", TG_STORE_DB_PATH))
    roots = [os.path.dirname(db_path) or "."]
    if os.path.isdir("/var/data"):
        roots.append("/var/data")
    lines = ["<blockquote><b>💽 STORAGE USAGE</b>"]
    for root in dict.fromkeys(roots):
        try:
            usage = shutil.disk_usage(root)
            lines.append(f"{_html.escape(root)} · free <code>{usage.free/1024**3:.2f} GB</code> / total <code>{usage.total/1024**3:.2f} GB</code>")
        except Exception as exc:
            lines.append(f"{_html.escape(root)} · unavailable: {_html.escape(str(exc)[:80])}")
    try:
        size = os.path.getsize(db_path)
        lines.append(f"Main SQLite DB: <code>{size/1024**2:.2f} MB</code>")
    except OSError:
        lines.append("Main SQLite DB: <i>file size unavailable</i>")
    try:
        total = 0
        for root, dirs, files in os.walk(CLONE_RUNTIME_DIR):
            dirs[:] = [d for d in dirs if d not in {".git", "__pycache__"}]
            for name in files:
                try: total += os.path.getsize(os.path.join(root, name))
                except OSError: pass
        lines.append(f"Clone runtime files: <code>{total/1024**2:.2f} MB</code>")
    except Exception:
        pass
    lines.append("</blockquote>")
    return "\n".join(lines)


def _sysmgr_error_log_text():
    found = next((x for x in _SYSTEM_LOG_CANDIDATES if os.path.isfile(x)), None)
    if not found:
        return ("<blockquote><b>🧾 ERROR LOG</b>\nNo local rotating log file was found. "
                "This deployment currently writes some errors to the process console; view Render/VPS service logs for the full stream.</blockquote>")
    try:
        with open(found, "r", encoding="utf-8", errors="replace") as fh:
            tail = fh.readlines()[-25:]
        body = "".join(tail).strip() or "(log file is empty)"
        return "<blockquote><b>🧾 ERROR LOG · LAST 25 LINES</b>\n<pre>" + _html.escape(body[-3200:]) + "</pre></blockquote>"
    except Exception as exc:
        return f"Could not read log: <code>{_html.escape(str(exc)[:150])}</code>"


def _sysmgr_status_text():
    cfg = _col_media_set.find_one({"setting_key": "auto_backup_config"}) or {}
    platform = "Render" if os.environ.get("RENDER") or os.environ.get("RENDER_SERVICE_ID") else "VPS / other host"
    uptime = str(datetime.now() - BOT_START_TIME).split(".")[0]
    return ("<blockquote><b>🖥️ SERVER & SYSTEM MANAGER</b>\n"
            f"Platform detected: <b>{platform}</b>\n"
            f"Master process: <b>{'clone' if CLONE_INSTANCE else 'running'}</b> · PID <code>{os.getpid()}</code>\n"
            f"Uptime: <code>{uptime}</code>\n"
            f"Database: <b>{_html.escape(_sysmgr_db_health())}</b>\n"
            f"Maintenance mode: <b>{'ON' if _sysmgr_is_maintenance() else 'OFF'}</b>\n"
            f"Auto backup: <b>{'ON' if cfg.get('enabled') else 'OFF'}</b> · target <code>{_html.escape(str(cfg.get('chat_id') or 'not set'))}</code>\n"
            "<i>Host status reflects this running process; Render dashboard/deploy state is not available without Render API credentials.</i></blockquote>")


def _sysmgr_keyboard():
    kb = InlineKeyboardMarkup(row_width=2)
    kb.add(InlineKeyboardButton("🔄 Refresh", callback_data="sysmgr_refresh", style="primary"),
           InlineKeyboardButton("🩺 DB Health", callback_data="sysmgr_db", style="primary"))
    kb.add(InlineKeyboardButton("💽 Storage", callback_data="sysmgr_storage", style="primary"),
           InlineKeyboardButton("🧾 Error Logs", callback_data="sysmgr_logs", style="primary"))
    kb.add(InlineKeyboardButton("💾 Backup Now", callback_data="sysmgr_backup", style="success"),
           InlineKeyboardButton("♻️ Restore Guide", callback_data="sysmgr_restore", style="primary"))
    kb.add(InlineKeyboardButton("🛠 Maintenance ON/OFF", callback_data="sysmgr_maintenance", style="danger"),
           InlineKeyboardButton("🔄 Restart Master", callback_data="sysmgr_restart_confirm", style="danger"))
    kb.add(InlineKeyboardButton("⬅️ Back to Admin", callback_data="admin_panel", style="primary"))
    return kb


@bot.callback_query_handler(func=lambda call: bool(call.data and call.data.startswith('secrole_')))
def _secrole_callbacks(call):
    uid = call.from_user.id
    if not call.message or call.message.chat.type != 'private' or uid not in ADMIN_IDS or CLONE_INSTANCE:
        bot.answer_callback_query(call.id, 'Only the configured owner can manage roles.', show_alert=True)
        return
    try:
        if call.data == 'secrole_back':
            bot.answer_callback_query(call.id)
            _show_admin_reply_page(call.message.chat.id, 0)
            return
        if call.data == 'secrole_add':
            ADMIN_STATE[uid] = {'action':'secrole_add'}
            bot.answer_callback_query(call.id, 'Send: USER_ID super_admin OR USER_ID moderator')
            bot.send_message(call.message.chat.id,
                'Send a Telegram numeric user ID and role, for example:\n<code>123456789 moderator</code>\n/cancel to abort.',
                parse_mode='HTML', reply_markup=_admin_back_kb())
            return
        if call.data == 'secrole_remove':
            ADMIN_STATE[uid] = {'action':'secrole_remove'}
            bot.answer_callback_query(call.id, 'Send the user ID to remove')
            bot.send_message(call.message.chat.id, 'Send the numeric USER_ID to remove its explicit role. Owner accounts cannot be changed.\n/cancel to abort.', reply_markup=_admin_back_kb())
            return
        if call.data == 'secrole_home':
            bot.edit_message_text(_sec_roles_text(), call.message.chat.id, call.message.message_id,
                                  parse_mode='HTML', reply_markup=_sec_roles_keyboard())
            bot.answer_callback_query(call.id, 'Roles refreshed')
            return
        bot.answer_callback_query(call.id, 'Unknown role action', show_alert=True)
    except Exception as exc:
        bot.answer_callback_query(call.id, str(exc)[:180], show_alert=True)


@bot.callback_query_handler(func=lambda call: bool(call.data and call.data.startswith("sysmgr_")))
def _sysmgr_callbacks(call):
    uid = call.from_user.id
    if not call.message or call.message.chat.type != "private" or not _sec_can(uid, "view_system") or CLONE_INSTANCE:
        bot.answer_callback_query(call.id, "System manager access denied.", show_alert=True)
        return
    data = call.data
    chat_id, msg_id = call.message.chat.id, call.message.message_id
    try:
        required = {"sysmgr_backup":"backup", "sysmgr_maintenance":"maintenance", "sysmgr_restart_confirm":"restart", "sysmgr_restart_yes":"restart"}.get(data)
        if required and not _sec_can(uid, required):
            bot.answer_callback_query(call.id, "Your role cannot perform this operation.", show_alert=True)
            return
        if data == "sysmgr_refresh":
            out = _sysmgr_status_text()
        elif data == "sysmgr_db":
            out = ("<blockquote><b>🩺 DATABASE HEALTH CHECK</b>\n"
                   f"SQLite PRAGMA quick_check: <code>{_html.escape(_sysmgr_db_health())}</code>\n"
                   f"Database path: <code>{_html.escape(os.path.abspath(_store.db_path))}</code>\n"
                   "This is a read-only integrity check.</blockquote>")
        elif data == "sysmgr_storage":
            out = _sysmgr_storage_text()
        elif data == "sysmgr_logs":
            out = _sysmgr_error_log_text()
        elif data == "sysmgr_backup":
            _admin_backup_now(chat_id, uid)
            bot.answer_callback_query(call.id, "Backup sent to configured group (or this chat if no group is set).")
            return
        elif data == "sysmgr_restore":
            out = ("<blockquote><b>♻️ SAFE BACKUP RESTORE</b>\n"
                   "Restore is deliberately not a one-tap live replacement. Stop the service first, keep a copy of the current DB, validate the backup with SQLite integrity_check, then replace the configured TG_STORE_DB_PATH and restart.\n"
                   f"Current DB path: <code>{_html.escape(os.path.abspath(_store.db_path))}</code>\n"
                   "A live overwrite could corrupt active writes. Use the backup file from your private Telegram backup group.</blockquote>")
        elif data == "sysmgr_maintenance":
            old = _sysmgr_is_maintenance()
            _col_media_set.update_one({"setting_key": "system_maintenance"},
                {"$set": {"enabled": not old, "updated_at": datetime.now().isoformat(), "updated_by": uid}}, upsert=True)
            _admin_audit("maintenance_toggle", uid, "enabled" if not old else "disabled")
            out = ("<blockquote><b>🛠 MAINTENANCE FLAG UPDATED</b>\n"
                   f"Maintenance flag is now <b>{'ON' if not old else 'OFF'}</b>.\n"
                   "<i>Important: this flag is recorded and shown in the system dashboard; it does not yet block every user handler in this legacy bot.</i></blockquote>")
        elif data == "sysmgr_restart_confirm":
            kb = InlineKeyboardMarkup(row_width=2)
            kb.add(InlineKeyboardButton("⚠️ Confirm Restart", callback_data="sysmgr_restart_yes", style="danger"),
                   InlineKeyboardButton("Cancel", callback_data="sysmgr_refresh", style="primary"))
            bot.edit_message_text("<blockquote><b>⚠️ RESTART MASTER BOT?</b>\nThe master process will disconnect briefly and should be relaunched by the process runner. Clone processes may also be affected by host restart. Confirm only if safe.</blockquote>", chat_id, msg_id, parse_mode="HTML", reply_markup=kb)
            bot.answer_callback_query(call.id)
            return
        elif data == "sysmgr_restart_yes":
            bot.answer_callback_query(call.id, "Restarting master process…")
            bot.send_message(chat_id, "🔄 Master restart requested. The bot will reconnect if the host process manager supports restart-on-exit.")
            def _sysmgr_restart():
                time.sleep(1.2)
                try: bot.stop_polling()
                except Exception: pass
                os.execv(sys.executable, [sys.executable] + sys.argv)
            threading.Thread(target=_sysmgr_restart, daemon=True).start()
            return
        else:
            bot.answer_callback_query(call.id, "Unknown system action.", show_alert=True)
            return
        bot.edit_message_text(out, chat_id, msg_id, parse_mode="HTML", reply_markup=_sysmgr_keyboard())
        bot.answer_callback_query(call.id)
    except Exception as exc:
        try: bot.answer_callback_query(call.id, str(exc)[:180], show_alert=True)
        except Exception: pass


@bot.callback_query_handler(func=lambda call: bool(call.data and call.data.startswith("suite_")))
def _admin_suite_callbacks(call):
    uid = call.from_user.id
    if not call.message or call.message.chat.type != "private" or not _sec_can(uid, "view_system") or CLONE_INSTANCE:
        bot.answer_callback_query(call.id, "Admin suite access denied.", show_alert=True)
        return
    data = call.data
    chat_id, msg_id = call.message.chat.id, call.message.message_id
    try:
        if data in ("suite_backup_now", "suite_backup_history", "suite_restore_info") and not _sec_can(uid, "backup"):
            bot.answer_callback_query(call.id, "Your role cannot access backup operations.", show_alert=True)
            return
        if data in ("suite_bc_all", "suite_bc_active", "suite_bc_clones") and not _sec_can(uid, "audit"):
            bot.answer_callback_query(call.id, "Your role cannot send broadcasts.", show_alert=True)
            return
        if data == "suite_activity" and not _sec_can(uid, "audit"):
            bot.answer_callback_query(call.id, "Your role cannot view audit logs.", show_alert=True)
            return
        if data == "suite_monitor":
            text_out, markup = _admin_monitor_text(), _admin_suite_keyboard("monitor")
        elif data == "suite_backup_now":
            _admin_backup_now(chat_id, uid)
            bot.answer_callback_query(call.id, "Backup sent to this chat.")
            return
        elif data == "suite_backup_history":
            hist = _admin_backup_history()
            lines = ["<blockquote><b>📜 BACKUP HISTORY</b>"]
            for item in hist[-20:][::-1]:
                lines.append(f"• {_html.escape(str(item.get('date','unknown')))} · {int(item.get('size',0))//1024} KB")
            if not hist: lines.append("No backup history yet.")
            lines.append("\n<i>Backup documents are retained in the configured Telegram backup destination. Restore requires a controlled restart.</i></blockquote>")
            text_out, markup = "\n".join(lines), _admin_suite_keyboard("backup")
        elif data == "suite_restore_info":
            text_out = ("<blockquote><b>♻️ RESTORE SAFETY</b>\n"
                        "A database restore replaces live user and settings data. To avoid corrupting an active SQLite store, restore is not performed from an inline button. "
                        "Download the selected backup, stop the service, preserve a copy of the current database, replace the database file, then restart. "
                        "Never restore an untrusted or unverified database file.</blockquote>")
            markup = _admin_suite_keyboard("backup")
        elif data == "suite_activity":
            lines = ["<blockquote><b>🧾 ADMIN ACTIVITY LOG</b>"]
            for item in _admin_audit_recent():
                lines.append(f"• <code>{_html.escape(item['created_at'])}</code> · <code>{item['admin_id']}</code> · {_html.escape(item['action'])} · {_html.escape(item['detail'][:90])}")
            if len(lines) == 1: lines.append("No recorded actions yet.")
            lines.append("</blockquote>")
            text_out, markup = "\n".join(lines), _admin_suite_keyboard("activity")
        elif data in ("suite_bc_all", "suite_bc_active", "suite_bc_clones"):
            target = {"suite_bc_all":"all", "suite_bc_active":"active30", "suite_bc_clones":"clones"}[data]
            ADMIN_STATE[uid] = {"action":"suite_broadcast_message", "target":target}
            bot.answer_callback_query(call.id, "Send the broadcast text.")
            bot.send_message(chat_id, f"📢 Send the message for audience: <b>{target}</b>. Send /cancel to abort.", parse_mode="HTML", reply_markup=_admin_back_kb())
            return
        else:
            bot.answer_callback_query(call.id, "Unknown admin suite action.", show_alert=True)
            return
        bot.edit_message_text(text_out, chat_id, msg_id, parse_mode="HTML", reply_markup=markup)
        bot.answer_callback_query(call.id)
    except Exception as exc:
        try: bot.answer_callback_query(call.id, str(exc)[:180], show_alert=True)
        except Exception: pass


@bot.callback_query_handler(func=lambda call: bool(call.data and call.data.startswith("keycheck_")))
def _security_key_callbacks(call):
    uid = call.from_user.id
    if not _sec_can(uid, "security_keys") or call.message.chat.type != "private" or CLONE_INSTANCE:
        bot.answer_callback_query(call.id, "Owner access required for encryption-key management.", show_alert=True)
        return
    try:
        data = call.data
        if data == "keycheck_back":
            bot.answer_callback_query(call.id)
            _show_admin_reply_page(call.message.chat.id, 0)
            return
        if data in ("keycheck_set_api", "keycheck_set_clone"):
            kind = "api" if data.endswith("_api") else "clone"
            name = "API_CONFIG_ENCRYPTION_KEY" if kind == "api" else "CLONE_TOKEN_ENCRYPTION_KEY"
            ADMIN_STATE[uid] = {"action": "security_key_set_" + kind}
            bot.answer_callback_query(call.id)
            bot.edit_message_text(
                f"🔐 <b>SET {kind.upper()} ENCRYPTION KEY</b>\nSend the new value for <code>{name}</code>.\n\n"
                "The value will never be echoed back. Send /cancel to abort.",
                call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=_security_keys_keyboard())
            return
        if data in ("keycheck_remove_api", "keycheck_remove_clone"):
            kind = "api" if data.endswith("_api") else "clone"
            kb = InlineKeyboardMarkup(row_width=2)
            kb.row(create_danger_button("⚠️ Confirm removal", callback_data="keycheck_confirm_remove_" + kind),
                   create_primary_button("Cancel", callback_data="keycheck_all"))
            bot.answer_callback_query(call.id)
            bot.edit_message_text(
                f"<b>Remove {kind.upper()} encryption key?</b>\nThis can make encrypted data unreadable. The bot will refuse removal if dependent encrypted records still exist.\nConfirm only if you understand this.",
                call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=kb)
            return
        if data.startswith("keycheck_confirm_remove_"):
            kind = data.rsplit("_", 1)[-1]
            _security_key_remove(kind)
            _admin_audit("security_key_removed", uid, kind)
            bot.answer_callback_query(call.id, "Key removed from persistent disk.", show_alert=True)
            bot.edit_message_text(_security_keys_text(), call.message.chat.id,
                                  call.message.message_id, parse_mode="HTML", reply_markup=_security_keys_keyboard())
            return
        if data in ("keycheck_api", "keycheck_clone", "keycheck_all"):
            if data == "keycheck_all":
                bot.answer_callback_query(call.id, "Key status refreshed")
            else:
                kind = "api" if data.endswith("_api") else "clone"
                name, ok, detail = _security_key_status(kind)
                bot.answer_callback_query(call.id, detail[:180], show_alert=True)
            bot.edit_message_text(_security_keys_text(), call.message.chat.id,
                                  call.message.message_id, parse_mode="HTML",
                                  reply_markup=_security_keys_keyboard())
            return
    except Exception as exc:
        try:
            bot.answer_callback_query(call.id, str(exc)[:180], show_alert=True)
            bot.edit_message_text(_security_keys_text() + "\n\n❌ " + _html.escape(str(exc)[:220]),
                                  call.message.chat.id, call.message.message_id, parse_mode="HTML",
                                  reply_markup=_security_keys_keyboard())
        except Exception:
            pass


@bot.callback_query_handler(func=lambda call: bool(call.data and call.data.startswith("clone_")))
def _clone_manager_callbacks(call):
    uid = call.from_user.id
    if not _sec_can(uid, "clone_control") or call.message.chat.type != "private" or CLONE_INSTANCE:
        bot.answer_callback_query(call.id, "Clone control permission required.", show_alert=True)
        return
    try:
        data = call.data
        if data == "clone_home":
            bot.edit_message_text(_clone_summary(), call.message.chat.id, call.message.message_id,
                                  parse_mode="HTML", reply_markup=_clone_manager_keyboard())
        elif data == "clone_list":
            rows = _clone_rows()
            bot.edit_message_text(_clone_summary(), call.message.chat.id, call.message.message_id,
                                  parse_mode="HTML", reply_markup=_clone_list_markup(rows))
        elif data == "clone_add":
            ADMIN_STATE[uid] = {"action": "clone_add_token"}
            bot.send_message(call.message.chat.id,
                "➕ <b>ADD NEW BOT CLONE</b>\nCreate a bot with @BotFather, then send its token here.\n"
                "I'll verify it with Telegram before saving. Token is encrypted at rest.\n"
                "Send /cancel to abort.", parse_mode="HTML", reply_markup=_admin_back_kb())
        elif data.startswith("clone_toggle:"):
            cid = int(data.split(":", 1)[1])
            row = next((r for r in _clone_rows() if int(r["clone_id"]) == cid), None)
            if not row:
                raise ValueError("Clone not found.")
            result = _clone_stop(cid) if row["enabled"] else _clone_start(cid)
            bot.answer_callback_query(call.id, result)
            rows = _clone_rows()
            bot.edit_message_text(_clone_summary(), call.message.chat.id, call.message.message_id,
                                  parse_mode="HTML", reply_markup=_clone_list_markup(rows))
            return
        elif data.startswith("clone_info:"):
            cid = int(data.split(":", 1)[1])
            row = next((r for r in _clone_rows() if int(r["clone_id"]) == cid), None)
            if not row:
                raise ValueError("Clone not found.")
            bot.answer_callback_query(call.id, f"@{row['bot_username']} · {'enabled' if row['enabled'] else 'stopped'}")
        bot.answer_callback_query(call.id)
    except Exception as exc:
        try: bot.answer_callback_query(call.id, str(exc)[:180], show_alert=True)
        except Exception: pass

@bot.callback_query_handler(func=lambda call: call.data.startswith("vech_page_"))
def vech_page_callback(call):
    try:
        parts = call.data.split("_", 3)
        # format: vech_page_{page_idx}_{user_id}
        if len(parts) < 4:
            bot.answer_callback_query(call.id)
            return
        page_idx = int(parts[2])
        user_id = int(parts[3])

        if call.from_user.id != user_id:
            bot.answer_callback_query(call.id, "❌ Not your session!", True)
            return

        chat_id = call.message.chat.id
        msg_id = call.message.message_id

        state = VECH_PAGINATION.get(user_id)
        if not state:
            bot.answer_callback_query(call.id, "❌ Session expired. Run command again.", True)
            return

        pages = state["pages"]
        if page_idx < 0 or page_idx >= len(pages):
            bot.answer_callback_query(call.id, "❌ Invalid page.", True)
            return

        state["current"] = page_idx
        text = pages[page_idx]

        markup = InlineKeyboardMarkup(row_width=3)
        buttons = []

        if len(pages) > 1:
            if page_idx > 0:
                buttons.append(create_primary_button(
                    "◀ Prev",
                    callback_data=f"vech_page_{page_idx - 1}_{user_id}",
                    icon_custom_emoji_id="5246794802560774143"
                ))

            buttons.append(create_success_button(
                f"{page_idx + 1}/{len(pages)}",
                callback_data=f"vech_noop_{user_id}",
                icon_custom_emoji_id="5422537279400868395"
            ))

            if page_idx < len(pages) - 1:
                buttons.append(create_danger_button(
                    "Next ▶",
                    callback_data=f"vech_page_{page_idx + 1}_{user_id}",
                    icon_custom_emoji_id="6192763368139397161"
                ))

            markup.row(*buttons)

        if state.get("posts_username"):
            markup.add(create_primary_button("📸 See Post", callback_data=f"viewall_{state['posts_username']}"))

        json_file = state.get("json_file")
        if page_idx == len(pages) - 1 and json_file:
            file_id = hashlib.md5(json_file.encode()).hexdigest()[:16]
            JSON_FILES[file_id] = json_file
            markup.add(InlineKeyboardButton("📥 Download JSON", callback_data=f"dljson_{file_id}"))

        markup.add(create_default_button("🔙 Back", callback_data="back_to_result", icon_custom_emoji_id="5307517685846785869"))

        try:
            edit_with_premium(chat_id, msg_id, text, reply_markup=markup)
        except Exception as e:
            print(f"Vech pagination edit error: {e}")

        bot.answer_callback_query(call.id, f"📄 Page {page_idx + 1}/{len(pages)}")
    except Exception as e:
        print(f"Vech page callback error: {e}")
        bot.answer_callback_query(call.id)


@bot.callback_query_handler(func=lambda call: call.data.startswith("vech_noop_"))
def vech_noop_callback(call):
    bot.answer_callback_query(call.id)


@bot.callback_query_handler(func=lambda call: call.data.startswith("num_page_"))
def num_page_callback(call):
    if call.data == "num_page_noop":
        bot.answer_callback_query(call.id)
        return

    user_id = call.from_user.id
    chat_id = call.message.chat.id
    msg_id  = call.message.message_id

    state = NUM_PAGINATION.get(user_id)
    if not state:
        bot.answer_callback_query(call.id, "❌ Session expired. Run /num again.", True)
        return

    parts    = call.data.split("_", 3)
    page_num = int(parts[2])
    pages    = state["pages"]

    if page_num < 1 or page_num > len(pages):
        bot.answer_callback_query(call.id, "❌ Invalid page.", True)
        return

    txt, markup = pages[page_num - 1]
    json_file = state.get("json_file")
    if page_num == len(pages) and json_file and markup:
        file_id = hashlib.md5(json_file.encode()).hexdigest()[:16]
        JSON_FILES[file_id] = json_file
        _cb = f"dljson_{file_id}"
        # markup object is reused across visits — add the button only once
        if not any(getattr(b, "callback_data", None) == _cb
                   for row in (markup.keyboard or []) for b in row):
            markup.add(InlineKeyboardButton("Download JSON", callback_data=_cb))

    try:
        edit_with_premium(chat_id, msg_id, txt, reply_markup=markup)
    except Exception as e:
        print(f"Pagination edit error: {e}")

    bot.answer_callback_query(call.id, f"📄 Page {page_num}/{len(pages)}")

@bot.callback_query_handler(func=lambda call: call.data == "num_dl_json")
def num_dl_json_callback(call):
    user_id = call.from_user.id
    chat_id = call.message.chat.id
    state = NUM_PAGINATION.get(user_id)
    if not state or not state.get("json_file"):
        bot.answer_callback_query(call.id, "❌ Session expired. Run /num again.", True)
        return
    json_file = state["json_file"]
    if os.path.exists(json_file):
        with open(json_file, 'rb') as f:
            bot.send_document(chat_id, f,
                              caption=premium_caption(f"\U0001f4c2 <b>{sc('JSON Export')}</b>"),
                              parse_mode="HTML")
        bot.answer_callback_query(call.id, "✅ JSON file sent!")
    else:
        bot.answer_callback_query(call.id, "❌ File not found!", True)


# ════════════════════════════════════════════════════════════
# ADMIN "ALL COMMANDS" MENU
# Every entry below maps to a real handler in this file.
# (cmd, purpose, example)
# ════════════════════════════════════════════════════════════
ADMIN_CMD_CATEGORIES = {
    "users": ("\U0001f465 User Management", [
        ("/users", "Show the latest registered users with their credits.", "/users"),
        ("/searchuser &lt;id|username&gt;", "Look up one user's full profile by ID or username.", "/searchuser 123456789"),
        ("/block &lt;user_id&gt;", "Ban a user from using the bot.", "/block 123456789"),
        ("/unblock &lt;user_id&gt;", "Remove a ban and let the user back in.", "/unblock 123456789"),
        ("/promote &lt;user_id&gt;", "Give a user admin rights.", "/promote 123456789"),
        ("/demote &lt;user_id&gt;", "Take admin rights away from a user.", "/demote 123456789"),
        ("/contact", "Export every verified phone number as a .txt file.", "/contact"),
    ]),
    "api": ("\U0001f50d Search &amp; APIs", [
        ("/api", "List every search command and the API URL it uses.", "/api"),
        ("/apic &lt;command&gt; &lt;api_url&gt;", "Point one command at a different API URL.", "/apic pan https://site.com/api/pan?key={key}&amp;pan={query}"),
        ("/apistatus &lt;command&gt; &lt;on|off&gt; [message]", "Turn a search command on or off and set its maintenance note.", "/apistatus num off Server down"),
        ("/commands", "Show the top command users and the total command count.", "/commands"),
    ]),
    "credits": ("\U0001f4b0 Credits &amp; Redeem", [
        ("/add &lt;user_id&gt; &lt;credits&gt;", "Add credits to a user's balance.", "/add 123456789 50"),
        ("/removecredit &lt;user_id&gt; &lt;credits&gt;", "Take credits away from a user.", "/removecredit 123456789 20"),
        ("/gen &lt;credits&gt; &lt;max_uses&gt; &lt;days&gt;", "Create a redeem code worth N credits, usable N times, valid N days.", "/gen 50 10 30"),
        ("/allcodes", "List the most recent redeem codes and their usage.", "/allcodes"),
        ("/deletecode &lt;code&gt;", "Deactivate a redeem code so it can no longer be used.", "/deletecode ABC123XYZ"),
    ]),
    "broadcast": ("\U0001f4e2 Broadcast", [
        ("/broadcast &lt;text&gt;", "Send a text message to every user and group.", "/broadcast Bot updated, enjoy!"),
        ("/broadcast (as a reply)", "Reply to any message with /broadcast to forward that exact message to everyone.", "/broadcast"),
        ("/broadcastbtn &lt;text&gt; | &lt;button&gt; | &lt;url&gt;", "Broadcast a message with a button attached.", "/broadcastbtn New update! | Join | https://t.me/yourchannel"),
        ("/setbc &lt;channel_id&gt;", "Auto-forward every post from this channel to all users.", "/setbc -1001234567890"),
        ("/removebc", "Turn the channel auto-broadcast off.", "/removebc"),
    ]),
    "forcejoin": ("\U0001f512 Force Join", [
        ("/addc", "Start the guided flow to add a force-join channel.", "/addc"),
        ("/removec &lt;url|username&gt;", "Remove a channel from the force-join list.", "/removec @mychannel"),
        ("/listc", "Show all force-join channels currently configured.", "/listc"),
        ("/lockf", "Disable force join — users can use the bot without joining.", "/lockf"),
        ("/unlockf", "Enable force join again.", "/unlockf"),
    ]),
    "media": ("\U0001f5bc Media Management", [
        ("/addvideo", "Start bulk video upload, then send videos and finish with /done.", "/addvideo"),
        ("/addphoto", "Start bulk photo upload, then send photos and finish with /done.", "/addphoto"),
        ("/done", "Save every file sent during the current upload session.", "/done"),
        ("/cancel", "Abort the current upload session without saving.", "/cancel"),
        ("/listvideos", "List saved videos with their IDs.", "/listvideos"),
        ("/listphotos", "List saved photos with their IDs.", "/listphotos"),
        ("/delvideo &lt;id&gt;", "Delete one saved video by its ID.", "/delvideo 652f1a9c4b1e8d0012ab34cd"),
        ("/delphoto &lt;id&gt;", "Delete one saved photo by its ID.", "/delphoto 652f1a9c4b1e8d0012ab34cd"),
        ("/setmode &lt;video|photo|both&gt;", "Choose which media type is attached to search results.", "/setmode both"),
    ]),
    "settings": ("\u2699\ufe0f Bot Settings", [
        ("/lock", "Lock the bot — only admins can use it.", "/lock"),
        ("/unlock", "Unlock the bot for everyone.", "/unlock"),
        ("/admin", "Open the admin panel.", "/admin"),
        ("/emojitest", "Check whether Telegram accepts this bot's premium emoji.", "/emojitest"),
    ]),
    "stats": ("\U0001f4ca Statistics", [
        ("/stats", "Full bot stats: users, credits, commands, referrals.", "/stats"),
        ("/uptime", "How long the bot has been running since its last restart.", "/uptime"),
        ("/commands", "Total commands used and the most active users.", "/commands"),
        ("/users", "Recently registered users.", "/users"),
    ]),
    "other": ("\U0001f4cc Other Commands", [
        ("/help", "The user-facing help menu with every search command.", "/help"),
        ("/profile", "Your own profile card.", "/profile"),
        ("/balance", "Your own credit balance.", "/balance"),
        ("/refer", "Your referral link.", "/refer"),
        ("/redeem &lt;code&gt;", "Redeem a credit code.", "/redeem ABC123XYZ"),
    ]),
}


def _acmd_root_markup():
    markup = InlineKeyboardMarkup(row_width=2)
    keys = list(ADMIN_CMD_CATEGORIES.keys())
    for i in range(0, len(keys), 2):
        row = [create_primary_button(ADMIN_CMD_CATEGORIES[k][0].replace("&amp;", "&"),
                                     callback_data=f"acmd_cat_{k}")
               for k in keys[i:i + 2]]
        markup.add(*row)
    markup.add(create_default_button("\U0001f519 Back", callback_data="acmd_back"))
    return markup


def _acmd_root_text():
    total = sum(len(v[1]) for v in ADMIN_CMD_CATEGORIES.values())
    return (
        "<blockquote>"
        "<b>\U0001f5c2 ALL COMMANDS</b>\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"\U0001f4c1 <b>Categories</b> : <code>{len(ADMIN_CMD_CATEGORIES)}</code>\n"
        f"\u26a1 <b>Commands</b>   : <code>{total}</code>\n\n"
        "Pick a category to see each command, what it does, and an example."
        "</blockquote>"
    )


def _acmd_cat_text(key):
    title, items = ADMIN_CMD_CATEGORIES[key]
    out = [
        "<blockquote>",
        f"<b>{title}</b>\n",
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n",
        "</blockquote>\n\n",
    ]
    for cmd, purpose, example in items:
        out.append(
            "<blockquote>"
            f"<b>{cmd}</b>\n"
            f"\U0001f4a1 <b>Purpose</b> : {purpose}\n"
            f"\U0001f4dd <b>Example</b> : <code>{example}</code>"
            "</blockquote>\n"
        )
    return "".join(out)


def _acmd_cat_markup(key):
    markup = InlineKeyboardMarkup(row_width=2)
    markup.add(
        create_default_button("\U0001f519 Categories", callback_data="acmd_root"),
        create_danger_button("\u274c Close", callback_data="acmd_close"),
    )
    return markup


@bot.callback_query_handler(func=lambda call: call.data.startswith("acmd_"))
def admin_allcommands_callback(call):
    """All Commands menu — admin only, no state kept, fully re-entrant."""
    try:
        if not is_admin(call.from_user.id):
            bot.answer_callback_query(call.id, "\u274c Admin only!", True)
            return

        chat_id = call.message.chat.id
        msg_id  = call.message.message_id
        data    = call.data

        if data == "acmd_close":
            _safe_call(bot.delete_message, chat_id, msg_id)
            bot.answer_callback_query(call.id)
            return

        if data in ("acmd_root", "acmd_all"):
            edit_with_premium(chat_id, msg_id, _acmd_root_text(), reply_markup=_acmd_root_markup())
            bot.answer_callback_query(call.id)
            return

        if data == "acmd_back":
            # back to the admin panel itself
            stats = get_bot_stats()
            edit_with_premium(chat_id, msg_id, _admin_panel_text(stats),
                              reply_markup=_admin_panel_markup())
            bot.answer_callback_query(call.id)
            return

        if data.startswith("acmd_cat_"):
            key = data[len("acmd_cat_"):]
            if key not in ADMIN_CMD_CATEGORIES:
                bot.answer_callback_query(call.id, "\u274c Unknown category.", True)
                return
            edit_with_premium(chat_id, msg_id, _acmd_cat_text(key),
                              reply_markup=_acmd_cat_markup(key))
            bot.answer_callback_query(call.id)
            return

        bot.answer_callback_query(call.id)
    except Exception as e:
        print(f"[ACMD] {e}")
        _safe_call(bot.answer_callback_query, call.id)



@bot.message_handler(commands=['emojitest'])
def emoji_test_cmd(message):
    """Admin: check whether Telegram accepts this bot's premium emoji."""
    global PREMIUM_EMOJI_SUPPORTED, _PREMIUM_WARNED
    if not is_admin(message.from_user.id):
        send_with_premium(message.chat.id, "\u274c Admin only!")
        return
    PREMIUM_EMOJI_SUPPORTED = True        # re-test from scratch
    _PREMIUM_WARNED = False
    eid = PREMIUM_EMOJI_IDS[0]
    probe = f'<b>Premium emoji probe</b>: <tg-emoji emoji-id="{eid}">\u2b50</tg-emoji>'
    try:
        bot.send_message(message.chat.id, probe, parse_mode="HTML")
        bot.send_message(
            message.chat.id,
            "\u2705 Telegram ACCEPTED the custom-emoji entity.\n"
            "If you still see a plain star, your own Telegram account is not "
            "Premium, or that emoji id is not in a pack your client can load.",
        )
    except Exception as exc:
        _note_premium_unsupported(exc)
        bot.send_message(
            message.chat.id,
            "\u274c Telegram REJECTED the custom-emoji entity.\n\n"
            f"Error: {str(exc)[:300]}\n\n"
            "A bot can only send premium emoji if it owns the emoji sticker set "
            "or holds a Fragment username. The bot has switched to normal emoji; "
            "all bold/code/blockquote formatting still works.",
        )


@bot.message_handler(commands=['allcommands'])
def all_commands_cmd(message):
    """Text entry point for the same menu."""
    if not is_admin(message.from_user.id):
        send_with_premium(message.chat.id, "\u274c Admin only!")
        return
    send_with_premium(message.chat.id, _acmd_root_text(), reply_markup=_acmd_root_markup())


# ══════════════════════════════════════════════════════════════
#  Admin panel — inline button router
# ══════════════════════════════════════════════════════════════

ADMIN_STATE = {}          # admin_id -> {"action": str}

_ADMIN_INPUT_ACTIONS = {
    "admin_addcredits":    ("addcredits",    "➕ ADD CREDITS",
                            "Send <code>&lt;user_id&gt; &lt;amount&gt;</code>\nExample: <code>8984851474 50</code>"),
    "admin_removecredits": ("removecredits", "➖ REMOVE CREDITS",
                            "Send <code>&lt;user_id&gt; &lt;amount&gt;</code>\nExample: <code>8984851474 20</code>"),
    "admin_block":         ("block",         "🚫 BLOCK USER",
                            "Send <code>&lt;user_id&gt;</code>"),
    "admin_unblock":       ("unblock",       "✅ UNBLOCK USER",
                            "Send <code>&lt;user_id&gt;</code>"),
    "admin_makeadmin":     ("makeadmin",     "👑 MAKE ADMIN",
                            "Send <code>&lt;user_id&gt;</code>"),
    "admin_removeadmin":   ("removeadmin",   "🗑 REMOVE ADMIN",
                            "Send <code>&lt;user_id&gt;</code>"),
    "admin_broadcast":     ("broadcast",     "📢 BROADCAST",
                            "Send the message text to blast to every user + group."),
    "admin_setbc":         ("setbc",         "📡 SET BC CHANNEL",
                            "Send the channel chat_id, e.g. <code>-1001234567890</code>"),
}


def _admin_kb(*rows):
    """Consistent admin submenus: positive=green, destructive=red, navigation=blue."""
    kb = InlineKeyboardMarkup(row_width=1)
    for label, data in rows:
        key = (str(data) + " " + str(label)).lower()
        if any(word in key for word in ("delete", "remove", "block", "disable", "reset", "clear")):
            button = create_danger_button(label, callback_data=data)
        elif any(word in key for word in ("add", "approve", "enable", "confirm", "save", "activate")):
            button = create_success_button(label, callback_data=data)
        else:
            button = create_primary_button(label, callback_data=data)
        kb.add(button)
    return kb


def _admin_back_kb():
    return _admin_kb(("⬅️ Back to Panel", "admin_panel"))


def _admin_users_page():
    try:
        total   = _col_users.count_documents({})
        admins  = _col_users.count_documents({"is_admin": 1})
        blocked = _col_users.count_documents({"is_blocked": 1})
    except Exception:
        total = admins = blocked = 0

    docs = []
    try:
        docs = list(_col_users.find({}, {"user_id": 1, "first_name": 1, "username": 1,
                                         "credits": 1, "is_admin": 1, "is_blocked": 1}))
        docs.sort(key=lambda d: _cmp_key(d.get("_id")), reverse=True)
        docs = docs[:12]
    except Exception:
        docs = []

    lines = ["<blockquote><b>👥 USERS</b>",
             "──────────────────────",
             f"📊 Total    : <code>{total}</code>",
             f"👑 Admins   : <code>{admins}</code>",
             f"🚫 Blocked  : <code>{blocked}</code>",
             f"✅ Active   : <code>{total - blocked}</code>",
             "──────────────────────",
             "<b>Latest 12</b>"]
    for d in docs:
        uname = d.get("username")
        tag = f"@{uname}" if uname else "no username"
        flag = "👑" if d.get("is_admin") in (1, "1", True) else ("🚫" if d.get("is_blocked") in (1, "1", True) else "•")
        lines.append(f"{flag} <code>{d.get('user_id')}</code> — {d.get('first_name') or 'User'} ({tag}) · {d.get('credits', 0)} cr")
    lines.append("</blockquote>")
    return "\n".join(lines)


def _admin_api_page():
    lines = ["<blockquote><b>🔧 API ENDPOINTS</b>", "──────────────────────"]
    for cmd, tpl in (API_ENDPOINTS or {}).items():
        if not tpl:
            lines.append(f"❌ <b>{cmd}</b> — not configured")
            continue
        host = tpl.split("//")[-1].split("/")[0]
        param = "query"
        m = re.search(r'[?&]([a-z0-9_]+)=\{query\}', tpl, re.I)
        if m:
            param = m.group(1)
        lines.append(f"✅ <b>{cmd}</b> → {host} <i>({param})</i>")
    lines.append("──────────────────────")
    lines.append(f"Total: <code>{len([1 for t in (API_ENDPOINTS or {}).values() if t])}</code> configured")
    lines.append("</blockquote>")
    return "\n".join(lines)


def _admin_media_page():
    return (
        "<blockquote><b>🖼 ADD MEDIA</b>\n"
        "──────────────────────\n"
        "Send photos → then <code>/done</code>\n"
        "Or send <code>/addphoto</code> to start photo mode\n\n"
        "Send videos → then <code>/done</code>\n"
        "Or send <code>/addvideo</code> to start video mode\n"
        "──────────────────────\n"
        "<code>/listphotos</code> · <code>/listvideos</code>\n"
        "<code>/delphoto &lt;n&gt;</code> · <code>/delvideo &lt;n&gt;</code>\n"
        "</blockquote>"
    )


def _admin_setbc_page():
    cur = BROADCAST_CHANNEL_ID
    return (
        "<blockquote><b>📡 BROADCAST CHANNEL</b>\n"
        "──────────────────────\n"
        f"Current: <code>{cur if cur else 'not set'}</code>\n\n"
        "Every post made in that channel is auto-forwarded\n"
        "to all users + groups.\n"
        "──────────────────────\n"
        "Send the new chat_id below, or use\n"
        "<code>/setbc -1001234567890</code>\n"
        "<code>/removebc</code> to turn it off\n"
        "</blockquote>"
    )


def _admin_backup_page():
    cfg = _col_media_set.find_one({"setting_key": "auto_backup_config"}) or {}
    target = cfg.get("chat_id")
    enabled = bool(cfg.get("enabled", False))
    status = "🟢 ENABLED" if enabled else "🔴 DISABLED"
    return ("<blockquote><b>💾 AUTOMATIC DATABASE BACKUP</b>\n"
            f"Status: <b>{status}</b>\n"
            f"Private group: <code>{target if target else 'Not selected'}</code>\n"
            "Interval: <code>30 seconds</code>\n\n"
            "Choose a private group by sending its numeric chat ID. Add the bot to that group and allow it to send documents.\n"
            "The bot sends a fresh SQLite database backup every 30 seconds while enabled.\n"
            "<i>Note: frequent backups create many files/messages in the group.</i></blockquote>")


def _auto_backup_worker():
    """Send a consistent SQLite snapshot to the admin-selected private group."""
    while True:
        time.sleep(30)
        try:
            cfg = _col_media_set.find_one({"setting_key": "auto_backup_config"}) or {}
            target = cfg.get("chat_id")
            if not cfg.get("enabled") or not target:
                continue
            fd, backup_path = tempfile.mkstemp(prefix="whoisshown_backup_", suffix=".db")
            os.close(fd)
            try:
                dest = sqlite3.connect(backup_path)
                try:
                    with _store._lock:
                        _store._conn.backup(dest)
                finally:
                    dest.close()
                stamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
                with open(backup_path, "rb") as backup_file:
                    bot.send_document(int(target), backup_file,
                                      caption=f"💾 WHOISSHOWN AUTO BACKUP\n🕒 {stamp}")
                _col_media_set.update_one({"setting_key": "auto_backup_config"},
                    {"$set": {"last_backup": stamp, "last_error": None}}, upsert=True)
            finally:
                try:
                    os.remove(backup_path)
                except OSError:
                    pass
        except Exception as exc:
            print(f"[AUTO_BACKUP] {exc}")
            try:
                _col_media_set.update_one({"setting_key": "auto_backup_config"},
                    {"$set": {"last_error": str(exc)[:300]}}, upsert=True)
            except Exception:
                pass


threading.Thread(target=_auto_backup_worker, daemon=True, name="auto-backup").start()


@bot.callback_query_handler(func=lambda call: bool(call.data and call.data.startswith("start_")))
def start_menu_callback(call):
    """Private-chat-only launcher actions. Group callbacks are intentionally rejected."""
    try:
        if not call.message or call.message.chat.type != "private":
            bot.answer_callback_query(call.id, "Open the bot in private chat to use these buttons.", True)
            return

        uid = call.from_user.id
        chat_id = call.message.chat.id
        data = call.data

        if data == "start_myid":
            bot.send_message(chat_id,
                f"<blockquote>🆔 <b>YOUR TELEGRAM USER ID</b>\n<code>{uid}</code></blockquote>",
                parse_mode="HTML")
        elif data == "start_number":
            bot.send_message(chat_id, "📱 Send a number using <code>/num number</code>.", parse_mode="HTML")
        elif data == "start_instagram":
            bot.send_message(chat_id, "📸 Send a public Instagram username using <code>/insta username</code>.", parse_mode="HTML")
        elif data == "start_freefire":
            bot.send_message(chat_id, "🎮 Send a game UID using <code>/ff PLAYER_UID</code>.", parse_mode="HTML")
        elif data == "start_github":
            bot.send_message(chat_id, "🐙 Send a public GitHub username using <code>/git username</code>.", parse_mode="HTML")
        elif data == "start_profile":
            user_data = get_user(uid)
            if not user_data:
                bot.send_message(chat_id, "Please send /start first.")
            else:
                body = (
                    "<blockquote><b>👤 ʏᴏᴜʀ ᴘʀᴏғɪʟᴇ</b>\n"
                    f"🆔 ID: <code>{user_data[0]}</code>\n"
                    f"👤 Username: @{_html.escape(str(user_data[1] or 'N/A'))}\n"
                    f"📝 Name: {_html.escape(str(user_data[2] or 'User'))}\n"
                    f"💎 Credits: <code>{user_data[3] or 0}</code>\n"
                    f"🎁 Referrals: <code>{user_data[6] or 0}</code></blockquote>"
                )
                bot.send_message(chat_id, body, parse_mode="HTML")
        elif data == "start_balance":
            bot.send_message(chat_id,
                f"<blockquote>💰 <b>ᴄʀᴇᴅɪᴛ ʙᴀʟᴀɴᴄᴇ</b>\n💎 Credits: <code>{get_credits(uid)}</code></blockquote>",
                parse_mode="HTML")
        elif data == "start_refer":
            bot.send_message(chat_id, "🎁 Use <code>/refer</code> to get your referral link.", parse_mode="HTML")
        elif data == "start_redeem":
            bot.send_message(chat_id, "🎟 Send your code using <code>/redeem YOUR_CODE</code>.", parse_mode="HTML")
        elif data == "start_help":
            bot.send_message(chat_id, "❔ Use /help to view the command guide.")
        elif data == "start_api_total":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "Admin only.", True)
                return
            endpoints = API_ENDPOINTS or {}
            configured = sum(1 for endpoint in endpoints.values() if endpoint)
            custom_count = 0
            try:
                custom_count = _col_api_config.count_documents({})
            except Exception:
                pass
            api_text = (
                "<blockquote><b>📊 ᴀᴘɪ ᴏᴠᴇʀᴠɪᴇᴡ</b>\n"
                f"🧩 Built-in endpoints: <code>{configured}</code>\n"
                f"🛠 Custom endpoint records: <code>{custom_count}</code>\n"
                f"📦 Total registered: <code>{configured + custom_count}</code>\n"
                "🔐 API credentials are hidden.</blockquote>"
            )
            bot.send_message(chat_id, api_text, parse_mode="HTML")
        elif data == "start_admin":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "Admin only.", True)
                return
            admin_panel(call.message)
        else:
            bot.answer_callback_query(call.id, "Unknown menu action.", True)
            return

        bot.answer_callback_query(call.id)
    except Exception as exc:
        print(f"[START_MENU_CALLBACK] {exc}")
        try:
            bot.answer_callback_query(call.id, "Could not open this option. Try again.", True)
        except Exception:
            pass


@bot.callback_query_handler(func=lambda call: call.data.startswith("admin_") or call.data == "admin_panel")
def admin_panel_callback(call):
    """Every admin-panel button lands here."""
    try:
        if not call.message or call.message.chat.type != "private":
            bot.answer_callback_query(call.id, "Use the admin panel in private chat only.", True)
            return
        if not is_admin(call.from_user.id):
            bot.answer_callback_query(call.id, "❌ Admin only!", True)
            return

        chat_id = call.message.chat.id
        msg_id  = call.message.message_id
        data    = call.data
        uid     = call.from_user.id
        _admin_audit("inline_action", uid, data)

        # reopen the panel
        if data == "admin_panel":
            ADMIN_STATE.pop(uid, None)
            try:
                edit_with_premium(chat_id, msg_id, "🛠 <b>Admin panel opened below.</b>", reply_markup=None)
            except Exception:
                pass
            _show_admin_reply_page(chat_id, 0)
            bot.answer_callback_query(call.id, "✅ Admin keyboard opened")
            return

        if data == "admin_stats":
            ADMIN_STATE.pop(uid, None)
            edit_with_premium(chat_id, msg_id, _admin_panel_text(get_bot_stats()),
                              reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id, "📊 Stats refreshed")
            return

        if data == "admin_dau":
            ADMIN_STATE.pop(uid, None)
            today_key = datetime.now().strftime("%Y-%m-%d")
            dau = _col_users.count_documents({"last_active": {"$regex": f"^{today_key}"}})
            yesterday_key = (datetime.now() - timedelta(days=1)).strftime("%Y-%m-%d")
            yesterday_dau = _col_users.count_documents({"last_active": {"$regex": f"^{yesterday_key}"}})
            page = (
                "<blockquote><b>📆 DAILY ACTIVE USERS</b>\n"
                "━━━━━━━━━━━━━━━━━━━━\n"
                f"🟢 <b>Today ({today_key})</b>: <code>{dau:,}</code>\n"
                f"🕘 <b>Yesterday ({yesterday_key})</b>: <code>{yesterday_dau:,}</code>\n"
                "<i>Counts registered users whose last activity timestamp falls on that calendar day.</i>\n"
                "━━━━━━━━━━━━━━━━━━━━</blockquote>"
            )
            edit_with_premium(chat_id, msg_id, page, reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id, "Daily active users")
            return

        if data == "admin_users":
            ADMIN_STATE.pop(uid, None)
            edit_with_premium(chat_id, msg_id, _admin_users_page(),
                              reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id)
            return

        if data == "admin_api_status":
            ADMIN_STATE.pop(uid, None)
            edit_with_premium(chat_id, msg_id, _admin_api_page(),
                              reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id)
            return

        if data == "admin_total_apis":
            ADMIN_STATE.pop(uid, None)
            built_in = API_ENDPOINTS or {}
            configured = sum(1 for endpoint in built_in.values() if endpoint)
            try:
                custom_count = _col_api_config.count_documents({})
            except Exception:
                custom_count = 0
            page = (
                "<blockquote><b>📊 TOTAL API OVERVIEW</b>\n"
                "━━━━━━━━━━━━━━━━━━━━\n"
                f"🧩 Built-in endpoints: <code>{configured}</code>\n"
                f"🛠 Custom API records: <code>{custom_count}</code>\n"
                f"📦 Total registered: <code>{configured + custom_count}</code>\n"
                "🔐 API keys and full URLs are not displayed here.\n"
                "━━━━━━━━━━━━━━━━━━━━</blockquote>"
            )
            edit_with_premium(chat_id, msg_id, page, reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id, "API totals")
            return

        if data == "admin_addmedia":
            ADMIN_STATE.pop(uid, None)
            edit_with_premium(chat_id, msg_id, _admin_media_page(),
                              reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id)
            return

        if data == "admin_backup":
            ADMIN_STATE.pop(uid, None)
            cfg = _col_media_set.find_one({"setting_key": "auto_backup_config"}) or {}
            toggle_label = "⏸ Disable backups" if cfg.get("enabled") else "▶️ Enable backups"
            edit_with_premium(chat_id, msg_id, _admin_backup_page(),
                reply_markup=_admin_kb(("📍 Choose private group", "admin_backup_set"),
                                       (toggle_label, "admin_backup_toggle"),
                                       ("⬅️ Back to Panel", "admin_panel")))
            bot.answer_callback_query(call.id)
            return

        if data == "admin_backup_set":
            ADMIN_STATE[uid] = {"action": "backup_chat_id"}
            edit_with_premium(chat_id, msg_id,
                "<blockquote><b>📍 SELECT BACKUP GROUP</b>\nSend the private group's numeric chat ID (usually starts with <code>-100</code>).\nThe bot must already be in that group and able to send documents.</blockquote>",
                reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id, "Send group chat ID")
            return

        if data == "admin_backup_toggle":
            cfg = _col_media_set.find_one({"setting_key": "auto_backup_config"}) or {}
            if not cfg.get("chat_id"):
                bot.answer_callback_query(call.id, "Choose a backup group first", True)
                return
            new_state = not bool(cfg.get("enabled"))
            _col_media_set.update_one({"setting_key": "auto_backup_config"},
                {"$set": {"enabled": new_state, "updated_by": uid}}, upsert=True)
            cfg["enabled"] = new_state
            edit_with_premium(chat_id, msg_id, _admin_backup_page(),
                reply_markup=_admin_kb(("📍 Choose private group", "admin_backup_set"),
                    (("⏸ Disable backups" if new_state else "▶️ Enable backups"), "admin_backup_toggle"),
                    ("⬅️ Back to Panel", "admin_panel")))
            bot.answer_callback_query(call.id, "Backups enabled" if new_state else "Backups disabled")
            return

        if data == "admin_add_all_credits":
            ADMIN_STATE[uid] = {"action": "addallcredits"}
            edit_with_premium(chat_id, msg_id,
                "<blockquote><b>🎁 ADD CREDITS TO ALL USERS</b>\nSend the amount to add to every registered user.\nExample: <code>25</code></blockquote>",
                reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id, "Send credit amount")
            return

        editable_text_actions = {
            "admin_edit_help": ("edit_help_text", "📝 EDIT HELP TEXT", "Send the complete replacement text for /help. HTML formatting is supported. This replaces the built-in help page."),
            "admin_edit_lookup_guide": ("edit_lookup_guide", "📘 EDIT LOOKUP GUIDE", "Send the lookup safety/usage guide to append to /help. HTML formatting is supported."),
            "admin_edit_support_text": ("edit_support_text", "☎️ EDIT SUPPORT TEXT", "Send the support/contact text to append to /help. HTML formatting is supported."),
        }
        if data in editable_text_actions:
            action, title, hint = editable_text_actions[data]
            ADMIN_STATE[uid] = {"action": action}
            edit_with_premium(chat_id, msg_id,
                f"<blockquote><b>{title}</b>\n{hint}\n\nSend your new text as the next message. Tap Back to cancel.</blockquote>",
                reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id, "Send the new text")
            return

        if data == "admin_reset_editable_text":
            _col_media_set.delete_one({"setting_key": "editable_bot_texts"})
            edit_with_premium(chat_id, msg_id, "✅ Editable help, lookup guide and support text reset. Built-in /help is active again.", reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id, "Text settings reset")
            return

        if data == "admin_welcome_manager":
            ADMIN_STATE.pop(uid, None)
            doc = _col_media_set.find_one({"setting_key": "welcome_config"}) or {}
            mode = doc.get("mode", "default")
            caption = doc.get("text", "")
            edit_with_premium(
                chat_id, msg_id,
                "<blockquote><b>👋 WELCOME MANAGER</b>\n"
                f"Current mode: <code>{_html.escape(str(mode))}</code>\n"
                f"Saved text: <code>{_html.escape(str(caption)[:350]) or 'Default welcome'}</code>\n\n"
                "Choose a welcome type below. For photo/video, send the media to the bot after selecting it.\n"
                "For text, send the new welcome text as your next message.</blockquote>",
                reply_markup=_admin_kb(("📝 Text welcome", "admin_welcome_text"),
                                       ("🖼 Photo welcome", "admin_welcome_photo"),
                                       ("🎬 Video welcome", "admin_welcome_video"),
                                       ("♻️ Reset default", "admin_welcome_reset"),
                                       ("⬅️ Back to Panel", "admin_panel")))
            bot.answer_callback_query(call.id)
            return

        if data in ("admin_welcome_text", "admin_welcome_photo", "admin_welcome_video"):
            mode = data.rsplit("_", 1)[-1]
            ADMIN_STATE[uid] = {"action": "welcome_" + mode}
            hint = "Send the welcome text." if mode == "text" else ("Now send one photo with an optional caption." if mode == "photo" else "Now send one video with an optional caption.")
            edit_with_premium(chat_id, msg_id, f"<blockquote><b>WELCOME: {mode.upper()}</b>\n{hint}\nTap Back to cancel.</blockquote>", reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id, "Send the content")
            return

        if data == "admin_welcome_reset":
            _col_media_set.delete_one({"setting_key": "welcome_config"})
            edit_with_premium(chat_id, msg_id, "✅ Welcome reset to the original default.", reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id, "Reset")
            return

        if data == "admin_user_history":
            ADMIN_STATE[uid] = {"action": "userhistory"}
            edit_with_premium(chat_id, msg_id, "<blockquote><b>🧾 USER HISTORY</b>\nSend a Telegram user ID or @username.\nShows account activity and up to 25 recorded searches. Search logging starts after this upgrade.</blockquote>", reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id)
            return

        if data == "admin_setbc_info":
            ADMIN_STATE[uid] = {"action": "setbc"}
            edit_with_premium(chat_id, msg_id, _admin_setbc_page(),
                              reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id, "📡 Send the chat_id")
            return

        if data == "admin_broadcast_info":
            ADMIN_STATE[uid] = {"action": "broadcast"}
            edit_with_premium(
                chat_id, msg_id,
                "<blockquote><b>📢 BROADCAST</b>\n"
                "──────────────────────\n"
                "Send the text to blast now.\n\n"
                "Or reply to any message with\n"
                "<code>/broadcast</code> to forward it.\n"
                "</blockquote>",
                reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id, "📢 Send the message")
            return

        if data == "admin_reload":
            bot.answer_callback_query(call.id, "🔄 Restarting bot…")
            send_with_premium(chat_id, "🔄 <b>Restarting…</b>\nBack in a few seconds.", parse_mode="HTML")
            def _restart():
                time.sleep(1.5)
                try:
                    bot.stop_polling()
                except Exception:
                    pass
                os.execv(sys.executable, [sys.executable] + sys.argv)
            threading.Thread(target=_restart, daemon=True).start()
            return

        spec = _ADMIN_INPUT_ACTIONS.get(data)
        if spec:
            action, title, hint = spec
            ADMIN_STATE[uid] = {"action": action}
            edit_with_premium(
                chat_id, msg_id,
                f"<blockquote><b>{title}</b>\n"
                "──────────────────────\n"
                f"{hint}\n"
                "──────────────────────\n"
                "Send it as your next message.\n"
                "Tap Back to cancel.</blockquote>",
                reply_markup=_admin_back_kb())
            bot.answer_callback_query(call.id)
            return

        bot.answer_callback_query(call.id, "❔ Unknown action")
    except Exception as exc:
        print(f"[ADMIN_PANEL] {exc}")
        try:
            bot.answer_callback_query(call.id, "❌ Error", True)
        except Exception:
            pass


# ══════════════════════════════════════════════════════════════
#  USER EXPERIENCE HUB — profile, preferences, favorites,
#  support tickets, feedback, activity, referrals and premium info
# ══════════════════════════════════════════════════════════════
_USER_HUB_STATE = {}
_USER_HUB_SETTINGS = _db["user_hub_settings"]
_USER_HUB_FAVORITES = _db["user_hub_favorites"]
_USER_HUB_TICKETS = _db["user_support_tickets"]
_USER_HUB_FEEDBACK = _db["user_feedback"]

_USER_HUB_NOTIFICATIONS = _db["user_hub_notifications"]
_USER_HUB_ASSISTANT_STATE = {}
_USER_HUB_MESSAGE = {}


def _uh_edit_target(chat_id, message_id, text, markup=None):
    """Edit the existing User Hub message; never create duplicate bot replies on edit failure."""
    text = _uh_safe_small_caps_html(text)
    try:
        return bot.edit_message_text(
            text, chat_id=chat_id, message_id=message_id,
            parse_mode="HTML", reply_markup=markup
        )
    except Exception as exc:
        if "message is not modified" in str(exc).lower():
            return None
        logging.warning("[USER_HUB_EDIT] Could not edit message %s; no duplicate message sent: %s", message_id, exc)
        raise


def _uh_edit_call(call, text, markup=None):
    if not call.message:
        return _uh_send(call.from_user.id, text, markup)
    chat_id = call.message.chat.id
    message_id = call.message.message_id
    _USER_HUB_MESSAGE[int(call.from_user.id)] = (chat_id, message_id)
    return _uh_edit_target(chat_id, message_id, text, markup)


def _uh_back_keyboard(callback_data="uh_home", label="⬅️ Uꜱᴇʀ Hᴜʙ"):
    kb = InlineKeyboardMarkup()
    kb.add(create_primary_button(label, callback_data=callback_data))
    return kb

def _uh_safe_small_caps_html(value):
    """Apply small caps to visible text without corrupting Telegram HTML tags."""
    parts = re.split(r"(<[^>]*>|&(?:amp|lt|gt|quot|#\d+|#x[0-9a-fA-F]+);)", str(value))
    return "".join(part if (part.startswith("<") and part.endswith(">")) or part.startswith("&")
                   else _admin_small_caps(part) for part in parts)

def _uh_command_catalog():
    catalog = []
    for label, (command, prompt) in _PRIVATE_MENU_PROMPTS.items():
        if command:
            catalog.append({"label": label, "command": command, "prompt": prompt})
    return catalog

def _uh_find_commands(query, limit=8):
    query = (query or "").strip().casefold()
    if not query:
        return []
    terms = [x for x in re.split(r"\s+", query) if x]
    found = []
    for item in _uh_command_catalog():
        haystack = (item["label"] + " " + item["command"] + " " + item["prompt"]).casefold()
        score = sum(3 if term in item["label"].casefold() else 2 if term in item["command"].casefold() else 1
                    for term in terms if term in haystack)
        if score:
            found.append((score, item))
    found.sort(key=lambda pair: (-pair[0], pair[1]["label"]))
    return [item for _score, item in found[:limit]]

def _uh_usage_text(uid):
    user = get_user(uid) or {}
    credits = get_credits(uid)
    commands = int(user.get("total_commands", 0) or 0)
    referrals = int(user.get("referral_count", 0) or 0)
    try:
        history_count = _col_search_history.count_documents({"user_id": int(uid)})
    except Exception:
        history_count = 0
    plan = "Premium" if user.get("premium_until") else "Free"
    return (
        "<blockquote><b>📊 YOUR USAGE DASHBOARD</b>\n"
        f"💎 Available credits: <code>{credits}</code>\n"
        f"⚡ Recorded commands: <code>{commands}</code>\n"
        f"🧾 Saved history entries: <code>{history_count}</code>\n"
        f"🎁 Successful referrals: <code>{referrals}</code>\n"
        f"⭐ Membership: <b>{plan}</b></blockquote>"
    )

def _uh_achievements_text(uid):
    user = get_user(uid) or {}
    referrals = int(user.get("referral_count", 0) or 0)
    commands = int(user.get("total_commands", 0) or 0)
    favorites = _USER_HUB_FAVORITES.count_documents({"user_id": int(uid)})
    tickets = _USER_HUB_TICKETS.count_documents({"user_id": int(uid)})
    achievements = [
        ("🌱 First Steps", commands >= 1, "Run your first command"),
        ("🔎 Explorer", commands >= 10, "Run 10 commands"),
        ("🚀 Power User", commands >= 100, "Run 100 commands"),
        ("🤝 Connector", referrals >= 1, "Refer your first eligible friend"),
        ("🌟 Community Builder", referrals >= 5, "Refer 5 eligible friends"),
        ("📌 Organizer", favorites >= 3, "Save 3 shortcuts"),
        ("💬 Communicator", tickets >= 1, "Open a support ticket"),
    ]
    lines = ["<blockquote><b>🏆 YOUR ACHIEVEMENTS</b>"]
    for title, unlocked, description in achievements:
        lines.append(f"{'✅' if unlocked else '🔒'} {title} — {description}")
    lines.append("\nAchievements are based on recorded bot activity and eligible referrals.</blockquote>")
    return "\n".join(lines)

def _uh_notifications_text(uid):
    docs = list(_USER_HUB_NOTIFICATIONS.find({"user_id": int(uid)}))
    docs.sort(key=lambda d: str(d.get("created_at", "")), reverse=True)
    lines = ["<blockquote><b>🔔 NOTIFICATION CENTER</b>"]
    if not docs:
        lines.append("No saved notifications yet.")
    for doc in docs[:15]:
        status = "●" if not doc.get("read") else "○"
        title = _html.escape(str(doc.get("title", "Update"))[:100])
        body = _html.escape(str(doc.get("body", ""))[:350])
        lines.append(f"{status} <b>{title}</b>\n{body}")
    lines.append("</blockquote>")
    return "\n".join(lines)


def _uh_get_settings(uid):
    doc = _USER_HUB_SETTINGS.find_one({"user_id": int(uid)}) or {}
    return {
        "language": doc.get("language", "English"),
        "notifications": bool(doc.get("notifications", True)),
        "tips": bool(doc.get("tips", True)),
    }


def _uh_menu():
    kb = InlineKeyboardMarkup(row_width=2)
    kb.row(create_primary_button("👤 Mʏ Pʀᴏꜰɪʟᴇ", callback_data="uh_profile"),
           create_primary_button("⚙️ Sᴇᴛᴛɪɴɢꜱ", callback_data="uh_settings"))
    kb.row(create_primary_button("⭐ Fᴀᴠᴏʀɪᴛᴇꜱ", callback_data="uh_favorites"),
           create_primary_button("🕘 Rᴇᴄᴇɴᴛ Aᴄᴛɪᴠɪᴛʏ", callback_data="uh_activity"))
    kb.row(create_primary_button("🎁 Rᴇꜰᴇʀʀᴀʟꜱ & Rᴇᴡᴀʀᴅꜱ", callback_data="uh_rewards"),
           create_primary_button("🔔 Nᴏᴛɪꜰɪᴄᴀᴛɪᴏɴꜱ", callback_data="uh_notifications"))
    kb.row(create_success_button("💬 Hᴇʟᴘ & Sᴜᴘᴘᴏʀᴛ", callback_data="uh_support"),
           create_success_button("📝 Sᴇɴᴅ Fᴇᴇᴅʙᴀᴄᴋ", callback_data="uh_feedback"))
    kb.row(create_primary_button("💎 Pʀᴇᴍɪᴜᴍ Pʟᴀɴꜱ", callback_data="uh_premium"))
    kb.row(create_primary_button("🔎 Sᴍᴀʀᴛ Sᴇᴀʀᴄʜ", callback_data="uh_search"),
           create_primary_button("🤖 Sᴍᴀʀᴛ Aꜱꜱɪꜱᴛᴀɴᴛ", callback_data="uh_assistant"))
    kb.row(create_primary_button("📊 Uꜱᴀɢᴇ Dᴀꜱʜʙᴏᴀʀᴅ", callback_data="uh_usage"),
           create_primary_button("🏆 Aᴄʜɪᴇᴠᴇᴍᴇɴᴛꜱ", callback_data="uh_achievements"))
    kb.row(create_primary_button("📥 Nᴏᴛɪꜰɪᴄᴀᴛɪᴏɴ Iɴʙᴏx", callback_data="uh_inbox"))
    return kb


def _uh_send(chat_id, text, markup=None):
    # Keep Telegram HTML tags intact while styling visible message text.
    text = _uh_safe_small_caps_html(text)
    return send_with_premium(chat_id, text, parse_mode="HTML", reply_markup=markup)


def _uh_home(chat_id, uid, message=None):
    doc = get_user(uid) or {}
    name = _html.escape(str(doc.get("first_name") or "there"))
    credits = get_credits(uid)
    settings = _uh_get_settings(uid)
    text = (
        "<blockquote><b>🌟 SHOWN LEGACY — USER HUB</b>\n"
        f"Welcome, <b>{name}</b>!\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"💎 Credits: <code>{credits}</code>\n"
        f"🌐 Language: <b>{_html.escape(settings['language'])}</b>\n"
        f"🔔 Notifications: <b>{'On' if settings['notifications'] else 'Off'}</b>\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        "Your profile, preferences, saved shortcuts and support are all here.</blockquote>"
    )
    if message is not None:
        _uh_edit_target(chat_id, message.message_id, text, _uh_menu())
        _USER_HUB_MESSAGE[int(uid)] = (chat_id, message.message_id)
    else:
        sent = _uh_send(chat_id, text, _uh_menu())
        try:
            _USER_HUB_MESSAGE[int(uid)] = (chat_id, sent.message_id)
        except Exception:
            pass


def _uh_profile_text(uid):
    doc = get_user(uid) or {}
    join_date = doc.get("join_date") or "Not available"
    referral_count = doc.get("referral_count", 0)
    username = ("@" + str(doc.get("username"))) if doc.get("username") not in (None, "", "N/A") else "Not set"
    premium_until = doc.get("premium_until")
    premium = "Active until " + str(premium_until) if premium_until else "Free account"
    return (
        "<blockquote><b>👤 YOUR PROFILE</b>\n"
        f"🆔 Telegram ID: <code>{uid}</code>\n"
        f"👤 Name: {_html.escape(str(doc.get('first_name') or 'User'))}\n"
        f"🔗 Username: {_html.escape(username)}\n"
        f"📅 Joined: <code>{_html.escape(str(join_date))}</code>\n"
        f"💎 Credits: <code>{get_credits(uid)}</code>\n"
        f"🎁 Successful referrals: <code>{referral_count}</code>\n"
        f"⭐ Plan: <b>{_html.escape(premium)}</b>\n"
        "</blockquote>"
    )


def _uh_settings_text(uid):
    s = _uh_get_settings(uid)
    kb = InlineKeyboardMarkup(row_width=2)
    kb.row(create_primary_button("🌐 Cʜᴀɴɢᴇ Lᴀɴɢᴜᴀɢᴇ", callback_data="uh_language"))
    kb.row(create_success_button("🔔 Nᴏᴛɪꜰɪᴄᴀᴛɪᴏɴꜱ: ON" if s["notifications"] else "🔕 Notifications: OFF",
                                 callback_data="uh_toggle_notifications"),
           create_primary_button("💡 Tɪᴘꜱ: ON" if s["tips"] else "💡 Tɪᴘꜱ: OFF",
                                 callback_data="uh_toggle_tips"))
    kb.add(create_primary_button("⬅️ Uꜱᴇʀ Hᴜʙ", callback_data="uh_home"))
    return (
        "<blockquote><b>⚙️ PERSONAL SETTINGS</b>\n"
        f"Language: <b>{_html.escape(s['language'])}</b>\n"
        f"Notifications: <b>{'Enabled' if s['notifications'] else 'Disabled'}</b>\n"
        f"Helpful tips: <b>{'Enabled' if s['tips'] else 'Disabled'}</b>\n"
        "Choose what you want to change.</blockquote>", kb
    )


def _uh_favorites_text(uid):
    docs = list(_USER_HUB_FAVORITES.find({"user_id": int(uid)}))
    docs.sort(key=lambda d: str(d.get("created_at", "")), reverse=True)
    lines = ["<blockquote><b>⭐ YOUR SAVED SHORTCUTS</b>"]
    if not docs:
        lines.append("You have not saved anything yet.")
    for n, d in enumerate(docs[:15], 1):
        lines.append(f"{n}. {_html.escape(str(d.get('label', 'Shortcut')))}")
    lines.append("</blockquote>")
    return "\n".join(lines)


def _uh_activity_text(uid):
    try:
        docs = list(_col_search_history.find({"user_id": int(uid)}))
        docs.sort(key=lambda d: str(d.get("timestamp") or d.get("created_at") or d.get("date") or ""), reverse=True)
    except Exception:
        docs = []
    lines = ["<blockquote><b>🕘 RECENT ACTIVITY</b>"]
    if not docs:
        lines.append("No recent lookup activity is available yet.")
    for d in docs[:8]:
        label = d.get("command") or d.get("type") or d.get("query_type") or "Lookup"
        when = d.get("timestamp") or d.get("created_at") or d.get("date") or ""
        lines.append(f"• {_html.escape(str(label))} — {_html.escape(str(when))}")
    lines.append("\nOnly activity retained by the bot can be shown here.</blockquote>")
    return "\n".join(lines)


def _uh_support_text():
    kb = InlineKeyboardMarkup(row_width=1)
    kb.add(create_success_button("🎫 Oᴘᴇɴ Sᴜᴘᴘᴏʀᴛ Tɪᴄᴋᴇᴛ", callback_data="uh_new_ticket"))
    kb.add(create_primary_button("📋 Mʏ Sᴜᴘᴘᴏʀᴛ Tɪᴄᴋᴇᴛꜱ", callback_data="uh_my_tickets"))
    kb.add(create_primary_button("⬅️ Uꜱᴇʀ Hᴜʙ", callback_data="uh_home"))
    return ("<blockquote><b>💬 HELP & SUPPORT</b>\n"
            "Need help? Open a support ticket and describe the issue. "
            "Please do not send passwords, OTPs, API keys or sensitive documents.</blockquote>", kb)


def _uh_notify_admins(text):
    sent = 0
    for admin_id in list(ADMIN_IDS):
        try:
            bot.send_message(int(admin_id), text, parse_mode="HTML")
            sent += 1
        except Exception:
            pass
    return sent


def _uh_callback(call):
    uid = int(call.from_user.id)
    chat_id = call.message.chat.id if call.message else uid
    data = call.data or ""
    if not call.message or call.message.chat.type != "private":
        bot.answer_callback_query(call.id, "Please use the User Hub in private chat.", True)
        return
    try:
        # Leaving a text-entry screen cancels its pending input state.
        _USER_HUB_STATE.pop(uid, None)
        _USER_HUB_MESSAGE[uid] = (chat_id, call.message.message_id)
        if data == "uh_home":
            _uh_home(chat_id, uid, call.message)
        elif data == "uh_profile":
            _uh_edit_call(call, _uh_profile_text(uid), _uh_back_keyboard())
        elif data == "uh_settings":
            text, kb = _uh_settings_text(uid)
            _uh_edit_call(call, text, kb)
        elif data == "uh_language":
            kb = InlineKeyboardMarkup(row_width=2)
            kb.row(create_primary_button("🇬🇧 Eɴɢʟɪꜱʜ", callback_data="uh_setlang_en"),
                   create_primary_button("🇮🇳 हिन्दी", callback_data="uh_setlang_hi"))
            kb.add(create_primary_button("⬅️ Sᴇᴛᴛɪɴɢꜱ", callback_data="uh_settings"))
            _uh_edit_call(call, "<b>Choose your preferred language.</b>\nThe bot's existing command responses remain unchanged.", kb)
        elif data in ("uh_setlang_en", "uh_setlang_hi"):
            lang = "English" if data.endswith("_en") else "Hindi"
            _USER_HUB_SETTINGS.update_one({"user_id": uid}, {"$set": {"language": lang}}, upsert=True)
            bot.answer_callback_query(call.id, "Language preference saved.")
            text, kb = _uh_settings_text(uid)
            _uh_edit_call(call, text, kb)
            return
        elif data in ("uh_toggle_notifications", "uh_toggle_tips"):
            key = "notifications" if data.endswith("notifications") else "tips"
            current = _uh_get_settings(uid)[key]
            _USER_HUB_SETTINGS.update_one({"user_id": uid}, {"$set": {key: not current}}, upsert=True)
            text, kb = _uh_settings_text(uid)
            _uh_edit_call(call, text, kb)
        elif data == "uh_notifications":
            s = _uh_get_settings(uid)
            kb = InlineKeyboardMarkup()
            kb.add(create_success_button("Tᴜʀɴ ɴᴏᴛɪꜰɪᴄᴀᴛɪᴏɴꜱ ON" if not s["notifications"] else "Tᴜʀɴ ɴᴏᴛɪꜰɪᴄᴀᴛɪᴏɴꜱ OFF",
                                          callback_data="uh_toggle_notifications"))
            kb.add(create_primary_button("⬅️ Uꜱᴇʀ Hᴜʙ", callback_data="uh_home"))
            _uh_edit_call(call, f"<b>🔔 NOTIFICATION PREFERENCES</b>\nCurrently: {'ON' if s['notifications'] else 'OFF'}", kb)
        elif data == "uh_favorites":
            kb = InlineKeyboardMarkup(row_width=1)
            kb.add(create_success_button("➕ Sᴀᴠᴇ ᴀ Sʜᴏʀᴛᴄᴜᴛ", callback_data="uh_add_favorite"))
            kb.add(create_danger_button("🗑 Cʟᴇᴀʀ Fᴀᴠᴏʀɪᴛᴇꜱ", callback_data="uh_clear_favorites"))
            kb.add(create_primary_button("⬅️ Uꜱᴇʀ Hᴜʙ", callback_data="uh_home"))
            _uh_edit_call(call, _uh_favorites_text(uid), kb)
        elif data == "uh_add_favorite":
            _USER_HUB_STATE[uid] = {"action": "favorite", "chat_id": chat_id, "message_id": call.message.message_id}
            _uh_edit_call(call, "<b>Send a short name for your saved shortcut.</b>\nExample: GitHub lookup or My usual tool. Do not include passwords or private data.", _uh_back_keyboard())
        elif data == "uh_clear_favorites":
            kb = InlineKeyboardMarkup()
            kb.add(create_danger_button("Yᴇꜱ, ᴄʟᴇᴀʀ ᴍʏ ꜰᴀᴠᴏʀɪᴛᴇꜱ", callback_data="uh_confirm_clear_favorites"))
            kb.add(create_primary_button("Cᴀɴᴄᴇʟ", callback_data="uh_favorites"))
            _uh_edit_call(call, "Are you sure you want to clear all saved shortcuts?", kb)
        elif data == "uh_confirm_clear_favorites":
            _USER_HUB_FAVORITES.delete_many({"user_id": uid})
            _uh_edit_call(call, "✅ Your saved shortcuts have been cleared.", _uh_back_keyboard())
        elif data == "uh_activity":
            _uh_edit_call(call, _uh_activity_text(uid), _uh_back_keyboard())
        elif data == "uh_rewards":
            doc = get_user(uid) or {}
            count = int(doc.get("referral_count", 0) or 0)
            link = f"https://t.me/{bot.get_me().username}?start=ref_{uid}"
            _uh_edit_call(call,
                "<blockquote><b>🎁 REFERRALS & REWARDS</b>\n"
                f"Successful referrals: <code>{count}</code>\n"
                f"Your referral reward: <code>{REFERRAL_BONUS_REFERRER}</code> credits per eligible referral\n"
                f"Friend reward: <code>{REFERRAL_BONUS_NEW}</code> credits\n"
                f"Your link:\n<code>{_html.escape(link)}</code>\n"
                "Rewards are credited under the bot's existing referral rules.</blockquote>", _uh_back_keyboard())
        elif data == "uh_support":
            text, kb = _uh_support_text()
            _uh_edit_call(call, text, kb)
        elif data == "uh_new_ticket":
            _USER_HUB_STATE[uid] = {"action": "ticket", "chat_id": chat_id, "message_id": call.message.message_id}
            _uh_edit_call(call, "🎫 <b>Describe your issue in one message.</b>\nDo not include passwords, OTPs, API keys or sensitive personal data.", _uh_back_keyboard())
        elif data == "uh_my_tickets":
            docs = list(_USER_HUB_TICKETS.find({"user_id": uid}))
            docs.sort(key=lambda d: str(d.get("created_at", "")), reverse=True)
            lines = ["<blockquote><b>📋 YOUR SUPPORT TICKETS</b>"]
            if not docs:
                lines.append("You have not opened a ticket yet.")
            for d in docs[:8]:
                lines.append(f"#{d.get('ticket_id')} · {d.get('status', 'Open')} · {_html.escape(str(d.get('created_at', '')))}")
            lines.append("</blockquote>")
            _uh_edit_call(call, "\n".join(lines), _uh_back_keyboard())
        elif data == "uh_feedback":
            _USER_HUB_STATE[uid] = {"action": "feedback", "chat_id": chat_id, "message_id": call.message.message_id}
            _uh_edit_call(call, "📝 <b>Send your feedback or feature suggestion in one message.</b>", _uh_back_keyboard())
        elif data == "uh_premium":
            doc = get_user(uid) or {}
            active = bool(doc.get("premium_until"))
            _uh_edit_call(call,
                "<blockquote><b>💎 SHOWN LEGACY PREMIUM</b>\n"
                f"Your plan: <b>{'Premium entitlement recorded' if active else 'Free'}</b>\n\n"
                "The core bot remains free. Premium membership can be purchased through the verified payment menu.\n"
                "Use /upgrade to view available payment methods. Never send payment details or screenshots to an admin.</blockquote>", _uh_back_keyboard())
        elif data == "uh_search":
            _USER_HUB_STATE[uid] = {"action": "command_search", "chat_id": chat_id, "message_id": call.message.message_id}
            _uh_edit_call(call, "<b>🔎 SMART COMMAND SEARCH</b>\nType a feature, keyword or command name. Example: Instagram, GitHub, IP, email or /num.", _uh_back_keyboard())
        elif data == "uh_assistant":
            kb = InlineKeyboardMarkup(row_width=2)
            kb.row(create_primary_button("👤 Pʀᴏꜰɪʟᴇ", callback_data="uh_profile"),
                   create_primary_button("💎 Cʀᴇᴅɪᴛꜱ & Uꜱᴀɢᴇ", callback_data="uh_usage"))
            kb.row(create_primary_button("⭐ Sᴀᴠᴇᴅ Iᴛᴇᴍꜱ", callback_data="uh_favorites"),
                   create_primary_button("🎫 Sᴜᴘᴘᴏʀᴛ", callback_data="uh_support"))
            kb.add(create_primary_button("🔎 Fɪɴᴅ A Cᴏᴍᴍᴀɴᴅ", callback_data="uh_search"))
            kb.add(create_primary_button("⬅️ Uꜱᴇʀ Hᴜʙ", callback_data="uh_home"))
            _uh_edit_call(call, "<blockquote><b>🤖 SMART ASSISTANT</b>\nChoose what you need and I'll open the matching section. For bot commands, use Smart Search. Sensitive actions still require your confirmation.</blockquote>", kb)
        elif data == "uh_usage":
            _uh_edit_call(call, _uh_usage_text(uid), _uh_back_keyboard())
        elif data == "uh_achievements":
            _uh_edit_call(call, _uh_achievements_text(uid), _uh_back_keyboard())
        elif data == "uh_inbox":
            kb = InlineKeyboardMarkup()
            kb.add(create_success_button("✅ Mᴀʀᴋ Aʟʟ Rᴇᴀᴅ", callback_data="uh_mark_all_read"))
            kb.add(create_primary_button("⬅️ Uꜱᴇʀ Hᴜʙ", callback_data="uh_home"))
            _uh_edit_call(call, _uh_notifications_text(uid), kb)
        elif data == "uh_mark_all_read":
            _USER_HUB_NOTIFICATIONS.update_many({"user_id": uid}, {"$set": {"read": True}})
            _uh_edit_call(call, _uh_notifications_text(uid), _uh_back_keyboard())
        elif data.startswith("uh_cmd_"):
            slug = data[len("uh_cmd_"):]
            item = next((x for x in _uh_command_catalog()
                         if re.sub(r"[^a-z0-9]+", "_", x["command"].lstrip("/").casefold()).strip("_") == slug), None)
            if not item:
                bot.answer_callback_query(call.id, "This command is no longer available.", True)
                return
            _uh_edit_call(call,
                f"<blockquote><b>{_html.escape(item['label'])}</b>\n"
                f"Command: <code>{_html.escape(item['command'])}</code>\n"
                f"{_html.escape(item['prompt'])}</blockquote>\n"
                "Use the matching command or its main-menu button to continue.", _uh_back_keyboard())
        else:
            bot.answer_callback_query(call.id, "Unknown User Hub option.", True)
            return
        bot.answer_callback_query(call.id)
    except Exception as exc:
        logging.exception("[USER_HUB_CALLBACK] %s", exc)
        try:
            bot.answer_callback_query(call.id, "Could not complete this action. Please try again.", True)
        except Exception:
            pass


@bot.callback_query_handler(func=lambda call: bool(call.data and call.data.startswith("uh_")))
def user_hub_callback(call):
    _uh_callback(call)


@bot.message_handler(func=lambda m: bool(m and m.chat and m.chat.type == "private"
    and m.from_user and m.from_user.id in _USER_HUB_STATE
    and m.from_user.id not in ADMIN_STATE
    and m.text and not m.text.startswith("/")))
def user_hub_input_handler(message):
    uid = int(message.from_user.id)
    chat_id = message.chat.id
    state = _USER_HUB_STATE.pop(uid, {})
    action = state.get("action")
    value = (message.text or "").strip()
    target_chat = state.get("chat_id", chat_id)
    target_message = state.get("message_id")
    def _uh_input_result(text, markup=None):
        if target_message:
            _USER_HUB_MESSAGE[uid] = (target_chat, target_message)
            return _uh_edit_target(target_chat, target_message, text, markup)
        return _uh_send(chat_id, text, markup)
    if not value:
        _uh_input_result( "Please send some text.", _uh_back_keyboard())
        return
    if action == "command_search":
        matches = _uh_find_commands(value)
        if not matches:
            _uh_input_result( "No matching command found. Try a shorter keyword such as GitHub, Instagram, IP or email.", _uh_back_keyboard())
            return
        kb = InlineKeyboardMarkup(row_width=1)
        for item in matches:
            slug = re.sub(r"[^a-z0-9]+", "_", item["command"].lstrip("/").casefold()).strip("_")
            kb.add(create_primary_button(
                _admin_small_caps(f"{item['label']} · {item['command']}"),
                callback_data=f"uh_cmd_{slug}"
            ))
        kb.add(create_primary_button("⬅️ Uꜱᴇʀ Hᴜʙ", callback_data="uh_home"))
        lines = ["<blockquote><b>🔎 SEARCH RESULTS</b>"]
        for item in matches:
            lines.append(f"• {_html.escape(item['label'])} — <code>{_html.escape(item['command'])}</code>")
        lines.append("</blockquote>Choose a result to see how to use it.")
        _uh_input_result( "\n".join(lines), kb)
    elif action == "favorite":
        if len(value) > 80:
            _uh_input_result( "Shortcut name must be 80 characters or fewer.", _uh_back_keyboard())
            return
        _USER_HUB_FAVORITES.insert_one({
            "user_id": uid, "label": value, "created_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        })
        _uh_input_result( "✅ Shortcut saved.", _uh_back_keyboard())
    elif action == "ticket":
        ticket_id = "".join(random.choices(string.ascii_uppercase + string.digits, k=8))
        created = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        _USER_HUB_TICKETS.insert_one({
            "ticket_id": ticket_id, "user_id": uid, "message": value[:2500],
            "status": "Open", "created_at": created
        })
        username = message.from_user.username or "not set"
        safe_text = _html.escape(value[:2500])
        _uh_notify_admins(
            f"<b>🎫 NEW SUPPORT TICKET #{ticket_id}</b>\n"
            f"User: <code>{uid}</code> · @{_html.escape(username)}\n"
            f"Time: <code>{created}</code>\n\n{safe_text}"
        )
        _uh_input_result( f"✅ Ticket <code>#{ticket_id}</code> created. Support has been notified where admin messages are available.", _uh_back_keyboard())
    elif action == "feedback":
        created = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        _USER_HUB_FEEDBACK.insert_one({"user_id": uid, "message": value[:2500], "created_at": created})
        username = message.from_user.username or "not set"
        _uh_notify_admins(
            f"<b>📝 USER FEEDBACK</b>\nUser: <code>{uid}</code> · @{_html.escape(username)}\n"
            f"Time: <code>{created}</code>\n\n{_html.escape(value[:2500])}"
        )
        _uh_input_result( "✅ Thank you! Your feedback has been submitted.", _uh_back_keyboard())




@bot.callback_query_handler(func=lambda call: not (call.data or "").startswith("v5_"))
def callback_handler(call):
    global BOT_LOCKED, FORCE_JOIN_ENABLED
    try:
        if call.data.startswith("dljson_"):
            file_id = call.data.replace("dljson_", "")
            json_file = JSON_FILES.get(file_id)
            if not json_file:
                bot.answer_callback_query(call.id, "❌ File expired or not found!", True)
                return
            if os.path.exists(json_file):
                _safe_call(bot.answer_callback_query, call.id, "✅ JSON file sent!")
                with open(json_file, 'rb') as f:
                    bot.send_document(call.message.chat.id, f,
                                      caption=premium_caption(f"\U0001f4c2 <b>{sc('JSON Export')}</b>"),
                                      parse_mode="HTML")
            else:
                bot.answer_callback_query(call.id, "❌ File not found!", True)
            return

        if call.data.startswith("viewall_"):
            username = call.data.replace("viewall_", "")
            posts = POSTS_CACHE.get(username, [])
            if posts:
                bot.answer_callback_query(call.id, f"📸 Sending {len(posts)} posts...")
                send_all_posts(call.message.chat.id, username, posts)
            else:
                bot.answer_callback_query(call.id, "❌ No posts found!", True)
            return

        if call.data == "close_insta" or call.data == "no_posts" or call.data == "close_result":
            try:
                bot.delete_message(call.message.chat.id, call.message.message_id)
            except:
                pass
            bot.answer_callback_query(call.id)
            return

        if call.data == "back_to_result":
            bot.answer_callback_query(call.id, "✅ Use the command again to see results", True)
            return

        if call.data == "check_join":
            user_id = call.from_user.id
            chat_id = call.message.chat.id

            if check_subscription(user_id):
                bot.answer_callback_query(call.id, "✅ Verification successful!", True)
                try:
                    bot.delete_message(chat_id, call.message.message_id)
                except:
                    pass
            else:
                bot.answer_callback_query(call.id, "❌ Please join all channels first!", True)
            return

        # ── addc inline confirm / skip ──────────────────────────
        # Step 1: "Yes, Add It" → show 2 mode buttons
        if call.data.startswith("addc_confirm_"):
            if not is_admin(call.from_user.id):
                bot.answer_callback_query(call.id, "❌ Admin only!", True)
                return
            # format: addc_confirm_<pseudo_user>_<is_private>_<jreq_detected>
            try:
                payload     = call.data[len("addc_confirm_"):]
                parts_cb    = payload.rsplit("_", 2)
                pseudo_user = parts_cb[0]
                is_private  = parts_cb[1] == "1"
                # jreq_detected: Telegram already detected join_by_request on this channel
                jreq_detected = parts_cb[2] == "1"

                # Build mode-select prompt
                txt = (
                    f"⚙️ <b>Select Join Mode</b>\n\n"
                    f"👤 <b>Channel</b>: <code>{pseudo_user}</code>\n\n"
                    f"🌍 <b>Normal Join</b> — user joins directly, bot verifies membership\n\n"
                    f"🔐 <b>Request to Join</b> — user sends join request, bot lets them through "
                    f"as soon as request is sent (no admin approval needed)"
                )
                markup = InlineKeyboardMarkup()
                markup.row(
                    create_success_button(
                        "🌍 Nᴏʀᴍᴀʟ Jᴏɪɴ",
                        callback_data=f"addc_mode_{pseudo_user}_{int(is_private)}_0"
                    ),
                    create_primary_button(
                        "🔐 Rᴇǫᴜᴇꜱᴛ ᴛᴏ Jᴏɪɴ",
                        callback_data=f"addc_mode_{pseudo_user}_{int(is_private)}_1"
                    )
                )
                markup.add(create_danger_button("❌ Cᴀɴᴄᴇʟ", callback_data="addc_skip"))
                bot.answer_callback_query(call.id)
                try:
                    bot.edit_message_text(
                        txt,
                        call.message.chat.id,
                        call.message.message_id,
                        reply_markup=markup,
                        parse_mode='HTML'
                    )
                except Exception:
                    send_with_premium(call.message.chat.id, txt, reply_markup=markup, parse_mode='HTML')
            except Exception as cb_e:
                bot.answer_callback_query(call.id, f"❌ Error: {cb_e}", True)
            return

        # Step 2: mode selected → actually add the channel
        if call.data.startswith("addc_mode_"):
            if not is_admin(call.from_user.id):
                bot.answer_callback_query(call.id, "❌ Admin only!", True)
                return
            try:
                payload  = call.data[len("addc_mode_"):]
                parts_cb = payload.rsplit("_", 1)
                token    = parts_cb[0]
                jreq     = parts_cb[1] == "1"   # 0=Normal, 1=Request

                cached = ADDC_LINK_CACHE.pop(token, None)
                if not cached:
                    bot.answer_callback_query(call.id, "❌ Session expired. Run /addc again.", True)
                    return

                chat_id_num = cached["chat_id"]
                url         = cached["link"]          # EXACT link admin typed — never regenerated
                is_private  = cached["is_private"]
                pseudo_user = str(chat_id_num)

                success, result_msg = add_force_join_channel_extended(
                    url, pseudo_user, call.from_user.id, is_private, jreq)

                if success:
                    mode_lbl = "🔐 Request to Join" if jreq else "🌍 Normal Join"
                    note = ""
                    if jreq:
                        note = ("\n\n💡 <b>How it works</b>: User sends join request → "
                                "bot immediately grants access without waiting for admin approval.")
                    bot.answer_callback_query(call.id, "✅ Channel Added!", True)
                    try:
                        bot.edit_message_text(
                            f"✅ <b>Channel Added!</b>\n\n"
                            f"🔗 <b>URL</b>: <code>{url}</code>\n"
                            f"🆔 <b>Chat ID</b>: <code>{chat_id_num}</code>\n"
                            f"⚙️ <b>Mode</b>: {mode_lbl}"
                            f"{note}",
                            call.message.chat.id,
                            call.message.message_id,
                            parse_mode='HTML'
                        )
                    except Exception:
                        pass
                else:
                    bot.answer_callback_query(call.id, f"❌ {result_msg}", True)
            except Exception as cb_e:
                bot.answer_callback_query(call.id, f"❌ Error: {cb_e}", True)
            return

        if call.data == "addc_skip":
            bot.answer_callback_query(call.id, "Cancelled.", True)
            try:
                bot.delete_message(call.message.chat.id, call.message.message_id)
            except Exception:
                pass
            return
        # ── end addc ────────────────────────────────────────────

        # ── leak pagination ─────────────────────────────────────
        if call.data.startswith("leak_page_"):
            if not is_admin(call.from_user.id):
                # any user can page through their own result stored in NUM_PAGINATION
                pass
            try:
                # format: leak_page_<page_idx>_<user_id>
                parts_lk = call.data[len("leak_page_"):].rsplit("_", 1)
                page_idx = int(parts_lk[0])
                uid_key  = int(parts_lk[1]) if parts_lk[1].isdigit() else call.from_user.id
                state    = NUM_PAGINATION.get(uid_key) or NUM_PAGINATION.get(call.from_user.id)
                if not state:
                    bot.answer_callback_query(call.id, "❌ Session expired, run /leak again", True)
                    return
                pages = state["pages"]
                if page_idx < 0 or page_idx >= len(pages):
                    bot.answer_callback_query(call.id, "❌ No such page", True)
                    return
                txt, _ = pages[page_idx]
                total_pages = len(pages)
                markup = InlineKeyboardMarkup(row_width=3)
                btns = []
                if page_idx > 0:
                    btns.append(create_primary_button(
                        "◀ Pʀᴇᴠ",
                        callback_data=f"leak_page_{page_idx - 1}_{call.from_user.id}",
                        icon_custom_emoji_id="5246794802560774143"
                    ))
                btns.append(create_success_button(
                    f"{page_idx + 1}/{total_pages}",
                    callback_data="noop",
                    icon_custom_emoji_id="5422537279400868395"
                ))
                if page_idx < total_pages - 1:
                    btns.append(create_danger_button(
                        "Nᴇxᴛ ▶",
                        callback_data=f"leak_page_{page_idx + 1}_{call.from_user.id}",
                        icon_custom_emoji_id="6192763368139397161"
                    ))
                if btns:
                    markup.row(*btns)
                # JSON on last page
                json_file = state.get("json_file")
                if page_idx == total_pages - 1 and json_file:
                    file_id = hashlib.md5(json_file.encode()).hexdigest()[:16]
                    JSON_FILES[file_id] = json_file
                    markup.add(InlineKeyboardButton("📥 Download JSON", callback_data=f"dljson_{file_id}"))
                bot.answer_callback_query(call.id)
                try:
                    bot.edit_message_text(
                        replace_with_premium_emojis(txt),
                        call.message.chat.id,
                        call.message.message_id,
                        reply_markup=markup,
                        parse_mode='HTML'
                    )
                except Exception:
                    send_with_premium(call.message.chat.id, txt, reply_markup=markup)
            except Exception as lk_e:
                bot.answer_callback_query(call.id, f"❌ {lk_e}", True)
            return
        # ── end leak pagination ─────────────────────────────────

        if call.data == "help":
            class FakeMsg:
                def __init__(self, cid, uid):
                    self.chat = type('obj', (), {'id': cid})
                    self.from_user = type('obj', (), {'id': uid})
                    self.text = "/help"
                    self.date = int(datetime.now().timestamp())
            help_cmd(FakeMsg(call.message.chat.id, call.from_user.id))
            bot.answer_callback_query(call.id)
            return

        if call.data == "profile":
            class FakeMsg:
                def __init__(self, cid, uid):
                    self.chat = type('obj', (), {'id': cid})
                    self.from_user = type('obj', (), {'id': uid})
                    self.text = "/profile"
                    self.date = int(datetime.now().timestamp())
            profile_cmd(FakeMsg(call.message.chat.id, call.from_user.id))
            bot.answer_callback_query(call.id)
            return

        if call.data == "balance":
            class FakeMsg:
                def __init__(self, cid, uid):
                    self.chat = type('obj', (), {'id': cid})
                    self.from_user = type('obj', (), {'id': uid})
                    self.text = "/balance"
                    self.date = int(datetime.now().timestamp())
            balance_cmd(FakeMsg(call.message.chat.id, call.from_user.id))
            bot.answer_callback_query(call.id)
            return

        bot.answer_callback_query(call.id)
    except Exception as e:
        print(f"❌ Callback error: {e}")

def is_recent_command(message):
    # Telegram updates can carry a timestamp from a different timezone or be
    # delayed by long-polling. Do not silently discard a real user command.
    return True

def clear_pending_updates():
    global LAST_PROCESSED_UPDATE_ID
    try:
        updates = bot.get_updates(limit=1, timeout=1)
        if updates:
            LAST_PROCESSED_UPDATE_ID = updates[-1].update_id
            bot.get_updates(offset=LAST_PROCESSED_UPDATE_ID + 1, limit=1, timeout=1)
    except Exception as e:
        pass

# ═══════════════════════════════════════════════════════════════
# CHANNEL → BROADCAST FEATURE
# When admin posts anything in BROADCAST_CHANNEL_ID,
# bot forwards that exact message to every user + group.
# ═══════════════════════════════════════════════════════════════

def _do_channel_broadcast(origin_chat_id: int, origin_msg_id: int):
    """Forward a channel post to all users and group chats."""
    all_targets = set()

    # collect users
    try:
        for doc in _col_users.find({}, {"user_id": 1}):
            all_targets.add(doc["user_id"])
    except Exception:
        pass

    # collect groups
    try:
        for gcid in get_all_group_chats():
            all_targets.add(gcid)
    except Exception:
        pass

    success = 0
    fail    = 0
    total   = len(all_targets)
    logger.info(f"[ChannelBroadcast] forwarding msg {origin_msg_id} from {origin_chat_id} → {total} targets")

    for target in all_targets:
        try:
            bot.forward_message(
                chat_id=target,
                from_chat_id=origin_chat_id,
                message_id=origin_msg_id,
                disable_notification=True,
            )
            success += 1
        except Exception as e:
            fail += 1
        time.sleep(0.05)   # ~20 msg/s — stays under Telegram limits

    logger.info(f"[ChannelBroadcast] done — success={success} fail={fail}")

    # notify admin
    try:
        bot.send_message(
            ADMIN_ID,
            f"📢 <b>Channel Broadcast Done</b>\n\n"
            f"✅ Sent: <b>{success}</b>\n"
            f"❌ Failed: <b>{fail}</b>\n"
            f"📊 Total: <b>{total}</b>",
            parse_mode="HTML"
        )
    except Exception:
        pass


@bot.channel_post_handler(func=lambda m: True)
def on_channel_post(message):
    """Triggered for every post in any channel where the bot is admin."""
    global BROADCAST_CHANNEL_ID

    print(f"[CHANNEL] post in {message.chat.id} — {message.chat.title}")

    # first channel the bot is admin in becomes the user archive
    if TG_STORE_CHANNEL_ID is None:
        set_store_channel(message.chat.id)
        try:
            send_with_premium(
                message.chat.id,
                f"✅ <b>Archive channel linked</b>\n"
                f"<code>{message.chat.id}</code>\n\n"
                f"Every new user now lands here as a card + data file.",
                parse_mode="HTML")
        except Exception:
            pass

    if BROADCAST_CHANNEL_ID is None:
        return
    if message.chat.id != int(BROADCAST_CHANNEL_ID):
        return

    # run in background so the handler returns immediately
    t = Thread(
        target=_do_channel_broadcast,
        args=(message.chat.id, message.message_id),
        daemon=True,
    )
    t.start()


# ── Admin commands to manage the broadcast channel on the fly ──

@bot.message_handler(commands=['setstore'])
def setstore_cmd(message):
    """/setstore <chat_id> — point the user archive at a channel."""
    if not is_admin(message.from_user.id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return
    parts = message.text.split(maxsplit=1)

    # reply to a message forwarded from the channel -> adopt that channel
    fwd = getattr(message.reply_to_message, "forward_from_chat", None) if message.reply_to_message else None
    if len(parts) < 2 and fwd is not None:
        set_store_channel(fwd.id)
        send_with_premium(
            message.chat.id,
            f"✅ <b>Archive channel set</b>\n"
            f"<code>{fwd.id}</code> — {fwd.title}\n\n"
            f"Run <code>/exportusers</code> to dump everyone.",
            parse_mode="HTML")
        return

    if len(parts) < 2:
        cur = TG_STORE_CHANNEL_ID or "not set"
        send_with_premium(
            message.chat.id,
            f"<b>📥 Archive channel</b>\n"
            f"Current: <code>{cur}</code>\n\n"
            f"Usage: <code>/setstore -1001234567890</code>\n"
            f"Easier: post anything in the channel — the bot adopts it.",
            parse_mode="HTML")
        return
    try:
        cid = int(parts[1].strip())
    except ValueError:
        send_with_premium(message.chat.id,
                          "❌ Send the numeric id, e.g. <code>-1001234567890</code>",
                          parse_mode="HTML")
        return
    set_store_channel(cid)
    send_with_premium(
        message.chat.id,
        f"✅ <b>Archive channel set</b>\n"
        f"<code>{cid}</code>\n\n"
        f"Make sure the bot is admin there, then run <code>/exportusers</code>.",
        parse_mode="HTML")


@bot.message_handler(commands=['setbc'])
def setbc_cmd(message):
    """
    /setbc <channel_id>
    Set which channel triggers auto-broadcast.
    Use the channel's numeric ID (e.g. -1001234567890).
    The bot must already be an admin in that channel.
    """
    global BROADCAST_CHANNEL_ID
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2:
        send_with_premium(
            message.chat.id,
            "❌ Usage: <code>/setbc -1001234567890</code>\n\n"
            "Send the channel's numeric chat_id.\n"
            "Bot must be admin in that channel.",
            parse_mode="HTML"
        )
        return

    raw = parts[1].strip()
    try:
        cid = int(raw)
    except ValueError:
        send_with_premium(message.chat.id, "❌ That doesn't look like a valid chat_id. Use a number like <code>-1001234567890</code>.", parse_mode="HTML")
        return

    BROADCAST_CHANNEL_ID = cid
    send_with_premium(
        message.chat.id,
        f"✅ <b>Broadcast channel set!</b>\n\n"
        f"📢 Channel ID: <code>{cid}</code>\n\n"
        f"Any post you send to that channel will now auto-forward to all users + groups.",
        parse_mode="HTML"
    )
    logger.info(f"[setbc] admin {user_id} set BROADCAST_CHANNEL_ID={cid}")


@bot.message_handler(commands=['removebc'])
def removebc_cmd(message):
    """Disable the channel broadcast feature."""
    global BROADCAST_CHANNEL_ID
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return

    BROADCAST_CHANNEL_ID = None
    send_with_premium(message.chat.id, "✅ Channel broadcast disabled.")
    logger.info(f"[removebc] admin {user_id} disabled channel broadcast")


# ── /contact — Admin command: export all verified phone numbers as .txt ──────

def _fetch_all_verified_contacts():
    """
    Fetch all contact-verified users from MongoDB.
    Returns list of dicts: [{user_id, phone, username}]
    Sorted by phone_verified_at descending.
    """
    try:
        docs = list(
            _col_users.find(
                {"phone": {"$exists": True, "$nin": [None, ""]}},
                {"user_id": 1, "phone": 1, "phone_verified_at": 1,
                 "username": 1, "first_name": 1}
            ).sort("phone_verified_at", -1)
        )
        contacts = []
        for doc in docs:
            ph = str(doc.get("phone", "")).strip()
            if not ph:
                continue
            uid = str(doc.get("user_id", "")).strip()
            uname = str(doc.get("username", "") or doc.get("first_name", "")).strip() or "N/A"
            contacts.append({
                "user_id":  uid,
                "phone":    ph,
                "username": uname,
                "verified_at": str(doc.get("phone_verified_at", "N/A")),
            })
        return contacts
    except Exception as exc:
        logger.error(f"[_fetch_contacts] MongoDB error: {exc}")
        return []


# Keep old name as alias so nothing else breaks
turso_fetch_all_contacts = _fetch_all_verified_contacts





@bot.message_handler(commands=["contact"])
def contact_export_cmd(message):
    """
    /contact — Admin only.
    Exports all captcha-verified phone numbers from MongoDB as a .txt file.

    Format (tab-separated, one entry per line):
        UserID          Number
        1234567890      +919876543210
    """
    user_id = message.from_user.id
    if not is_admin(user_id):
        send_with_premium(message.chat.id, "❌ Admin only!")
        return

    processing_msg = None
    try:
        processing_msg = send_with_premium(
            message.chat.id,
            "⏳ <b>Contacts fetch ho rahe hain...</b>",
            parse_mode="HTML",
        )
    except Exception:
        pass

    contacts = _fetch_all_verified_contacts()

    if processing_msg:
        try:
            bot.delete_message(message.chat.id, processing_msg.message_id)
        except Exception:
            pass

    if not contacts:
        send_with_premium(
            message.chat.id,
            "❌ <b>No verified contacts found.</b>\n"
            "Abhi tak kisi ne bhi number verify nahi kiya.",
            parse_mode="HTML",
        )
        return

    # ── Build .txt content — clean aligned format ──────────────
    now_str  = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    total    = len(contacts)
    bar      = "━" * 42
    header   = (
        f"{bar}\n"
        f"  VERIFIED CONTACTS EXPORT\n"
        f"  Total  : {total}\n"
        f"  Date   : {now_str}\n"
        f"{bar}\n\n"
        f"{'UserID':<20}{'Number'}\n"
        f"{'-'*20}{'-'*20}\n"
    )

    rows = []
    for c in contacts:
        uid    = c.get("user_id",  "").strip() or "N/A"
        number = c.get("phone",    "").strip() or "N/A"
        # ensure number starts with +
        if number and number != "N/A" and not number.startswith("+"):
            number = "+" + number
        rows.append(f"{uid:<20}{number}")

    txt_content = header + "\n".join(rows) + f"\n\n{bar}\n"

    # ── Write temp file and send ────────────────────────────────
    tmp_path = f"/tmp/verified_contacts_{datetime.now().strftime('%Y%m%d_%H%M%S')}.txt"
    try:
        with open(tmp_path, "w", encoding="utf-8") as fh:
            fh.write(txt_content)

        caption = premium_caption(
            "<blockquote>"
            f"\U0001f4cb <b>{sc('Verified Contacts')}</b>\n\n"
            f"\u2705 <b>{sc('Total')}</b> : <b>{total}</b>\n"
            f"\U0001f4c5 <b>{sc('Date')}</b>  : <code>{now_str}</code>"
            "</blockquote>"
        )
        filename = f"contacts_{datetime.now().strftime('%Y%m%d')}.txt"

        with open(tmp_path, "rb") as fh:
            try:
                bot.send_document(
                    message.chat.id,
                    document=fh,
                    caption=caption,
                    parse_mode="HTML",
                    visible_file_name=filename,
                )
            except TypeError:
                fh.seek(0)
                bot.send_document(
                    message.chat.id,
                    document=InputFile(fh, file_name=filename),
                    caption=caption,
                    parse_mode="HTML",
                )

        logger.info(f"[/contact] admin {user_id} exported {total} contacts")

    except Exception as exc:
        send_with_premium(
            message.chat.id,
            f"❌ <b>Export failed:</b>\n<code>{exc}</code>",
            parse_mode="HTML",
        )
        logger.error(f"[/contact] export error: {exc}")
    finally:
        try:
            os.remove(tmp_path)
        except Exception:
            pass


# ── Admin welcome media upload (photo/video) ───────────────────
@bot.message_handler(content_types=["photo", "video"], func=lambda m: bool(m.from_user and m.from_user.id in ADMIN_STATE and (ADMIN_STATE.get(m.from_user.id) or {}).get("action") in ("welcome_photo", "welcome_video")))
def admin_welcome_media_input(message):
    uid = message.from_user.id
    chat_id = message.chat.id
    action = (ADMIN_STATE.get(uid) or {}).get("action")
    if not is_admin(uid):
        ADMIN_STATE.pop(uid, None)
        return
    expected = "photo" if action == "welcome_photo" else "video"
    if expected == "photo" and not message.photo:
        send_with_premium(chat_id, "❌ Please send a photo.")
        return
    if expected == "video" and not message.video:
        send_with_premium(chat_id, "❌ Please send a video.")
        return
    file_id = message.photo[-1].file_id if expected == "photo" else message.video.file_id
    caption = (message.caption or "Welcome!")[:900]
    _col_media_set.update_one({"setting_key": "welcome_config"},
        {"$set": {"mode": expected, "file_id": file_id, "text": caption, "updated_by": uid,
                  "updated_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S")}}, upsert=True)
    ADMIN_STATE.pop(uid, None)
    send_with_premium(chat_id, f"✅ {expected.title()} welcome saved. It will appear on the next /start.", reply_markup=_admin_back_kb())


# ── Admin panel: text input for button flows ────────────────────
@bot.message_handler(func=lambda m: (
    m.from_user and
    m.from_user.id in ADMIN_STATE and
    m.text
))
def admin_state_input(message):
    uid     = message.from_user.id
    chat_id = message.chat.id
    if not is_admin(uid):
        ADMIN_STATE.pop(uid, None)
        return
    action  = (ADMIN_STATE.get(uid) or {}).get("action")
    if not action:
        ADMIN_STATE.pop(uid, None)
        return
    raw = message.text.strip()

    if action in ("security_key_set_api", "security_key_set_clone"):
        kind = "api" if action.endswith("_api") else "clone"
        nav_key = re.sub(r"[^a-z0-9]+", "", raw.casefold())
        if raw.casefold() in {"/cancel", "cancel"} or nav_key in {"backtopanel", "backtoadmin", "adminpanel", "back"}:
            ADMIN_STATE.pop(uid, None)
            send_with_premium(chat_id, "Key update cancelled.", reply_markup=_admin_back_kb())
            if nav_key in {"backtopanel", "backtoadmin", "adminpanel", "back"}:
                _show_admin_reply_page(chat_id, 0)
            return
        admin_action_by_text = {
            re.sub(r"[^a-z0-9]+", "", str(label).casefold()): target
            for label, target in _ADMIN_REPLY_LABEL_TO_ACTION.items()
        }
        routed_action = admin_action_by_text.get(nav_key)
        if routed_action:
            ADMIN_STATE.pop(uid, None)
            _admin_reply_action(message, routed_action)
            return
        if uid not in ADMIN_IDS:
            ADMIN_STATE.pop(uid, None)
            send_with_premium(chat_id, "❌ Only the configured owner can manage encryption keys.")
            return
        try:
            # Reduce exposure of the secret in the admin chat history immediately.
            try: bot.delete_message(chat_id, message.message_id)
            except Exception: pass
            _security_key_set(kind, raw)
            ADMIN_STATE.pop(uid, None)
            _admin_audit("security_key_set", uid, kind)
            send_with_premium(chat_id, "✅ Encryption key saved on persistent disk. The value was not displayed. Verify it from Security & Keys.", reply_markup=_security_keys_keyboard())
        except Exception as exc:
            # Keep the input state active for a corrected retry; never echo the submitted secret.
            ADMIN_STATE[uid] = {"action": action}
            send_with_premium(chat_id, f"❌ Could not save key: {_html.escape(str(exc)[:220])}\nSend a corrected value or /cancel.", parse_mode="HTML", reply_markup=_admin_back_kb())
        return

    if action in ('secrole_add', 'secrole_remove'):
        if uid not in ADMIN_IDS:
            ADMIN_STATE.pop(uid, None)
            send_with_premium(chat_id, '❌ Only the configured owner can manage roles.')
            return
        if raw.casefold() in {'/cancel','cancel'}:
            ADMIN_STATE.pop(uid, None)
            send_with_premium(chat_id, 'Role operation cancelled.', reply_markup=_admin_back_kb())
            return
        try:
            if action == 'secrole_add':
                parts = raw.split()
                if len(parts) != 2 or parts[1].lower() not in {'super_admin','moderator'}:
                    raise ValueError('Format must be: USER_ID super_admin OR USER_ID moderator')
                target, role = int(parts[0]), parts[1].lower()
                if target <= 0:
                    raise ValueError('User ID must be a positive number.')
                if target in ADMIN_IDS:
                    raise ValueError('Configured owner accounts cannot be changed.')
                if not is_admin(target):
                    raise ValueError('User must already be an existing bot admin. Use the existing Make Admin function first.')
                _sec_roles_init()
                with _clone_db() as conn:
                    conn.execute('INSERT INTO admin_roles(user_id,role,assigned_by,assigned_at) VALUES(?,?,?,?) '
                                 'ON CONFLICT(user_id) DO UPDATE SET role=excluded.role,assigned_by=excluded.assigned_by,assigned_at=excluded.assigned_at',
                                 (target, role, uid, datetime.now().isoformat(timespec='seconds')))
                _admin_audit('admin_role_set', uid, f'user={target}; role={role}')
                result = f'✅ Role set: <code>{target}</code> → <b>{role.replace("_", " ").title()}</b>'
            else:
                target = int(raw)
                if target in ADMIN_IDS:
                    raise ValueError('Configured owner accounts cannot be changed.')
                _sec_roles_init()
                with _clone_db() as conn:
                    cur = conn.execute('DELETE FROM admin_roles WHERE user_id=?', (target,))
                if cur.rowcount:
                    result = f'✅ Explicit role removed for <code>{target}</code>. Existing legacy admin access remains unchanged.'
                    _admin_audit('admin_role_removed', uid, f'user={target}')
                else:
                    result = 'No explicit role assignment existed for that user.'
            ADMIN_STATE.pop(uid, None)
            send_with_premium(chat_id, result + '\n\n' + _sec_roles_text(), parse_mode='HTML', reply_markup=_sec_roles_keyboard())
        except Exception as exc:
            send_with_premium(chat_id, f'❌ {_html.escape(str(exc))}\nPlease try again or send /cancel.', parse_mode='HTML', reply_markup=_admin_back_kb())
        return

    if action == "suite_broadcast_message":
        if raw.casefold() in {"/cancel", "cancel"}:
            ADMIN_STATE.pop(uid, None)
            send_with_premium(chat_id, "Broadcast cancelled.", reply_markup=_admin_back_kb())
            return
        target = (ADMIN_STATE.get(uid) or {}).get("target", "all")
        ADMIN_STATE.pop(uid, None)
        recipients = []
        try:
            if target == "all":
                recipients = [int(d["user_id"]) for d in _col_users.find({}, {"user_id":1}) if d.get("user_id")]
            elif target == "active30":
                cutoff = (datetime.now() - timedelta(days=30)).strftime("%Y-%m-%d")
                recipients = [int(d["user_id"]) for d in _col_users.find({"last_active":{"$gte":cutoff}}, {"user_id":1}) if d.get("user_id")]
            elif target == "clones":
                # Each clone has a separate DB; this instance only manages process lifecycle.
                # Clone user delivery is not attempted without an isolated clone DB reader.
                send_with_premium(chat_id, "⚠️ Clone broadcast requires per-clone user-store enumeration; no clone messages were sent.", reply_markup=_admin_suite_keyboard("broadcast"))
                return
            sent = failed = 0
            for recipient in recipients:
                try:
                    bot.send_message(recipient, raw)
                    sent += 1
                except Exception:
                    failed += 1
            _admin_audit("broadcast", uid, f"target={target}; sent={sent}; failed={failed}")
            send_with_premium(chat_id, f"<blockquote><b>📢 BROADCAST REPORT</b>\nAudience: <code>{target}</code>\nAttempted: <code>{len(recipients)}</code>\nDelivered: <code>{sent}</code>\nFailed: <code>{failed}</code></blockquote>", parse_mode="HTML", reply_markup=_admin_suite_keyboard("broadcast"))
        except Exception as exc:
            send_with_premium(chat_id, f"❌ Broadcast failed: <code>{_html.escape(str(exc)[:180])}</code>", parse_mode="HTML", reply_markup=_admin_suite_keyboard("broadcast"))
        return

    if action == "clone_add_token":
        # Slash commands and reply-keyboard navigation must never be treated as tokens.
        def _clone_menu_key(value):
            return re.sub(r"[^a-z0-9]+", "", str(value).casefold())

        nav_key = _clone_menu_key(raw)
        if raw.casefold() in {"/cancel", "cancel"} or nav_key in {
            "backtopanel", "backtoadmin", "adminpanel", "menumenu",
            "back", "cancel"
        }:
            ADMIN_STATE.pop(uid, None)
            _show_admin_reply_page(chat_id, 0)
            return

        # Route every known admin reply-keyboard button out of token-entry mode.
        admin_action_by_text = {
            _clone_menu_key(label): target
            for label, target in _ADMIN_REPLY_LABEL_TO_ACTION.items()
        }
        routed_action = admin_action_by_text.get(nav_key)
        if routed_action:
            ADMIN_STATE.pop(uid, None)
            _admin_reply_action(message, routed_action)
            return

        # A token is the only input accepted in this state. A malformed value
        # keeps the prompt active, but does not poison later admin navigation.
        if not re.fullmatch(r"[0-9]{5,}:[A-Za-z0-9_-]{20,}", raw):
            send_with_premium(chat_id,
                "❌ This doesn't look like a Telegram bot token. Send the token from @BotFather, "
                "tap Back to Panel, or send /cancel.",
                reply_markup=_admin_back_kb())
            return
        try:
            clone_id, info, status = _clone_add_token(raw)
            ADMIN_STATE.pop(uid, None)
            send_with_premium(chat_id,
                f"✅ <b>CLONE REGISTERED</b>\nBot: @{_html.escape(info['username'])}\n"
                f"Clone ID: <code>{clone_id}</code>\nStatus: <code>{_html.escape(status)}</code>",
                parse_mode="HTML", reply_markup=_clone_manager_keyboard())
        except Exception as exc:
            ADMIN_STATE[uid] = {"action": "clone_add_token"}
            send_with_premium(chat_id,
                f"❌ Could not add clone: <code>{_html.escape(str(exc)[:220])}</code>\n"
                "Send a valid token or /cancel.", parse_mode="HTML", reply_markup=_admin_back_kb())
        return

    # While an API Manager prompt is active, allow its menu buttons to work
    # immediately instead of treating their labels as lookup commands/values.
    if action and action.startswith("api_mgr_"):
        # Match reply-keyboard labels independent of emoji variation selectors.
        def _menu_key(value):
            return re.sub(r"[^a-z0-9]+", "", str(value).casefold())

        api_action_by_text = {_menu_key(label): target for label, target in _API_MANAGER_ACTIONS.items()}
        next_api_action = api_action_by_text.get(_menu_key(raw))
        if next_api_action:
            _admin_reply_action(message, next_api_action)
            return
        if _menu_key(raw) in {"backtoadmin", "backadmin"}:
            ADMIN_STATE.pop(uid, None)
            _show_admin_reply_page(chat_id, 0)
            return
        # Allow other admin-page navigation buttons to escape an API prompt.
        admin_action_by_text = {
            _menu_key(label): target for label, target in _ADMIN_REPLY_LABEL_TO_ACTION.items()
        }
        next_admin_action = admin_action_by_text.get(_menu_key(raw))
        if next_admin_action:
            _admin_reply_action(message, next_admin_action)
            return

    ADMIN_STATE.pop(uid, None)

    def back_kb():
        kb = InlineKeyboardMarkup(row_width=1)
        kb.add(create_primary_button("⬅️ Back to Panel", callback_data="admin_panel"))
        return kb

    try:
        if action.startswith("api_mgr_"):
            parts = raw.split(maxsplit=1)
            if action == "api_mgr_endpoint":
                if len(parts) != 2:
                    ADMIN_STATE[uid] = {"action": action}
                    send_with_premium(chat_id, "❌ Format: <code>command https://...{query}&amp;key={key}</code>", parse_mode="HTML", reply_markup=_api_manager_keyboard())
                    return
                command, endpoint = parts[0].lstrip("/").lower(), parts[1].strip()
                ok, result = set_api_endpoint(command, endpoint, uid)
                send_with_premium(chat_id, ("✅ " if ok else "❌ ") + _html.escape(result), reply_markup=_api_manager_keyboard())
                return
            if action == "api_mgr_key":
                if len(parts) != 2 or len(parts[1]) > 500:
                    ADMIN_STATE[uid] = {"action": action}
                    send_with_premium(chat_id, "❌ Format: <code>command API_KEY</code>", parse_mode="HTML", reply_markup=_api_manager_keyboard())
                    return
                command, api_key = parts[0].lstrip("/").lower(), parts[1].strip()
                if command not in API_ENDPOINTS:
                    send_with_premium(chat_id, "❌ Unknown lookup command. Use an existing command from /api.", reply_markup=_api_manager_keyboard())
                    return
                try:
                    encrypted_key = _encrypt_api_key(api_key)
                except Exception as exc:
                    send_with_premium(chat_id, f"❌ Secure key storage unavailable. Install cryptography and configure API_CONFIG_ENCRYPTION_KEY. <code>{_html.escape(str(exc)[:120])}</code>", parse_mode="HTML", reply_markup=_api_manager_keyboard())
                    return
                _col_api_config.update_one({"command_name": command}, {"$set": {"api_key": encrypted_key, "updated_by": uid, "updated_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S")}}, upsert=True)
                _API_EP_CACHE.delete(command)
                send_with_premium(chat_id, f"✅ API key saved for <code>/{_html.escape(command)}</code>. The key is not echoed back.", parse_mode="HTML", reply_markup=_api_manager_keyboard())
                return
            command = raw.lstrip("/").split()[0].lower()
            if command not in API_ENDPOINTS:
                send_with_premium(chat_id, "❌ Unknown lookup command. Check 📋 List APIs.", reply_markup=_api_manager_keyboard())
                return
            if action in ("api_mgr_disable", "api_mgr_enable"):
                enabled = action == "api_mgr_enable"
                _col_api_config.update_one({"command_name": command}, {"$set": {"enabled": enabled, "updated_by": uid, "updated_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S")}}, upsert=True)
                _API_EP_CACHE.delete(command)
                send_with_premium(chat_id, f"{'🟢 Enabled' if enabled else '🔴 Disabled'} <code>/{_html.escape(command)}</code>.", parse_mode="HTML", reply_markup=_api_manager_keyboard())
                return
            if action == "api_mgr_remove":
                _col_api_config.delete_one({"command_name": command})
                _API_EP_CACHE.delete(command)
                send_with_premium(chat_id, f"🗑 Custom override and key removed for <code>/{_html.escape(command)}</code>. Built-in endpoint is restored.", parse_mode="HTML", reply_markup=_api_manager_keyboard())
                return
            if action == "api_mgr_test":
                if len(parts) != 2:
                    send_with_premium(chat_id, "❌ Format: <code>command sample_query</code>", parse_mode="HTML", reply_markup=_api_manager_keyboard())
                    return
                command, sample = parts[0].lstrip("/").lower(), parts[1]
                url = ep(command, sample)
                if not url:
                    send_with_premium(chat_id, "❌ No enabled endpoint is configured for this command.", reply_markup=_api_manager_keyboard())
                    return
                try:
                    response = requests.get(url, timeout=12, headers={"User-Agent": "ShownLegacy-API-Manager/1.0"})
                    send_with_premium(chat_id, f"<blockquote><b>🧪 API TEST</b>\nCommand: <code>/{_html.escape(command)}</code>\nHTTP status: <code>{response.status_code}</code>\nResponse type: <code>{_html.escape(response.headers.get('content-type', 'unknown'))}</code>\nResult: {'✅ reachable' if response.ok else '⚠️ provider returned an error'}\nResponse body is not displayed to avoid exposing personal data or secrets.</blockquote>", parse_mode="HTML", reply_markup=_api_manager_keyboard())
                except Exception as exc:
                    send_with_premium(chat_id, f"❌ Connection test failed: <code>{_html.escape(str(exc)[:180])}</code>", parse_mode="HTML", reply_markup=_api_manager_keyboard())
                return

        editable_fields = {
            "edit_help_text": "help_text",
            "edit_lookup_guide": "lookup_guide",
            "edit_support_text": "support_text",
        }
        if action in editable_fields:
            field = editable_fields[action]
            if len(raw) > 3500:
                ADMIN_STATE[uid] = {"action": action}
                send_with_premium(chat_id, "❌ Text is too long. Keep it under 3,500 characters and try again.", reply_markup=back_kb())
                return
            _col_media_set.update_one(
                {"setting_key": "editable_bot_texts"},
                {"$set": {field: raw, "updated_by": uid,
                           "updated_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S")}},
                upsert=True,
            )
            send_with_premium(chat_id, f"✅ Saved <b>{field.replace('_', ' ').title()}</b>. It will be used by /help immediately.", parse_mode="HTML", reply_markup=back_kb())
            return

        if action == "welcome_text":
            _col_media_set.update_one({"setting_key": "welcome_config"},
                {"$set": {"mode": "text", "text": raw[:3500], "updated_by": uid,
                          "updated_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S")}}, upsert=True)
            send_with_premium(chat_id, "✅ Text welcome saved. It will appear on the next /start.", reply_markup=back_kb())
            return

        if action == "backup_chat_id":
            try:
                target_chat = int(raw)
                # Verify bot access before saving the destination.
                bot.send_message(target_chat, "✅ WHOISSHOWN backup destination connected. You can enable 30-second backups from Admin Panel.")
                _col_media_set.update_one({"setting_key": "auto_backup_config"},
                    {"$set": {"chat_id": target_chat, "enabled": False, "updated_by": uid}}, upsert=True)
                send_with_premium(chat_id, f"✅ Backup group saved: <code>{target_chat}</code>\nNow open Auto Backup and enable it.", parse_mode="HTML", reply_markup=back_kb())
            except Exception as exc:
                send_with_premium(chat_id, f"❌ Could not access that group. Add the bot and grant permission to send documents.\n<code>{_html.escape(str(exc)[:250])}</code>", parse_mode="HTML", reply_markup=back_kb())
            return

        if action == "addallcredits":
            try:
                amount = int(raw)
                if amount <= 0 or amount > 100000000:
                    raise ValueError("Amount must be between 1 and 100,000,000")
                result = _col_users.update_many({}, {"$inc": {"credits": amount}})
                count = getattr(result, "modified_count", 0)
                send_with_premium(chat_id,
                    f"<blockquote>✅ <b>Credits distributed to all users</b>\nAmount per user: <code>{amount}</code>\nUsers updated: <code>{count}</code></blockquote>",
                    parse_mode="HTML", reply_markup=back_kb())
            except Exception as exc:
                send_with_premium(chat_id, f"❌ Invalid amount or database error: {_html.escape(str(exc)[:250])}", parse_mode="HTML", reply_markup=back_kb())
            return

        if action == "userhistory":
            target = raw.lstrip("@").strip()
            if target.isdigit():
                doc = _col_users.find_one({"user_id": int(target)})
            else:
                doc = None
                for candidate in _col_users.find({}, {"user_id": 1, "username": 1, "first_name": 1,
                                                       "join_date": 1, "last_active": 1, "credits": 1,
                                                       "is_blocked": 1, "total_commands": 1}):
                    if str(candidate.get("username", "")).lower() == target.lower():
                        doc = candidate
                        break
            if not doc:
                send_with_premium(chat_id, "❌ User not found.", reply_markup=back_kb())
                return
            uid2 = int(doc.get("user_id", 0))
            refs = _col_referrals.count_documents({"referrer_id": uid2})
            recent_searches = list(_col_search_history.find({"user_id": uid2}).sort("created_at", -1).limit(15))
            lines = [
                "<blockquote><b>🧾 ACCOUNT ACTIVITY</b>",
                f"ID: <code>{uid2}</code>",
                f"Username: @{_html.escape(str(doc.get('username', 'N/A')))}",
                f"Name: {_html.escape(str(doc.get('first_name', 'N/A')))}",
                f"Joined: <code>{_html.escape(str(doc.get('join_date', 'N/A')))}</code>",
                f"Last active: <code>{_html.escape(str(doc.get('last_active', 'N/A')))}</code>",
                f"Credits: <code>{doc.get('credits', 0)}</code>",
                f"Referrals: <code>{refs}</code>",
                f"Commands used (aggregate): <code>{doc.get('total_commands', 0)}</code>",
                f"Status: <code>{'Blocked' if doc.get('is_blocked') else 'Active'}</code>",
                "\n<b>🔎 RECENT SEARCH HISTORY (latest 15)</b>",
            ]
            if recent_searches:
                for entry in recent_searches:
                    cmd = _html.escape(str(entry.get("command", "")))
                    query = _html.escape(str(entry.get("query", ""))[:90])
                    when = _html.escape(str(entry.get("created_at", "")))
                    lines.append(f"<code>{when}</code> · <b>{cmd}</b> {query}")
            else:
                lines.append("No searches recorded yet. New searches will be logged from this update onward.")
            lines.append("</blockquote>")
            send_with_premium(chat_id, "\n".join(lines), parse_mode="HTML", reply_markup=back_kb())
            return

        # ── credits ─────────────────────────────────────────────
        if action in ("addcredits", "removecredits"):
            parts = raw.split()
            if len(parts) < 2:
                ADMIN_STATE[uid] = {"action": action}      # stay armed for a retry
                send_with_premium(chat_id, "❌ Send it as <code>user_id amount</code>", parse_mode="HTML")
                return
            target_id, amount = int(parts[0]), int(parts[1])
            if amount <= 0:
                ADMIN_STATE[uid] = {"action": action}
                send_with_premium(chat_id, "❌ Amount must be greater than 0")
                return
            if action == "addcredits":
                ok = add_credits(target_id, amount)
                verb = "Added"
            else:
                with db_lock:
                    _col_users.update_one({"user_id": target_id}, {"$inc": {"credits": -amount}})
                ok = True
                verb = "Removed"
            if not ok:
                send_with_premium(chat_id, f"❌ User <code>{target_id}</code> not found", parse_mode="HTML")
                return
            bal = get_credits(target_id)
            send_with_premium(
                chat_id,
                f"<blockquote>✅ <b>{verb} {amount} credits</b>\n"
                f"User: <code>{target_id}</code>\n"
                f"New balance: <code>{bal}</code></blockquote>",
                parse_mode="HTML", reply_markup=back_kb())
            if action == "addcredits":
                try:
                    send_with_premium(target_id, f"✅ Admin added {amount} credits!\n💰 New Balance: {bal}")
                except Exception:
                    pass
            return

        # ── block / unblock ─────────────────────────────────────
        if action in ("block", "unblock"):
            target_id = int(raw.split()[0])
            if target_id in ADMIN_IDS:
                send_with_premium(chat_id, "❌ Cannot touch an owner account")
                return
            ok = block_user_in_db(target_id) if action == "block" else unblock_user_in_db(target_id)
            if not ok:
                send_with_premium(chat_id, f"❌ User <code>{target_id}</code> not found", parse_mode="HTML")
                return
            label = "blocked 🚫" if action == "block" else "unblocked ✅"
            send_with_premium(chat_id,
                              f"<blockquote>✅ User <code>{target_id}</code> {label}</blockquote>",
                              parse_mode="HTML", reply_markup=back_kb())
            try:
                if action == "block":
                    send_with_premium(target_id, f"🚫 BANNED\n\nContact Admin: {OWNER_USERNAME}")
                else:
                    send_with_premium(target_id, "✅ You have been unblocked! You can use the bot again.")
            except Exception:
                pass
            return

        # ── promote / demote ────────────────────────────────────
        if action in ("makeadmin", "removeadmin"):
            target_id = int(raw.split()[0])
            if action == "removeadmin" and target_id in ADMIN_IDS:
                send_with_premium(chat_id, "❌ Cannot demote an owner account")
                return
            if not _col_users.find_one({"user_id": target_id}, {"_id": 1}):
                send_with_premium(chat_id, f"❌ User <code>{target_id}</code> not found", parse_mode="HTML")
                return
            flag = 1 if action == "makeadmin" else 0
            _col_users.update_one({"user_id": target_id}, {"$set": {"is_admin": flag}})
            _ADMIN_CACHE.set(target_id, bool(flag))
            label = "promoted to admin 👑" if flag else "demoted to user 👤"
            send_with_premium(chat_id,
                              f"<blockquote>✅ <code>{target_id}</code> {label}</blockquote>",
                              parse_mode="HTML", reply_markup=back_kb())
            try:
                send_with_premium(target_id, "👑 You are now an admin!" if flag else "👤 You are no longer an admin.")
            except Exception:
                pass
            return

        # ── broadcast ───────────────────────────────────────────
        if action == "broadcast":
            targets = set()
            try:
                for doc in _col_users.find({}, {"user_id": 1}):
                    targets.add(doc["user_id"])
            except Exception:
                pass
            try:
                for gcid in get_all_group_chats():
                    targets.add(gcid)
            except Exception:
                pass
            targets.discard(chat_id)
            sent = failed = 0
            for i, tid in enumerate(targets, 1):
                try:
                    send_with_premium(tid, raw)
                    sent += 1
                except Exception:
                    failed += 1
                if i % 25 == 0:
                    time.sleep(1)
            send_with_premium(
                chat_id,
                f"<blockquote><b>📢 BROADCAST DONE</b>\n"
                f"──────────────────────\n"
                f"✅ Sent    : <code>{sent}</code>\n"
                f"❌ Failed  : <code>{failed}</code></blockquote>",
                parse_mode="HTML", reply_markup=back_kb())
            return

        # ── set broadcast channel ───────────────────────────────
        if action == "setbc":
            global BROADCAST_CHANNEL_ID
            BROADCAST_CHANNEL_ID = int(raw.split()[0])
            send_with_premium(
                chat_id,
                f"<blockquote>✅ <b>Broadcast channel set</b>\n"
                f"📢 <code>{BROADCAST_CHANNEL_ID}</code></blockquote>",
                parse_mode="HTML", reply_markup=back_kb())
            print(f"[setbc] {uid} set BROADCAST_CHANNEL_ID={BROADCAST_CHANNEL_ID}")
            return
    except ValueError:
        ADMIN_STATE[uid] = {"action": action}
        send_with_premium(chat_id, "❌ Invalid input — send numbers only.", reply_markup=back_kb())
    except Exception as exc:
        print(f"[ADMIN_INPUT] {exc}")
        send_with_premium(chat_id, f"❌ Error: {exc}", reply_markup=back_kb())


# ── Private reply-keyboard actions (private chats only) ──
_PRIVATE_MENU_PROMPTS = {
    "📱 Number Lookup": ("/num", "Send a phone number, e.g. /num 9876543210"),
    "👤 Telegram User": ("/tguser", "Send a public Telegram username, e.g. /tguser username"),
    "🆔 My Telegram ID": ("/myid", "This shows your own Telegram numeric ID."),
    "📸 Instagram Lookup": ("/insta", "Send a public Instagram username, e.g. /insta username"),
    "🐙 GitHub Lookup": ("/git", "Send a public GitHub username, e.g. /git octocat"),
    "🎮 Free Fire Lookup": ("/ff", "Send a Free Fire player UID, e.g. /ff PLAYER_UID"),
    "🎯 BGMI Lookup": ("/bgmi", "Send a BGMI player identifier, e.g. /bgmi PLAYER_ID"),
    "🌐 IP Lookup": ("/ip", "Send an IP address, e.g. /ip 8.8.8.8"),
    "🔗 Domain Lookup": ("/domain", "Send a domain, e.g. /domain example.com"),
    "📮 PIN Code Lookup": ("/pin", "Send a PIN code, e.g. /pin 400064"),
    "📧 Email Lookup": ("/email", "Send an email address using /email address@example.com. Only use an address you are authorised to check."),
    "🔎 OSINT Lookup": ("/osint", "Send a public identifier using /osint identifier. Do not submit private or sensitive personal data."),
    "🪪 ID Verification Guide": (None, "For Aadhaar/PAN verification, use only official UIDAI/Income Tax services and the document holder's consent. This bot does not retrieve private identity records. Aadhaar number format: 12 digits; PAN format: 5 letters + 4 digits + 1 letter."),
}

def _api_manager_keyboard():
    kb = types.ReplyKeyboardMarkup(row_width=2, resize_keyboard=True, one_time_keyboard=False)
    kb.row(_KB("📋 List APIs", style="primary"), _KB("➕ Add / Edit Provider", style="primary"))
    kb.row(_KB("🔑 Set API Key", style="success"), _KB("🧪 Test API", style="success"))
    kb.row(_KB("⏸ Disable API", style="danger"), _KB("▶️ Enable API", style="success"))
    kb.row(_KB("🗑 Remove Override", style="danger"))
    kb.row(_KB("⬅️ Back to Admin", style="primary"))
    return kb

_API_MANAGER_ACTIONS = {
    "📋 List APIs": "api_mgr_list", "➕ Add / Edit Provider": "api_mgr_endpoint",
    "🔑 Set API Key": "api_mgr_key", "🧪 Test API": "api_mgr_test",
    "⏸ Disable API": "api_mgr_disable", "▶️ Enable API": "api_mgr_enable",
    "🗑 Remove Override": "api_mgr_remove",
}

def _api_manager_list_text():
    lines = ["<blockquote><b>🔌 API MANAGER — EXISTING LOOKUPS</b>"]
    for cmd, template in sorted((API_ENDPOINTS or {}).items()):
        cfg = get_api_config(cmd)
        active = cfg.get("enabled", True)
        endpoint = cfg.get("api_endpoint") or template
        if not endpoint:
            status = "⚪ not configured"
        else:
            status = "🟢 enabled" if active else "🔴 disabled"
        source = "custom override" if cfg.get("api_endpoint") else "built-in"
        lines.append(f"{status} <b>/{_html.escape(cmd)}</b> · {source}")
    lines.append("\n🔐 Keys and full endpoint URLs are hidden. Use Add / Edit Provider or Set API Key to change configuration.</blockquote>")
    return "\n".join(lines)

def _api_manager_prompt(chat_id, uid, action, prompt):
    ADMIN_STATE[uid] = {"action": action}
    send_with_premium(chat_id, prompt + "\nUse Back to Admin to cancel.", reply_markup=_api_manager_keyboard())

def _admin_reply_action(message, action):
    """Run the same top-level admin actions from reply-keyboard text buttons."""
    uid, chat_id = message.from_user.id, message.chat.id
    if message.chat.type != "private" or not is_admin(uid):
        send_with_premium(chat_id, "❌ Admin only. Open the bot in a private chat.")
        return True
    _admin_audit("menu_action", uid, str(action))
    if action in ("admin_security_roles", "admin_security_keys") and uid not in ADMIN_IDS:
        send_with_premium(chat_id, "❌ Owner access required for security administration.", reply_markup=_admin_back_kb())
        return True
    if action == "admin_clone_manager" and not _sec_can(uid, "clone_control"):
        send_with_premium(chat_id, "❌ Your role cannot manage bot clones.", reply_markup=_admin_back_kb())
        return True

    if action in _API_MANAGER_ACTIONS.values():
        if action == "api_mgr_list":
            send_with_premium(chat_id, _api_manager_list_text(), parse_mode="HTML", reply_markup=_api_manager_keyboard())
        else:
            prompts = {
                "api_mgr_endpoint": ("api_mgr_endpoint", "✏️ Send: <code>command https://provider.example/api?q={query}&amp;key={key}</code>"),
                "api_mgr_key": ("api_mgr_key", "🔑 Send: <code>command YOUR_NEW_API_KEY</code>. The key is stored privately and never shown in listings."),
                "api_mgr_test": ("api_mgr_test", "🧪 Send: <code>command sample_query</code>"),
                "api_mgr_disable": ("api_mgr_disable", "⏸ Send the lookup command to disable, e.g. <code>num</code>."),
                "api_mgr_enable": ("api_mgr_enable", "▶️ Send the lookup command to enable, e.g. <code>num</code>."),
                "api_mgr_remove": ("api_mgr_remove", "🗑 Send the lookup command to remove its custom endpoint override, e.g. <code>num</code>."),
            }
            state, prompt = prompts[action]
            _api_manager_prompt(chat_id, uid, state, prompt)
        return True

    # Keyboard page navigation and dashboards
    if action == "admin_system_manager":
        send_with_premium(chat_id, _sysmgr_status_text(), parse_mode="HTML", reply_markup=_sysmgr_keyboard())
    elif action == "admin_live_monitor":
        send_with_premium(chat_id, _admin_monitor_text(), parse_mode="HTML", reply_markup=_admin_suite_keyboard("monitor"))
    elif action == "admin_backup_manager":
        send_with_premium(chat_id, _admin_backup_manager_text(), parse_mode="HTML", reply_markup=_admin_suite_keyboard("backup"))
    elif action == "admin_activity_logs":
        lines = ["<blockquote><b>🧾 ADMIN ACTIVITY LOG</b>"]
        for item in _admin_audit_recent():
            lines.append(f"• <code>{_html.escape(item['created_at'])}</code> · <code>{item['admin_id']}</code> · {_html.escape(item['action'])} · {_html.escape(item['detail'][:90])}")
        if len(lines) == 1: lines.append("No recorded actions yet.")
        lines.append("</blockquote>")
        send_with_premium(chat_id, "\n".join(lines), parse_mode="HTML", reply_markup=_admin_suite_keyboard("activity"))
    elif action == "admin_broadcast_manager":
        send_with_premium(chat_id, "<blockquote><b>📢 ADVANCED BROADCAST</b>\nChoose an audience. You will be asked to send the message after selecting it. A delivery report will be generated.</blockquote>", parse_mode="HTML", reply_markup=_admin_suite_keyboard("broadcast"))
    elif action == "admin_customization":
        send_with_premium(chat_id, _admin_customization_text(), parse_mode="HTML", reply_markup=_admin_suite_keyboard("custom"))
    elif action == "admin_security_keys":
        send_with_premium(chat_id, _security_keys_text(), parse_mode="HTML",
                          reply_markup=_security_keys_keyboard())
    elif action == "admin_security_roles":
        if uid not in ADMIN_IDS:
            send_with_premium(chat_id, "❌ Only the configured bot owner can manage admin roles.", reply_markup=_admin_back_kb())
        else:
            send_with_premium(chat_id, _sec_roles_text(), parse_mode="HTML", reply_markup=_sec_roles_keyboard())
    elif action == "admin_clone_manager":
        if CLONE_INSTANCE:
            send_with_premium(chat_id, "This clone is controlled from the master bot's Clone Manager.", reply_markup=_admin_back_kb())
        else:
            send_with_premium(chat_id, _clone_summary(), parse_mode="HTML", reply_markup=_clone_manager_keyboard())
    elif action == "admin_api_manager":
        send_with_premium(chat_id, "<blockquote><b>🔌 API MANAGER</b>\nManage the existing lookup endpoints and credentials.\n\nEndpoint format: <code>https://provider.example/api?q={query}&amp;key={key}</code>\nUse trusted HTTPS providers only.</blockquote>", parse_mode="HTML", reply_markup=_api_manager_keyboard())
    elif action == "admin_api_test":
        _api_manager_prompt(chat_id, uid, "api_mgr_test", "🧪 Send: <code>command sample_query</code> to test its configured endpoint.")
    elif action == "admin_user_menu":
        send_with_premium(chat_id, "👤 Returned to the user menu.", reply_markup=_private_main_menu_keyboard(True))
    elif action.startswith("admin_page_"):
        try:
            _show_admin_reply_page(chat_id, int(action.rsplit("_", 1)[1]))
        except (TypeError, ValueError):
            _show_admin_reply_page(chat_id, 0)
    elif action == "admin_stats":
        send_with_premium(chat_id, _admin_panel_text(get_bot_stats()), reply_markup=_admin_back_kb())
    elif action == "admin_dau":
        today_key = datetime.now().strftime("%Y-%m-%d")
        yesterday_key = (datetime.now() - timedelta(days=1)).strftime("%Y-%m-%d")
        dau = _col_users.count_documents({"last_active": {"$regex": f"^{today_key}"}})
        yesterday_dau = _col_users.count_documents({"last_active": {"$regex": f"^{yesterday_key}"}})
        page = ("<blockquote><b>📆 DAILY ACTIVE USERS</b>\n━━━━━━━━━━━━━━━━━━━━\n"
                f"🟢 <b>Today ({today_key})</b>: <code>{dau:,}</code>\n"
                f"🕘 <b>Yesterday ({yesterday_key})</b>: <code>{yesterday_dau:,}</code>\n"
                "<i>Counts registered users whose last activity timestamp falls on that calendar day.</i>\n"
                "━━━━━━━━━━━━━━━━━━━━</blockquote>")
        send_with_premium(chat_id, page, reply_markup=_admin_back_kb())
    elif action == "admin_users":
        send_with_premium(chat_id, _admin_users_page(), reply_markup=_admin_back_kb())
    elif action == "admin_api_status":
        send_with_premium(chat_id, _admin_api_page(), reply_markup=_admin_back_kb())
    elif action == "admin_total_apis":
        built_in = API_ENDPOINTS or {}
        configured = sum(1 for endpoint in built_in.values() if endpoint)
        try: custom_count = _col_api_config.count_documents({})
        except Exception: custom_count = 0
        page = ("<blockquote><b>📊 TOTAL API OVERVIEW</b>\n━━━━━━━━━━━━━━━━━━━━\n"
                f"🧩 Built-in endpoints: <code>{configured}</code>\n"
                f"🛠 Custom API records: <code>{custom_count}</code>\n"
                f"📦 Total registered: <code>{configured + custom_count}</code>\n"
                "🔐 API keys and full URLs are not displayed here.\n━━━━━━━━━━━━━━━━━━━━</blockquote>")
        send_with_premium(chat_id, page, reply_markup=_admin_back_kb())
    elif action == "admin_addmedia":
        send_with_premium(chat_id, _admin_media_page(), reply_markup=_admin_back_kb())
    elif action == "admin_backup":
        cfg = _col_media_set.find_one({"setting_key": "auto_backup_config"}) or {}
        toggle_label = "⏸ Disable backups" if cfg.get("enabled") else "▶️ Enable backups"
        send_with_premium(chat_id, _admin_backup_page(), reply_markup=_admin_kb(
            ("📍 Choose private group", "admin_backup_set"),
            (toggle_label, "admin_backup_toggle"), ("⬅️ Back to Panel", "admin_panel")))
    elif action == "admin_welcome_manager":
        doc = _col_media_set.find_one({"setting_key": "welcome_config"}) or {}
        send_with_premium(chat_id,
            "<blockquote><b>👋 WELCOME MANAGER</b>\n"
            f"Current mode: <code>{_html.escape(str(doc.get('mode', 'default')))}</code>\n"
            "Choose text, photo or video using the inline options below.</blockquote>",
            reply_markup=_admin_kb(("📝 Text welcome", "admin_welcome_text"),
                ("🖼 Photo welcome", "admin_welcome_photo"), ("🎬 Video welcome", "admin_welcome_video"),
                ("♻️ Reset default", "admin_welcome_reset"), ("⬅️ Back to Panel", "admin_panel")))
    elif action == "admin_welcome_video":
        ADMIN_STATE[uid] = {"action": "welcome_video"}
        send_with_premium(chat_id, "🎬 Send the welcome video now, with an optional caption.", reply_markup=_admin_back_kb())
    elif action == "admin_user_history":
        ADMIN_STATE[uid] = {"action": "userhistory"}
        send_with_premium(chat_id, "🧾 Send a Telegram user ID or @username to view account activity and recorded searches.", reply_markup=_admin_back_kb())
    elif action == "admin_add_all_credits":
        ADMIN_STATE[uid] = {"action": "addallcredits"}
        send_with_premium(chat_id, "🎁 Send the amount to add to every registered user. Example: <code>25</code>", parse_mode="HTML", reply_markup=_admin_back_kb())
    elif action in ("admin_edit_help", "admin_edit_lookup_guide", "admin_edit_support_text"):
        editable = {
            "admin_edit_help": ("edit_help_text", "📝 Send the complete replacement text for /help."),
            "admin_edit_lookup_guide": ("edit_lookup_guide", "📘 Send the lookup guide text."),
            "admin_edit_support_text": ("edit_support_text", "☎️ Send the support/contact text."),
        }
        state_action, prompt = editable[action]
        ADMIN_STATE[uid] = {"action": state_action}
        send_with_premium(chat_id, prompt + "\nHTML formatting is supported. Use Back to cancel.", reply_markup=_admin_back_kb())
    elif action == "admin_reset_editable_text":
        _col_media_set.delete_one({"setting_key": "editable_bot_texts"})
        send_with_premium(chat_id, "✅ Editable help, lookup guide and support text reset.", reply_markup=_admin_back_kb())
    elif action == "admin_broadcast_info":
        ADMIN_STATE[uid] = {"action": "broadcast"}
        send_with_premium(chat_id, "📢 Send the broadcast message now. Or reply to a message with /broadcast.", reply_markup=_admin_back_kb())
    elif action == "admin_setbc_info":
        ADMIN_STATE[uid] = {"action": "setbc"}
        send_with_premium(chat_id, _admin_setbc_page(), reply_markup=_admin_back_kb())
    elif action in _ADMIN_INPUT_ACTIONS:
        state_action, title, hint = _ADMIN_INPUT_ACTIONS[action]
        ADMIN_STATE[uid] = {"action": state_action}
        send_with_premium(chat_id, f"<blockquote><b>{title}</b>\n{hint}\nSend it as your next message. Use Back to cancel.</blockquote>", parse_mode="HTML", reply_markup=_admin_back_kb())
    elif action == "acmd_all":
        send_with_premium(chat_id, _acmd_root_text(), reply_markup=_acmd_root_markup())
    elif action == "admin_reload":
        send_with_premium(chat_id, "🔄 <b>Restarting…</b>\nBack in a few seconds.", parse_mode="HTML")
        def _restart_from_reply():
            time.sleep(1.5)
            try: bot.stop_polling()
            except Exception: pass
            os.execv(sys.executable, [sys.executable] + sys.argv)
        threading.Thread(target=_restart_from_reply, daemon=True).start()
    else:
        send_with_premium(chat_id, "This option is available from the inline Admin Panel.", reply_markup=_admin_back_kb())
    return True


# Visible Unicode small-cap labels -> the original internal menu action labels.
# Keep the visual styling independent from the callback/router names.
_PRIVATE_MENU_LABEL_ALIASES = {
    "📱 ɴᴜᴍʙᴇʀ ʟᴏᴏᴋᴜᴘ": "📱 Number Lookup",
    "👤 ᴛᴇʟᴇɢʀᴀᴍ ᴜsᴇʀ": "👤 Telegram User",
    "🆔 ᴍʏ ᴛᴇʟᴇɢʀᴀᴍ ɪᴅ": "🆔 My Telegram ID",
    "📸 ɪɴsᴛᴀɢʀᴀᴍ ʟᴏᴏᴋᴜᴘ": "📸 Instagram Lookup",
    "🐙 ɢɪᴛʜᴜʙ ʟᴏᴏᴋᴜᴘ": "🐙 GitHub Lookup",
    "🎮 ғʀᴇᴇ ғɪʀᴇ ʟᴏᴏᴋᴜᴘ": "🎮 Free Fire Lookup",
    "🎯 ʙɢᴍɪ ʟᴏᴏᴋᴜᴘ": "🎯 BGMI Lookup",
    "🌐 ɪᴘ ʟᴏᴏᴋᴜᴘ": "🌐 IP Lookup",
    "🔗 ᴅᴏᴍᴀɪɴ ʟᴏᴏᴋᴜᴘ": "🔗 Domain Lookup",
    "📮 ᴘɪɴ ᴄᴏᴅᴇ ʟᴏᴏᴋᴜᴘ": "📮 PIN Code Lookup",
    "📧 ᴇᴍᴀɪʟ ʟᴏᴏᴋᴜᴘ": "📧 Email Lookup",
    "🔎 ᴏsɪɴᴛ ʟᴏᴏᴋᴜᴘ": "🔎 OSINT Lookup",
    "🪪 ɪᴅ ᴠᴇʀɪғɪᴄᴀᴛɪᴏɴ ɢᴜɪᴅᴇ": "🪪 ID Verification Guide",
    "👤 ᴍʏ ᴘʀᴏғɪʟᴇ": "👤 My Profile",
    "👤 MY PROFILE": "👤 My Profile",
    "👤 My Profile": "👤 My Profile",
    "💰 ʙᴀʟᴀɴᴄᴇ": "💰 Balance",
    "🎁 ʀᴇғᴇʀ & ᴇᴀʀɴ": "🎁 Refer & Earn",
    "🎟 ʀᴇᴅᴇᴇᴍ ᴄᴏᴅᴇ": "🎟 Redeem Code",
    "❔ ʜᴇʟᴘ / ᴄᴏᴍᴍᴀɴᴅs": "❔ Help / Commands",
    "🛠 ᴀᴅᴍɪɴ ᴘᴀɴᴇʟ": "🛠 Admin Panel",
    "🌟 ᴜsᴇʀ ʜᴜʙ": "🌟 User Hub",
}
_PRIVATE_MENU_ACCEPTED_LABELS = set(_PRIVATE_MENU_PROMPTS) | set(_PRIVATE_MENU_LABEL_ALIASES)
_ADMIN_API_LABEL_TO_ACTION = dict(_API_MANAGER_ACTIONS)

@bot.message_handler(func=lambda m: bool(m and m.chat and m.chat.type == "private" and m.text and (
    m.text in _PRIVATE_MENU_ACCEPTED_LABELS | {
        "👤 My Profile", "👤 MY PROFILE", "💰 Balance", "🎁 Refer & Earn", "🎟 Redeem Code",
        "❔ Help / Commands", "🛠 Admin Panel", "🌟 User Hub"
    } | set(_ADMIN_REPLY_LABEL_TO_ACTION) | set(_ADMIN_API_LABEL_TO_ACTION)
)))
def private_menu_button_handler(message):
    raw_label = (message.text or "").strip()
    label = _PRIVATE_MENU_LABEL_ALIASES.get(raw_label, raw_label)
    # Telegram clients can normalize Unicode small caps differently; accept
    # case/spacing variants of the profile shortcut explicitly.
    if raw_label.casefold().replace(" ", "") in {"👤myprofile", "👤ᴍʏᴘʀᴏғɪʟᴇ"}:
        label = "👤 My Profile"
    uid = message.from_user.id
    try:
        _col_users.update_one({"user_id": uid}, {"$set": {"last_active": datetime.now().strftime("%Y-%m-%d %H:%M:%S")}})
        admin_action = _ADMIN_REPLY_LABEL_TO_ACTION.get(raw_label)
        if admin_action:
            _admin_reply_action(message, admin_action)
            return
        api_action = _ADMIN_API_LABEL_TO_ACTION.get(raw_label)
        if api_action:
            _admin_reply_action(message, api_action)
            return
        if raw_label == "⬅️ Back to Admin":
            _show_admin_reply_page(message.chat.id, 0)
            return
        if label == "🌟 User Hub":
            _uh_home(message.chat.id, uid)
        elif label == "🛠 Admin Panel":
            if not is_admin(uid):
                send_with_premium(message.chat.id, "❌ Admin only!")
                return
            _show_admin_reply_page(message.chat.id, 0)
        elif label == "👤 My Profile":
            profile_cmd(message)
        elif label == "💰 Balance":
            balance_cmd(message)
        elif label == "🎁 Refer & Earn":
            refer_cmd(message)
        elif label == "❔ Help / Commands":
            help_cmd(message)
        elif label == "🎟 Redeem Code":
            send_with_premium(message.chat.id, "Send your code using: <code>/redeem YOUR_CODE</code>", parse_mode="HTML")
        elif label == "🆔 My Telegram ID":
            show_my_telegram_id(message)
        elif label in _PRIVATE_MENU_PROMPTS:
            command, prompt = _PRIVATE_MENU_PROMPTS[label]
            send_with_premium(message.chat.id, f"{prompt}", parse_mode="HTML")
    except Exception as exc:
        print(f"[PRIVATE_MENU] {exc}")
        send_with_premium(message.chat.id, "❌ Could not open that menu item. Please use /help.")


@bot.message_handler(func=lambda m: bool(m and m.from_user and m.text and (
    int(m.from_user.id) in _V5_PAYMENT_INPUT or m.text.strip() == "/cancel")))
def v5_payment_input_handler(message):
    _v5_payment_input_message(message)


# Catch-all registered LAST: telebot uses the first matching handler, so when this
# was registered earlier it swallowed /setbc, /removebc and /contact.
@bot.message_handler(func=lambda m: bool(m and m.chat and m.chat.type in ("group", "supergroup")))
def track_all_messages(m):
    if m.chat.type in ['group', 'supergroup']:
        chat_id = m.chat.id
        chat_title = m.chat.title or "Unknown"
        # throttle: one DB upsert per group per 10 min (was: every message)
        if _GROUP_SEEN.get(chat_id) == chat_title:
            return
        chat_type = m.chat.type
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        try:
            _col_groups.update_one(
                {"chat_id": chat_id},
                {"$set": {"chat_title": chat_title, "chat_type": chat_type,
                           "last_active": now, "is_active": 1},
                 "$setOnInsert": {"added_date": now}},
                upsert=True
            )
            _GROUP_SEEN.set(chat_id, chat_title)
        except Exception as e:
            print(f"track_all_messages error: {e}")


if __name__ == "__main__":
    print("=" * 60)
    print("✅ OSINT BOT STARTING WITH ALL FIXES...")
    print("✅ Developer: ㅤ⏤͟͟͞͞𝗙ʟɪʀᴛ𝗫ᴏ")
    print("=" * 60)

    # Turso removed — MongoDB only
    print("✅ Contact store: MongoDB only (Turso removed)")

    try:
        bot.remove_webhook()
    except Exception:
        pass

    clear_pending_updates()

    # Telegram slash-command suggestions. Sensitive/private-data lookup commands
    # are deliberately not promoted in the public command menu.
    try:
        bot.set_my_commands([
            types.BotCommand("start", "Open the bot and main menu"),
            types.BotCommand("help", "Show available commands"),
            types.BotCommand("profile", "View your account profile"),
            types.BotCommand("balance", "Check your credits"),
            types.BotCommand("refer", "Get your referral link"),
            types.BotCommand("redeem", "Redeem a credit code"),
            types.BotCommand("ff", "Public game profile lookup"),
            types.BotCommand("insta", "Public Instagram profile lookup"),
        ])
    except Exception as command_menu_exc:
        print(f"[BOT_COMMAND_MENU] {command_menu_exc}")

    print(f"⚙️  threads={BOT_THREADS} bg={BG_WORKERS} sub={SUB_WORKERS} "
          f"api={API_WORKERS} animations={MAX_ANIMATIONS if SEARCH_ANIMATION else 0}")

    if not CLONE_INSTANCE:
        _clone_autostart()

    failures = 0
    while True:
        try:
            bot.polling(non_stop=True, skip_pending=True, timeout=20,
                        long_polling_timeout=25,
                        allowed_updates=["message", "callback_query",
                                         "channel_post", "chat_join_request"])
            break                                    # clean exit
        except KeyboardInterrupt:
            print("\n🛑 Bot stopped")
            break
        except MemoryError:
            print("❌ Out of memory — hard restart")
            os.execv(sys.executable, [sys.executable] + sys.argv)
        except Exception as e:
            failures += 1
            wait = min(60, 5 * failures)
            print(f"❌ Polling error ({failures}): {e} — retry in {wait}s")
            try:
                bot.stop_polling()
            except Exception:
                pass
            time.sleep(wait)
            if failures >= 5:
                print("🔄 Restarting process")
                os.execv(sys.executable, [sys.executable] + sys.argv)



# ═══════════════════════════════════════════════════════════════════════
# SHOWN LEGACY V5 — MANAGEMENT & USER EXPERIENCE FOUNDATION
# Added as an additive module; existing V4.1 handlers and data are retained.
# ═══════════════════════════════════════════════════════════════════════
_V5_VERSION = "5.1.0"
_V5_USERS = _store["v5_user_profiles"]
_V5_AUDIT = _store["v5_audit_events"]
_V5_NOTICES = _store["v5_notifications"]
_V5_XP = _store["v5_xp"]
_V5_TASKS = _store["v5_scheduled_tasks"]
_V5_SUPPORT = _store["v5_support_queue"]
_V5_FLAGS = _store["v5_abuse_flags"]
_V5_SETTINGS = _store["v5_settings"]
_V5_STATE = {}
_V5_LOCK = threading.RLock()


def _v5_now():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def _v5_audit(actor, action, target=None, detail=""):
    try:
        _V5_AUDIT.insert_one({
            "actor_id": int(actor), "action": str(action)[:80],
            "target_id": int(target) if target is not None else None,
            "detail": str(detail)[:500], "created_at": _v5_now()
        })
    except Exception:
        logging.exception("[V5_AUDIT] failed")


def _v5_admin_kb(rows):
    kb = InlineKeyboardMarkup(row_width=2)
    for label, data, kind in rows:
        fn = create_danger_button if kind == "danger" else (
            create_success_button if kind == "success" else create_primary_button)
        kb.add(fn(label, callback_data=data))
    return kb


def _v5_edit(call, text, markup=None):
    # V5 admin/user screens edit the invoking message; no send-new-message fallback.
    try:
        edit_with_premium(call.message.chat.id, call.message.message_id,
                          text, reply_markup=markup)
    except Exception as exc:
        logging.warning("[V5_EDIT] message edit failed: %s", exc)
        try:
            bot.answer_callback_query(call.id, "This screen could not be refreshed. Reopen the menu.", True)
        except Exception:
            pass



# ─────────────────────────────────────────────────────────────────────────────
# V5 PAYMENT SETTINGS — Telegram Stars + Razorpay Payment Links (UPI enabled)
# Secrets are Fernet-encrypted at rest. A dedicated key is generated on first use
# and stored with mode 0600 on the persistent disk. Keep /var/data persistent.
# ─────────────────────────────────────────────────────────────────────────────
_V5_PAYMENT_INPUT = {}
_V5_PAYMENT_LOCK = threading.RLock()
_V5_PAYMENT_KEY_FILE = os.environ.get("SHOWN_PAYMENT_KEY_FILE") or (
    "/var/data/shown_payment_config.key" if os.path.isdir("/var/data")
    else os.path.join(os.path.dirname(os.path.abspath(__file__)), "shown_payment_config.key")
)
_V5_PAYMENT_SECRET_FIELDS = {"razorpay_key_id", "razorpay_key_secret", "razorpay_webhook_secret"}
_V5_PAYMENT_FIELDS = {
    "upi_id": ("UPI ID", 150),
    "razorpay_key_id": ("Razorpay Key ID", 200),
    "razorpay_key_secret": ("Razorpay Key Secret", 300),
    "razorpay_webhook_secret": ("Razorpay Webhook Secret", 300),
    "inr_amount": ("Razorpay amount in paise (e.g. 9900 = ₹99)", 9),
    "stars_amount": ("Telegram Stars amount (whole number)", 6),
    "duration_days": ("Membership duration in days", 5),
}


def _v5_payment_cipher():
    from cryptography.fernet import Fernet
    directory = os.path.dirname(_V5_PAYMENT_KEY_FILE) or "."
    os.makedirs(directory, mode=0o700, exist_ok=True)
    with _V5_PAYMENT_LOCK:
        if not os.path.exists(_V5_PAYMENT_KEY_FILE):
            fd, tmp = tempfile.mkstemp(prefix=".shown_payment_key_", dir=directory)
            try:
                os.fchmod(fd, 0o600)
                with os.fdopen(fd, "wb") as fh:
                    fh.write(Fernet.generate_key())
                    fh.flush(); os.fsync(fh.fileno())
                os.replace(tmp, _V5_PAYMENT_KEY_FILE)
                os.chmod(_V5_PAYMENT_KEY_FILE, 0o600)
            finally:
                try:
                    if os.path.exists(tmp): os.remove(tmp)
                except Exception: pass
        with open(_V5_PAYMENT_KEY_FILE, "rb") as fh:
            key = fh.read().strip()
        return Fernet(key)


def _v5_payment_get():
    doc = _V5_SETTINGS.find_one({"_id": "payment_config"}) or {}
    values = dict(doc.get("values") or {})
    for field in _V5_PAYMENT_SECRET_FIELDS:
        value = values.get(field, "")
        if value:
            try:
                values[field] = _v5_payment_cipher().decrypt(str(value).encode("ascii")).decode("utf-8")
            except Exception:
                logging.exception("[V5_PAYMENT] Could not decrypt %s", field)
                values[field] = ""
    defaults = {"upi_id":"", "razorpay_key_id":"", "razorpay_key_secret":"",
                "razorpay_webhook_secret":"", "inr_amount":9900, "stars_amount":50,
                "duration_days":30, "razorpay_enabled":False, "stars_enabled":False,
                "payments_enabled":False}
    defaults.update(values)
    return defaults


def _v5_payment_save(field, value):
    if field not in set(_V5_PAYMENT_FIELDS) | {"razorpay_enabled", "stars_enabled", "payments_enabled"}:
        raise ValueError("Unsupported payment setting.")
    values = dict((_V5_SETTINGS.find_one({"_id":"payment_config"}) or {}).get("values") or {})
    if field in _V5_PAYMENT_SECRET_FIELDS and value:
        value = _v5_payment_cipher().encrypt(str(value).encode("utf-8")).decode("ascii")
    values[field] = value
    _V5_SETTINGS.update_one({"_id":"payment_config"}, {"$set":{"values":values,"updated_at":_v5_now()}}, upsert=True)


def _v5_payment_admin_text():
    c = _v5_payment_get()
    def status(v): return "🟢 ON" if v else "🔴 OFF"
    def secret(v): return "Configured" if v else "Not configured"
    return ("<blockquote><b>💳 PAYMENT SETTINGS</b>\n"
        f"Payment switch: <b>{status(c['payments_enabled'])}</b>\n"
        f"Telegram Stars: <b>{status(c['stars_enabled'])}</b> · Price: <code>{int(c['stars_amount'])} XTR</code>\n"
        f"Razorpay / UPI: <b>{status(c['razorpay_enabled'])}</b> · Price: <code>₹{int(c['inr_amount'])/100:.2f}</code>\n"
        f"UPI ID: <code>{_html.escape(str(c['upi_id']) or 'Not set')}</code>\n"
        f"Razorpay Key ID: <code>{secret(c['razorpay_key_id'])}</code>\n"
        f"Razorpay Key Secret: <code>{secret(c['razorpay_key_secret'])}</code>\n"
        f"Webhook Secret: <code>{secret(c['razorpay_webhook_secret'])}</code>\n"
        f"Membership duration: <code>{int(c['duration_days'])} days</code>\n\n"
        "Secrets are encrypted at rest and masked here. Keep the Render disk mounted at /var/data. "
        "Razorpay payments are confirmed by querying Razorpay's API; never trust screenshots.</blockquote>")


def _v5_payment_history_text():
    try:
        docs = list(_V5_SETTINGS.find({}).limit(300))
    except Exception:
        logging.exception("[V5_PAYMENT] Could not read payment history")
        docs = []
    rows = []
    for doc in docs:
        key = str(doc.get("_id", ""))
        if key.startswith("payment_link_"):
            rows.append((str(doc.get("created_at", "")),
                         f"Razorpay · user {doc.get('user_id','?')} · ₹{int(doc.get('amount',0))/100:.2f} · {doc.get('status','unknown')}"))
        elif key.startswith("stars_payment_"):
            rows.append((str(doc.get("created_at", "")),
                         f"Stars · user {doc.get('user_id','?')} · {doc.get('amount','?')} XTR · {doc.get('status','unknown')}"))
    rows.sort(key=lambda item: item[0], reverse=True)
    lines = ["<blockquote><b>💳 PAYMENT HISTORY</b>"]
    if not rows:
        lines.append("No payment records yet.")
    else:
        lines.extend("• " + _html.escape(stamp) + " — " + _html.escape(summary) for stamp, summary in rows[:25])
    lines.append("</blockquote>")
    return "\n".join(lines)


def _v5_payment_admin_kb():
    c = _v5_payment_get()
    rows = [
        ("✏️ Edit UPI ID", "v5_pay_set_upi_id", "primary"),
        ("🔑 Set Razorpay Key ID", "v5_pay_set_razorpay_key_id", "primary"),
        ("🔐 Set Razorpay Key Secret", "v5_pay_set_razorpay_key_secret", "primary"),
        ("🔏 Set Webhook Secret", "v5_pay_set_razorpay_webhook_secret", "primary"),
        ("💰 Set INR Price", "v5_pay_set_inr_amount", "primary"),
        ("⭐ Set Stars Price", "v5_pay_set_stars_amount", "primary"),
        ("🗓 Set Membership Days", "v5_pay_set_duration_days", "primary"),
        (("🟢 Enable All Payments" if not c["payments_enabled"] else "🔴 Pause All Payments"), "v5_pay_toggle_payments_enabled", "success" if not c["payments_enabled"] else "danger"),
        (("🟢 Enable Razorpay" if not c["razorpay_enabled"] else "🔴 Disable Razorpay"), "v5_pay_toggle_razorpay_enabled", "success" if not c["razorpay_enabled"] else "danger"),
        (("🟢 Enable Stars" if not c["stars_enabled"] else "🔴 Disable Stars"), "v5_pay_toggle_stars_enabled", "success" if not c["stars_enabled"] else "danger"),
        ("🗑 Remove UPI ID", "v5_pay_remove_upi", "danger"),
        ("🗑 Remove Razorpay Credentials", "v5_pay_remove_razorpay", "danger"),
        ("📜 Payment History", "v5_admin_payment_history", "primary"),
        ("🔄 Refresh", "v5_admin_payments", "primary"),
        ("⬅️ Admin Home", "v5_admin_home", "primary"),
    ]
    return _v5_admin_kb(rows)


def _v5_payment_callback(call, data, uid):
    if not is_admin(uid):
        bot.answer_callback_query(call.id, "Admin only.", True); return
    if data.startswith("v5_pay_set_"):
        field = data[len("v5_pay_set_"):]
        if field not in _V5_PAYMENT_FIELDS:
            bot.answer_callback_query(call.id, "Unknown setting.", True); return
        with _V5_PAYMENT_LOCK:
            _V5_PAYMENT_INPUT[uid] = field
        label, _limit = _V5_PAYMENT_FIELDS[field]
        bot.answer_callback_query(call.id, "Send the new value in your next message.")
        send_with_premium(call.message.chat.id,
            f"<b>Set { _html.escape(label) }</b>\nSend the new value now. Send /cancel to cancel.",
            parse_mode="HTML")
        return
    if data.startswith("v5_pay_toggle_"):
        field = data[len("v5_pay_toggle_"):]
        if field not in ("payments_enabled", "razorpay_enabled", "stars_enabled"):
            bot.answer_callback_query(call.id, "Unknown switch.", True); return
        c = _v5_payment_get(); new_value = not bool(c[field])
        if new_value and field == "razorpay_enabled":
            if not all(c.get(x) for x in ("razorpay_key_id", "razorpay_key_secret")):
                bot.answer_callback_query(call.id, "Set Razorpay Key ID and Secret first.", True); return
        if new_value and field == "stars_enabled" and int(c.get("stars_amount",0)) < 1:
            bot.answer_callback_query(call.id, "Set a valid Stars price first.", True); return
        _v5_payment_save(field, new_value)
        _v5_audit(uid, "payment_setting_toggle", detail=f"{field}={new_value}")
    elif data == "v5_pay_remove_upi":
        _v5_payment_save("upi_id", "")
        _v5_audit(uid, "payment_upi_removed")
    elif data == "v5_pay_remove_razorpay":
        for field in ("razorpay_key_id", "razorpay_key_secret", "razorpay_webhook_secret"):
            _v5_payment_save(field, "")
        _v5_payment_save("razorpay_enabled", False)
        _v5_audit(uid, "razorpay_credentials_removed")
    _v5_edit(call, _v5_payment_admin_text(), _v5_payment_admin_kb())
    bot.answer_callback_query(call.id)


def _v5_payment_input_message(message):
    if not message or not message.from_user or not message.text:
        return
    uid = int(message.from_user.id)
    if not is_admin(uid):
        return
    with _V5_PAYMENT_LOCK:
        field = _V5_PAYMENT_INPUT.get(uid)
    if not field:
        return
    raw = message.text.strip()
    if raw == "/cancel":
        with _V5_PAYMENT_LOCK: _V5_PAYMENT_INPUT.pop(uid, None)
        send_with_premium(message.chat.id, "Payment setting update cancelled.")
        return
    label, max_len = _V5_PAYMENT_FIELDS[field]
    if not raw or len(raw) > max_len or any(ord(ch) < 32 for ch in raw):
        send_with_premium(message.chat.id, f"Invalid value for {label}. Try again or send /cancel.")
        return
    try:
        if field == "upi_id":
            if not re.fullmatch(r"[A-Za-z0-9._-]{2,256}@[A-Za-z0-9.-]{2,64}", raw):
                raise ValueError("Enter a valid UPI ID, for example name@bank.")
        elif field in ("inr_amount", "stars_amount", "duration_days"):
            if not raw.isdigit(): raise ValueError("Enter a whole number only.")
            number = int(raw)
            minimum = 100 if field == "inr_amount" else 1
            maximum = 10000000 if field == "inr_amount" else (100000 if field == "stars_amount" else 3650)
            if not minimum <= number <= maximum: raise ValueError(f"Value must be between {minimum} and {maximum}.")
            raw = number
        _v5_payment_save(field, raw)
        _v5_audit(uid, "payment_setting_updated", detail=field)
        with _V5_PAYMENT_LOCK: _V5_PAYMENT_INPUT.pop(uid, None)
        if field in _V5_PAYMENT_SECRET_FIELDS:
            try: bot.delete_message(message.chat.id, message.message_id)
            except Exception: logging.warning("[V5_PAYMENT] Could not delete credential message; admin should delete it manually")
        send_with_premium(message.chat.id, f"✅ {label} updated. Open /v5admin → Payment Settings to review.")
    except Exception as exc:
        send_with_premium(message.chat.id, f"❌ { _html.escape(str(exc)) }\nTry again or send /cancel.", parse_mode="HTML")


@bot.message_handler(commands=["upgrade"])
def v5_upgrade_command(message):
    c = _v5_payment_get()
    rows = []
    if c.get("payments_enabled") and c.get("stars_enabled"):
        rows.append((f"⭐ Pay {int(c['stars_amount'])} Stars", "v5_pay_user_stars", "success"))
    if c.get("payments_enabled") and c.get("razorpay_enabled"):
        rows.append((f"🇮🇳 Pay ₹{int(c['inr_amount'])/100:.2f} via UPI", "v5_pay_user_razorpay", "success"))
    text = ("<blockquote><b>💎 PREMIUM MEMBERSHIP</b>\n"
            f"Duration: <code>{int(c['duration_days'])} days</code>\n"
            "Choose a verified payment method below. Premium is activated only after payment confirmation.</blockquote>")
    if not rows:
        send_with_premium(message.chat.id, text + "\n\nPayments are currently unavailable.", parse_mode="HTML")
        return
    send_with_premium(message.chat.id, text, parse_mode="HTML", reply_markup=_v5_admin_kb(rows))


def _v5_admin_home_text():
    try:
        users = _col_users.count_documents({})
    except Exception:
        users = 0
    try:
        clones = len(_clone_rows())
        running = sum(1 for x in _clone_processes.values() if x and x.poll() is None)
    except Exception:
        clones, running = 0, 0
    try:
        open_tickets = _USER_HUB_TICKETS.count_documents({"status": "open"})
    except Exception:
        open_tickets = 0
    try:
        flags = _V5_FLAGS.count_documents({"status": "open"})
    except Exception:
        flags = 0
    return (
        "<blockquote><b>🛡 SHOWN LEGACY V5 — ADMIN CENTRE</b>\n"
        f"Version: <code>{_V5_VERSION}</code>\n"
        f"Registered users: <code>{users:,}</code>\n"
        f"Clones: <code>{clones}</code> · Running processes: <code>{running}</code>\n"
        f"Open support tickets: <code>{open_tickets}</code>\n"
        f"Open abuse flags: <code>{flags}</code>\n"
        "Choose a management area below.</blockquote>"
    )


def _v5_admin_home_kb():
    return _v5_admin_kb([
        ("📊 Advanced Dashboard", "v5_admin_analytics", "primary"),
        ("👥 User Management", "v5_admin_users", "primary"),
        ("📢 Broadcast Manager", "v5_admin_broadcast", "success"),
        ("🤖 Clone Manager", "v5_admin_clones", "primary"),
        ("🔐 Security & Keys", "v5_admin_security", "primary"),
        ("💳 Payment Settings", "v5_admin_payments", "success"),
        ("⚙️ Automation & Tasks", "v5_admin_tasks", "primary"),
        ("🎫 Support Tickets", "v5_admin_support", "success"),
        ("💾 Backup & Restore", "v5_admin_backup", "primary"),
        ("🔔 Notifications", "v5_admin_notify", "success"),
        ("🛡 Anti-Abuse Centre", "v5_admin_abuse", "danger"),
        ("📜 Admin Audit Log", "v5_admin_audit", "primary"),
    ])


def _v5_admin_analytics_text():
    today = datetime.now().strftime("%Y-%m-%d")
    yesterday = (datetime.now() - timedelta(days=1)).strftime("%Y-%m-%d")
    try:
        total = _col_users.count_documents({})
        dau = _col_users.count_documents({"last_active": {"$regex": f"^{today}"}})
        prev = _col_users.count_documents({"last_active": {"$regex": f"^{yesterday}"}})
    except Exception:
        total = dau = prev = 0
    try:
        ticket_count = _V5_SUPPORT.count_documents({})
        notice_count = _V5_NOTICES.count_documents({})
        flag_count = _V5_FLAGS.count_documents({"status": "open"})
    except Exception:
        ticket_count = notice_count = flag_count = 0
    try:
        clone_rows = _clone_rows()
        clone_total = len(clone_rows)
        clone_running = sum(1 for p in _clone_processes.values() if p and p.poll() is None)
    except Exception:
        clone_total = clone_running = 0
    return (
        "<blockquote><b>📊 V5 ADVANCED ANALYTICS</b>\n"
        f"Total registered users: <code>{total:,}</code>\n"
        f"Active today: <code>{dau:,}</code>\n"
        f"Active yesterday: <code>{prev:,}</code>\n"
        f"Registered clones: <code>{clone_total}</code>\n"
        f"Running clone processes: <code>{clone_running}</code>\n"
        f"Support tickets recorded: <code>{ticket_count}</code>\n"
        f"Saved notifications: <code>{notice_count}</code>\n"
        f"Open abuse flags: <code>{flag_count}</code>\n\n"
        "Counts use records currently retained by this installation.</blockquote>"
    )


def _v5_admin_users_text():
    docs = list(_col_users.find({}).sort("last_active", -1).limit(12))
    lines = ["<blockquote><b>👥 USER MANAGEMENT — RECENT USERS</b>"]
    if not docs:
        lines.append("No registered users were found.")
    for d in docs:
        uid = d.get("user_id") or d.get("_id") or "?"
        name = _html.escape(str(d.get("first_name") or d.get("username") or "User")[:35])
        lines.append(f"• <b>{name}</b> · <code>{uid}</code>")
    lines.append("\nUse the existing admin user tools for ban/unban and credit changes.</blockquote>")
    return "\n".join(lines)


def _v5_admin_clone_text():
    try:
        rows = _clone_rows()
    except Exception as exc:
        return "<b>Clone manager unavailable:</b> " + _html.escape(str(exc)[:250])
    lines = ["<blockquote><b>🤖 ADVANCED CLONE MANAGER</b>"]
    if not rows:
        lines.append("No clones registered.")
    for row in rows[:15]:
        proc = _clone_processes.get(int(row["clone_id"]))
        running = bool(proc and proc.poll() is None)
        lines.append(
            f"#{row['clone_id']} · @{_html.escape(str(row['bot_username']))} · "
            f"{'🟢 Running' if running else '🔴 Stopped'}"
        )
        if row.get("last_error"):
            lines.append("  Last error: " + _html.escape(str(row["last_error"])[:120]))
    lines.append("\nUse the existing Clone Manager to add, start and stop clones. "
                 "Automatic recovery only restarts clones whose manager process remains alive.</blockquote>")
    return "\n".join(lines)


def _v5_admin_security_text():
    api, api_source = _security_key_get("api")
    clone, clone_source = _security_key_get("clone")
    return (
        "<blockquote><b>🔐 SECURITY & ENCRYPTION CENTRE</b>\n"
        f"API key: <b>{'Configured' if api else 'Missing'}</b> · Source: <code>{_html.escape(str(api_source or 'none'))}</code>\n"
        f"Clone key: <b>{'Configured' if clone else 'Missing'}</b> · Source: <code>{_html.escape(str(clone_source or 'none'))}</code>\n\n"
        "Secrets are never displayed here. Manage persistent-disk keys in the existing Security & Keys workflow. "
        "Before rotating a clone key, ensure all stored clone tokens can be migrated safely.</blockquote>"
    )


def _v5_admin_tasks_text():
    docs = list(_V5_TASKS.find({"enabled": True}).sort("run_at", 1).limit(10))
    lines = ["<blockquote><b>⚙️ AUTOMATION & SCHEDULED TASKS</b>"]
    if not docs:
        lines.append("No scheduled tasks are currently queued.")
    for d in docs:
        lines.append(f"• <code>{_html.escape(str(d.get('run_at','')))}</code> · "
                     f"{_html.escape(str(d.get('task_type','task')))} · "
                     f"{_html.escape(str(d.get('status','queued')))}")
    lines.append("\nThis screen reports V5 task records. It does not claim to control Render's infrastructure.</blockquote>")
    return "\n".join(lines)


def _v5_admin_support_text():
    docs = list(_USER_HUB_TICKETS.find({"status": "open"}).sort("created_at", -1).limit(10))
    lines = ["<blockquote><b>🎫 SUPPORT TICKET QUEUE</b>"]
    if not docs:
        lines.append("No open V5 support tickets.")
    for d in docs:
        lines.append(f"#{d.get('ticket_id')} · user <code>{d.get('user_id')}</code> · "
                     f"{_html.escape(str(d.get('subject','Support request'))[:90])}")
    lines.append("</blockquote>")
    return "\n".join(lines)


def _v5_admin_abuse_text():
    docs = list(_V5_FLAGS.find({"status": "open"}).sort("created_at", -1).limit(10))
    lines = ["<blockquote><b>🛡 ANTI-ABUSE CENTRE</b>"]
    if not docs:
        lines.append("No open abuse flags recorded.")
    for d in docs:
        lines.append(f"• User <code>{d.get('user_id')}</code> · "
                     f"{_html.escape(str(d.get('reason','Flagged'))[:100])}")
    lines.append("\nThis queue records reviewed reports and admin flags. It is not a substitute for Telegram-side abuse detection.</blockquote>")
    return "\n".join(lines)


def _v5_user_privacy_text(uid):
    return (
        "<blockquote><b>🔒 YOUR PRIVACY CENTRE</b>\n"
        "You can request a copy of your account data or request account deletion.\n"
        "Deletion requests are reviewed by an administrator to prevent accidental loss and handle records that must be retained.\n"
        "Do not send passwords, OTPs or payment credentials.</blockquote>"
    )


def _v5_user_home_additions(uid):
    return


@bot.message_handler(commands=["v5admin"])
def v5_admin_command(message):
    if not is_admin(message.from_user.id):
        send_with_premium(message.chat.id, "❌ Admin only.")
        return
    send_with_premium(message.chat.id, _v5_admin_home_text(),
                      reply_markup=_v5_admin_home_kb())


# Keep this prefix-specific router ahead of the legacy catch-all callback handler.
@bot.callback_query_handler(func=lambda call: bool(call.data and call.data.startswith("v5_")))
def v5_callback_router(call):
    try:
        data = call.data or ""
        uid = int(call.from_user.id)
        chat_id = call.message.chat.id if call.message else uid
        if data.startswith("v5_admin_"):
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "Admin only.", True)
                return
            if data.startswith("v5_pay_"):
                _v5_payment_callback(call, data, uid)
                return
            screens = {
                "v5_admin_home": (_v5_admin_home_text(), _v5_admin_home_kb()),
                "v5_admin_analytics": (_v5_admin_analytics_text(), _v5_admin_kb([
                    ("🔄 Refresh", "v5_admin_analytics", "primary"),
                    ("⬅️ Admin Home", "v5_admin_home", "primary")])),
                "v5_admin_users": (_v5_admin_users_text(), _v5_admin_kb([
                    ("🔄 Refresh", "v5_admin_users", "primary"),
                    ("⬅️ Admin Home", "v5_admin_home", "primary")])),
                "v5_admin_clones": (_v5_admin_clone_text(), _v5_admin_kb([
                    ("➕ Add / Manage Clones", "clone_list", "success"),
                    ("🔄 Refresh", "v5_admin_clones", "primary"),
                    ("⬅️ Admin Home", "v5_admin_home", "primary")])),
                "v5_admin_security": (_v5_admin_security_text(), _v5_admin_kb([
                    ("🔑 Existing Key Manager", "keycheck_all", "primary"),
                    ("🔄 Refresh", "v5_admin_security", "primary"),
                    ("⬅️ Admin Home", "v5_admin_home", "primary")])),
                "v5_admin_payments": (_v5_payment_admin_text(), _v5_payment_admin_kb()),
                "v5_admin_payment_history": (_v5_payment_history_text(), _v5_admin_kb([
                    ("⬅️ Payment Settings", "v5_admin_payments", "primary"),
                    ("⬅️ Admin Home", "v5_admin_home", "primary")])),
                "v5_admin_tasks": (_v5_admin_tasks_text(), _v5_admin_kb([
                    ("🔄 Refresh", "v5_admin_tasks", "primary"),
                    ("⬅️ Admin Home", "v5_admin_home", "primary")])),
                "v5_admin_support": (_v5_admin_support_text(), _v5_admin_kb([
                    ("🔄 Refresh", "v5_admin_support", "primary"),
                    ("⬅️ Admin Home", "v5_admin_home", "primary")])),
                "v5_admin_backup": (_admin_backup_manager_text(), _v5_admin_kb([
                    ("💾 Existing Backup Manager", "sysmgr_backup", "primary"),
                    ("⬅️ Admin Home", "v5_admin_home", "primary")])),
                "v5_admin_abuse": (_v5_admin_abuse_text(), _v5_admin_kb([
                    ("🔄 Refresh", "v5_admin_abuse", "primary"),
                    ("⬅️ Admin Home", "v5_admin_home", "primary")])),
                "v5_admin_audit": (
                    "<blockquote><b>📜 RECENT ADMIN AUDIT</b>\n" +
                    "\n".join("• " + _html.escape(str(x.get("created_at",""))) +
                              " · " + _html.escape(str(x.get("action",""))) +
                              " · <code>" + str(x.get("actor_id","")) + "</code>"
                              for x in list(_V5_AUDIT.find({}).sort("created_at",-1).limit(12))) +
                    "</blockquote>",
                    _v5_admin_kb([("⬅️ Admin Home", "v5_admin_home", "primary")])
                ),
                "v5_admin_broadcast": (
                    "<blockquote><b>📢 BROADCAST MANAGER</b>\n"
                    "Use the existing verified broadcast workflow from Admin Panel. "
                    "Scheduled delivery and campaign analytics require a configured task runner and delivery tracking.</blockquote>",
                    _v5_admin_kb([("⬅️ Admin Home", "v5_admin_home", "primary")])
                ),
                "v5_admin_notify": (
                    "<blockquote><b>🔔 NOTIFICATION CENTRE</b>\n"
                    "Notification records are stored separately from system announcements. "
                    "Publishing to users requires an explicit audience and message confirmation.</blockquote>",
                    _v5_admin_kb([("⬅️ Admin Home", "v5_admin_home", "primary")])
                ),
            }
            text, markup = screens.get(data, (_v5_admin_home_text(), _v5_admin_home_kb()))
            _v5_edit(call, text, markup)
            _v5_audit(uid, data)
            bot.answer_callback_query(call.id)
            return

        if data.startswith("v5_pay_user_"):
            c = _v5_payment_get()
            if not c.get("payments_enabled"):
                bot.answer_callback_query(call.id, "Payments are currently paused.", True); return
            if data == "v5_pay_user_stars":
                if not c.get("stars_enabled"):
                    bot.answer_callback_query(call.id, "Telegram Stars is disabled.", True); return
                bot.answer_callback_query(call.id, "Preparing Stars invoice…")
                try:
                    payload = f"shown-premium:{uid}:{int(time.time())}"
                    bot.send_invoice(chat_id, "Premium Membership", f"{int(c['duration_days'])} days premium access",
                        payload, "", "XTR", [types.LabeledPrice("Premium Membership", int(c["stars_amount"]))])
                except Exception:
                    logging.exception("[V5_PAYMENT] Stars invoice creation failed")
                    send_with_premium(chat_id, "Could not create a Telegram Stars invoice. Please try again later.")
                return
            if data == "v5_pay_user_razorpay":
                if not c.get("razorpay_enabled"):
                    bot.answer_callback_query(call.id, "Razorpay is disabled.", True); return
                try:
                    import requests as _requests
                    auth = (str(c["razorpay_key_id"]), str(c["razorpay_key_secret"]))
                    amount = int(c["inr_amount"])
                    resp = _requests.post("https://api.razorpay.com/v1/payment_links", auth=auth,
                        json={"amount":amount,"currency":"INR","accept_partial":False,
                              "description":f"Shown Legacy Premium - {int(c['duration_days'])} days",
                              "customer":{"name":str(call.from_user.first_name or "Telegram User")[:80]},
                              "notify":{"sms":False,"email":False},"reminder_enable":False}, timeout=20)
                    if resp.status_code not in (200, 201):
                        raise RuntimeError(f"Razorpay returned HTTP {resp.status_code}")
                    link = resp.json()
                    _V5_SETTINGS.update_one({"_id":"payment_link_"+str(link.get("id"))},
                        {"$set":{"user_id":uid,"duration_days":int(c["duration_days"]),"amount":amount,
                                  "created_at":_v5_now(),"status":"created"}},upsert=True)
                    kb = _v5_admin_kb([("💳 Open Secure Payment", "v5_pay_open_"+str(link.get("id")), "success")])
                    pay_url = str(link.get("short_url") or "")
                    if not pay_url:
                        raise RuntimeError("Razorpay did not return a payment URL")
                    pay_kb = InlineKeyboardMarkup()
                    pay_kb.add(InlineKeyboardButton("💳 Open Secure Payment", url=pay_url))
                    send_with_premium(chat_id, "<blockquote><b>RAZORPAY PAYMENT LINK</b>\nComplete payment using UPI or another enabled method. After payment, use /verify_payment " + _html.escape(str(link.get("id"))) + " to verify.</blockquote>", parse_mode="HTML", reply_markup=pay_kb)
                    bot.answer_callback_query(call.id)
                except Exception:
                    logging.exception("[V5_PAYMENT] Razorpay link creation failed")
                    bot.answer_callback_query(call.id, "Could not create payment link. Check Razorpay configuration.", True)
                return
            if data.startswith("v5_pay_open_"):
                bot.answer_callback_query(call.id, "Open the payment link from the message.")
                return
            bot.answer_callback_query(call.id, "Unknown payment action.", True); return

        if data.startswith("v5_user_"):
            if data == "v5_user_privacy":
                text = _v5_user_privacy_text(uid)
                kb = _v5_admin_kb([
                    ("📦 Request My Data", "v5_user_export", "primary"),
                    ("🗑 Request Account Deletion", "v5_user_delete", "danger"),
                    ("⬅️ User Hub", "uh_home", "primary")])
                _v5_edit(call, text, kb)
            elif data in ("v5_user_export", "v5_user_delete"):
                kind = "data_export" if data.endswith("export") else "account_deletion"
                _USER_HUB_TICKETS.insert_one({
                    "ticket_id": int(time.time() * 1000) % 1000000000,
                    "user_id": uid, "subject": kind.replace("_", " ").title(),
                    "message": "User submitted a privacy request.",
                    "status": "open", "created_at": _v5_now(), "request_type": kind
                })
                _v5_edit(call,
                    "<blockquote><b>✅ REQUEST RECORDED</b>\n"
                    "Your request has been submitted for administrator review. "
                    "You will be contacted through this bot if further action is needed.</blockquote>",
                    _v5_admin_kb([("⬅️ User Hub", "uh_home", "primary")]))
                _v5_audit(uid, kind)
            else:
                bot.answer_callback_query(call.id, "Unknown user option.", True)
                return
            bot.answer_callback_query(call.id)
            return
        bot.answer_callback_query(call.id, "Unknown V5 action.", True)
    except Exception as exc:
        logging.exception("[V5_CALLBACK] %s", exc)
        try:
            bot.answer_callback_query(call.id, "V5 action failed. Check logs.", True)
        except Exception:
            pass


# Add privacy access to the existing User Hub without replacing its menu.
# A standalone /privacy command remains available if the older menu is cached.

@bot.message_handler(commands=["verify_payment"])
def v5_verify_payment_command(message):
    parts = (message.text or "").split(maxsplit=1)
    if len(parts) != 2:
        send_with_premium(message.chat.id, "Usage: /verify_payment PAYMENT_LINK_ID")
        return
    link_id = parts[1].strip()
    doc = _V5_SETTINGS.find_one({"_id":"payment_link_"+link_id}) or {}
    if int(doc.get("user_id", -1)) != int(message.from_user.id):
        send_with_premium(message.chat.id, "Payment link not found for your account.")
        return
    c = _v5_payment_get()
    try:
        import requests as _requests
        resp = _requests.get("https://api.razorpay.com/v1/payment_links/"+_urlquote(link_id),
            auth=(str(c["razorpay_key_id"]),str(c["razorpay_key_secret"])),timeout=20)
        if resp.status_code != 200: raise RuntimeError(f"Razorpay returned HTTP {resp.status_code}")
        data = resp.json()
        if data.get("status") != "paid" or int(data.get("amount_paid",0)) < int(doc.get("amount",0)):
            send_with_premium(message.chat.id, "Payment is not confirmed yet. If you have just paid, wait briefly and try again.")
            return
        payment_rows = data.get("payments") or [{}]
        payment_id = str(payment_rows[0].get("payment_id", ""))
        _V5_SETTINGS.update_one({"_id":"payment_link_"+link_id},
            {"$set":{"status":"paid","paid_at":_v5_now(),"razorpay_payment_id":payment_id}})
        # Claim activation once. If user-record update fails, release the claim for retry.
        claim = _V5_SETTINGS.update_one({"_id":"payment_link_"+link_id,"membership_activated":{"$ne":True}},
            {"$set":{"membership_activated":True}})
        if getattr(claim,"modified_count",0):
            expiry = (datetime.now()+timedelta(days=int(doc.get("duration_days",c["duration_days"])))).strftime("%Y-%m-%d %H:%M:%S")
            try:
                _col_users.update_one({"user_id":int(message.from_user.id)},
                    {"$set":{"premium_until":expiry}},upsert=True)
            except Exception:
                _V5_SETTINGS.update_one({"_id":"payment_link_"+link_id},
                    {"$set":{"membership_activated":False}})
                logging.exception("[V5_PAYMENT] Membership activation failed")
                send_with_premium(message.chat.id,"Payment verified, but membership activation needs admin review. Contact support.")
                return
            _v5_audit(message.from_user.id,"razorpay_payment_verified",detail=link_id)
        send_with_premium(message.chat.id,"✅ Payment verified. Your premium membership is active.")
    except Exception:
        logging.exception("[V5_PAYMENT] Payment verification failed")
        send_with_premium(message.chat.id,"Could not verify payment right now. Please retry later.")


@bot.pre_checkout_query_handler(func=lambda query: bool(query.invoice_payload and query.invoice_payload.startswith("shown-premium:")))
def v5_stars_precheckout(query):
    c = _v5_payment_get()
    try:
        payload = str(query.invoice_payload or "")
        parts = payload.split(":")
        valid_payload = (len(parts) == 3 and parts[0] == "shown-premium"
                         and parts[1].isdigit() and int(parts[1]) == int(query.from_user.id))
        valid_amount = int(query.total_amount) == int(c.get("stars_amount", 0))
        valid_currency = str(query.currency) == "XTR"
        allowed = bool(c.get("payments_enabled") and c.get("stars_enabled")
                       and valid_payload and valid_amount and valid_currency)
        bot.answer_pre_checkout_query(query.id, allowed,
            error_message="Premium payment details are invalid or payments are unavailable.")
    except Exception:
        logging.exception("[V5_PAYMENT] Stars pre-checkout failed")


@bot.message_handler(content_types=["successful_payment"])
def v5_stars_successful_payment(message):
    payment = getattr(message, "successful_payment", None)
    if not payment or not str(payment.invoice_payload).startswith("shown-premium:"):
        return
    try:
        payload_parts = str(payment.invoice_payload or "").split(":")
        if (len(payload_parts) != 3 or payload_parts[0] != "shown-premium"
                or not payload_parts[1].isdigit() or int(payload_parts[1]) != int(message.from_user.id)
                or str(payment.currency) != "XTR"
                or int(payment.total_amount) != int(_v5_payment_get().get("stars_amount", 0))):
            logging.error("[V5_PAYMENT] Rejected mismatched Telegram Stars payment payload/user/amount")
            return
        charge_key = "stars_payment_"+str(payment.telegram_payment_charge_id)
        _V5_SETTINGS.update_one({"_id":charge_key},
            {"$setOnInsert":{"user_id":int(message.from_user.id),"amount":int(payment.total_amount),
                "currency":payment.currency,"created_at":_v5_now(),"status":"paid"}},upsert=True)
        claim = _V5_SETTINGS.update_one({"_id":charge_key,"membership_activated":{"$ne":True}},
            {"$set":{"membership_activated":True}})
        if getattr(claim,"modified_count",0):
            expiry = (datetime.now()+timedelta(days=int(_v5_payment_get()["duration_days"]))).strftime("%Y-%m-%d %H:%M:%S")
            try:
                _col_users.update_one({"user_id":int(message.from_user.id)},
                    {"$set":{"premium_until":expiry}},upsert=True)
            except Exception:
                _V5_SETTINGS.update_one({"_id":charge_key},{"$set":{"membership_activated":False}})
                raise
            _v5_audit(message.from_user.id,"telegram_stars_payment_verified",detail=str(payment.telegram_payment_charge_id))
        send_with_premium(message.chat.id,"✅ Telegram Stars payment received. Premium membership is active.")
    except Exception:
        logging.exception("[V5_PAYMENT] Stars membership activation failed")
        send_with_premium(message.chat.id,"Payment received, but activation failed. Contact support with your Telegram payment receipt.")


@bot.message_handler(commands=["privacy"])
def v5_privacy_command(message):
    text = _v5_user_privacy_text(message.from_user.id)
    kb = _v5_admin_kb([
        ("📦 Request My Data", "v5_user_export", "primary"),
        ("🗑 Request Account Deletion", "v5_user_delete", "danger"),
        ("⬅️ User Hub", "uh_home", "primary")])
    send_with_premium(message.chat.id, text, reply_markup=kb)


# Scheduled task runner: only executes explicitly supported internal tasks.
# It deliberately does not execute arbitrary code or shell commands.
def _v5_task_worker():
    while True:
        time.sleep(20)
        try:
            due = list(_V5_TASKS.find({"enabled": True, "status": "queued"}).limit(20))
            now = datetime.now()
            for task in due:
                try:
                    run_at = datetime.strptime(str(task.get("run_at")), "%Y-%m-%d %H:%M:%S")
                    if run_at > now:
                        continue
                    if task.get("task_type") == "notification":
                        _V5_NOTICES.insert_one({
                            "user_id": int(task["user_id"]), "title": str(task.get("title","Update"))[:100],
                            "body": str(task.get("body",""))[:1000], "read": False, "created_at": _v5_now()
                        })
                    _V5_TASKS.update_one({"_id": task["_id"]},
                        {"$set": {"status": "completed", "completed_at": _v5_now()}})
                except Exception as task_exc:
                    logging.exception("[V5_TASK] task failed: %s", task_exc)
                    try:
                        _V5_TASKS.update_one({"_id": task["_id"]},
                            {"$set": {"status": "failed", "last_error": str(task_exc)[:300]}})
                    except Exception:
                        pass
        except Exception:
            logging.exception("[V5_TASK_WORKER] error")


try:
    if not CLONE_INSTANCE:
        threading.Thread(target=_v5_task_worker, daemon=True, name="v5-task-worker").start()
except Exception:
    logging.exception("[V5] task worker startup failed")


def _v5_clone_recovery_worker():
    """Restart enabled clones after unexpected child-process exits, with backoff."""
    if CLONE_INSTANCE:
        return
    last_attempt = {}
    while True:
        time.sleep(30)
        try:
            rows = _clone_rows()
            for row in rows:
                clone_id = int(row["clone_id"])
                if not row.get("enabled"):
                    continue
                proc = _clone_processes.get(clone_id)
                if proc is not None and proc.poll() is None:
                    continue
                now = time.time()
                if now - last_attempt.get(clone_id, 0) < 120:
                    continue
                last_attempt[clone_id] = now
                try:
                    _clone_start(clone_id)
                    _admin_audit("clone_auto_recovery", 0, f"clone_id={clone_id}")
                except Exception as recovery_exc:
                    with _clone_db() as conn:
                        conn.execute("UPDATE clones SET last_error=? WHERE clone_id=?",
                                     (str(recovery_exc)[:500], clone_id))
                    logging.exception("[V5_CLONE_RECOVERY] clone %s failed", clone_id)
        except Exception:
            logging.exception("[V5_CLONE_RECOVERY] monitor failed")


try:
    if not CLONE_INSTANCE:
        threading.Thread(target=_v5_clone_recovery_worker, daemon=True,
                         name="v5-clone-recovery").start()
except Exception:
    logging.exception("[V5] clone recovery worker startup failed")
