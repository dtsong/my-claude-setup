#!/usr/bin/env python3
"""ste-score.py: Score assistant prose in Claude Code transcripts against the STE-lite rules.

The STE-lite rules live in the "Writing Rules" section of CLAUDE.md. This script
measures how closely assistant text follows them, so a rule change can be judged
by numbers instead of impressions. Use --split to compare sessions that started
before and after a change (CLAUDE.md loads at session start, so sessions are
bucketed by their first timestamp).

All metrics are regex heuristics (stdlib only, no POS tagger). Compare deltas
between buckets; do not treat absolute values as exact.
"""

import argparse
import json
import math
import re
import sys
from datetime import datetime
from pathlib import Path

DEFAULT_ROOT = Path.home() / ".claude" / "projects"

# Sentences shorter than this are labels or table fragments, not prose.
DEFAULT_MIN_WORDS = 3

FENCE_RE = re.compile(r"^(`{3,}|~{3,}).*?^\1[ \t]*$", re.MULTILINE | re.DOTALL)
INLINE_CODE_RE = re.compile(r"`[^`\n]+`")
URL_RE = re.compile(r"https?://\S+")
LINK_RE = re.compile(r"\[([^\]]+)\]\([^)]+\)")
TABLE_SEP_RE = re.compile(r"^\s*\|?\s*:?-{3,}")
LIST_MARKER_RE = re.compile(r"^\s*(?:[-*+]|\d+[.)])\s+")
SENTENCE_SPLIT_RE = re.compile(r"(?<=[.!?])\s+(?=[A-Z0-9\"'(])")
WORD_RE = re.compile(r"[A-Za-z][A-Za-z'’-]*|\d[\d.,%]*")

BE_FORMS = r"(?:am|is|are|was|were|be|been|being|get|gets|got|gotten)"
IRREGULAR_PARTICIPLES = (
    "built|chosen|done|drawn|driven|found|given|held|hidden|kept|known|left|lost|"
    "made|meant|paid|read|seen|sent|shown|spent|taken|told|thrown|understood|written"
)
PASSIVE_RE = re.compile(
    rf"\b{BE_FORMS}\s+(?:\w+ly\s+)?(?:(?!\w*eed\b)\w{{2,}}ed|{IRREGULAR_PARTICIPLES})\b",
    re.IGNORECASE,
)

NOMINALIZATION_RE = re.compile(r"^[a-z]{3,}(?:tion|sion|ment|ance|ence|ity|ness)s?$")

FILLER_HEDGES = (
    "it seems",
    "it appears",
    "perhaps",
    "arguably",
    "i think",
    "i believe",
    "might be worth",
    "may want to consider",
    "it's possible that",
    "it is possible that",
    "to some extent",
    "sort of",
    "kind of",
)
CALIBRATED_MARKERS = ("unverified:", "likely (not tested)", "not tested:", "untested:")

# Function words and auxiliaries break a noun-cluster run. Anything else
# (nouns, adjectives, and some verbs) extends it, which makes this a proxy.
STOPWORDS = frozenset(
    """
    a an the this that these those it its it's i you we they he she me us them my your our
    their his her and or but nor so yet if then than as of in on at to for from by with
    without into onto over under about after before between through during per via vs
    is am are was were be been being do does did done have has had will would can could
    shall should may might must not no yes all any each every some most more less few
    many much other such only also just very too here there when where which who whom
    whose what why how while because although though since until unless whether either
    neither both one two three four five
    """.split()
)
NOUN_CLUSTER_MIN = 4


def strip_markdown(text):
    """Return prose segments (one per line or table cell) with code, URLs, and markup removed."""
    text = FENCE_RE.sub("\n", text)
    text = INLINE_CODE_RE.sub("CODE", text)
    text = LINK_RE.sub(r"\1", text)
    text = URL_RE.sub("URL", text)
    segments = []
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#") or TABLE_SEP_RE.match(stripped):
            continue
        stripped = stripped.lstrip(">").strip()
        cells = stripped.strip("|").split("|") if stripped.startswith("|") else [stripped]
        for cell in cells:
            cell = LIST_MARKER_RE.sub("", cell).replace("**", "").replace("__", "").strip()
            if cell:
                segments.append(cell)
    return segments


def split_sentences(segment):
    return [s.strip() for s in SENTENCE_SPLIT_RE.split(segment) if s.strip()]


def words(sentence):
    return WORD_RE.findall(sentence)


def count_noun_clusters(sentence):
    """Count runs of NOUN_CLUSTER_MIN+ content words with no punctuation or function word between them.

    Capitalized words after the first token are treated as proper or technical
    names, which the rules exempt, so they break a run.
    """
    clusters = 0
    run = 0
    for index, token in enumerate(sentence.split()):
        core = token.strip("\"'()[]*_").rstrip(".,;:!?")
        breaks_after = bool(re.search(r"[.,;:!?)\]]$", token))
        is_content = (
            bool(re.fullmatch(r"[A-Za-z][A-Za-z-]*", core))
            and core.lower() not in STOPWORDS
            and not core.lower().endswith("ly")
            and (index == 0 or not core[0].isupper())
        )
        if is_content:
            run += 1
        else:
            if run >= NOUN_CLUSTER_MIN:
                clusters += 1
            run = 0
        if breaks_after:
            if run >= NOUN_CLUSTER_MIN:
                clusters += 1
            run = 0
    if run >= NOUN_CLUSTER_MIN:
        clusters += 1
    return clusters


class Bucket:
    def __init__(self, name):
        self.name = name
        self.sessions = set()
        self.responses = 0
        self.words = 0
        self.sentence_lengths = []
        self.passive = 0
        self.noun_clusters = 0
        self.nominalizations = 0
        self.filler_hedges = 0
        self.calibrated = 0
        self.em_dashes = 0

    def add_text(self, session_id, text, min_words):
        self.sessions.add(session_id)
        self.responses += 1
        lowered = text.lower()
        self.em_dashes += text.count("\u2014")
        self.calibrated += sum(lowered.count(m) for m in CALIBRATED_MARKERS)
        for segment in strip_markdown(text):
            seg_lower = segment.lower()
            self.filler_hedges += sum(
                len(re.findall(rf"\b{re.escape(h)}\b", seg_lower)) for h in FILLER_HEDGES
            )
            for sentence in split_sentences(segment):
                tokens = words(sentence)
                self.words += len(tokens)
                self.nominalizations += sum(
                    1 for t in tokens if NOMINALIZATION_RE.match(t.lower())
                )
                if len(tokens) < min_words:
                    continue
                self.sentence_lengths.append(len(tokens))
                self.passive += len(PASSIVE_RE.findall(sentence))
                self.noun_clusters += count_noun_clusters(sentence)

    def metrics(self):
        n = len(self.sentence_lengths)
        lengths = sorted(self.sentence_lengths)

        def per(count, base, scale):
            return round(count * scale / base, 2) if base else None

        return {
            "sessions": len(self.sessions),
            "responses": self.responses,
            "words": self.words,
            "sentences": n,
            "mean_sentence_words": round(sum(lengths) / n, 2) if n else None,
            "p90_sentence_words": lengths[min(n - 1, math.ceil(0.9 * n) - 1)] if n else None,
            "pct_sentences_over_20": per(sum(1 for x in lengths if x > 20), n, 100),
            "pct_sentences_over_25": per(sum(1 for x in lengths if x > 25), n, 100),
            "passive_per_100_sentences": per(self.passive, n, 100),
            "noun_clusters_per_100_sentences": per(self.noun_clusters, n, 100),
            "nominalizations_per_1k_words": per(self.nominalizations, self.words, 1000),
            "filler_hedges_per_1k_words": per(self.filler_hedges, self.words, 1000),
            "calibrated_markers_per_1k_words": per(self.calibrated, self.words, 1000),
            "em_dashes_per_1k_words": per(self.em_dashes, self.words, 1000),
        }


# (metric, direction the STE-lite rules should push it)
REPORT_ROWS = [
    ("sessions", ""),
    ("responses", ""),
    ("words", ""),
    ("sentences", ""),
    ("mean_sentence_words", "down"),
    ("p90_sentence_words", "down"),
    ("pct_sentences_over_20", "down"),
    ("pct_sentences_over_25", "down"),
    ("passive_per_100_sentences", "down"),
    ("noun_clusters_per_100_sentences", "down"),
    ("nominalizations_per_1k_words", "down"),
    ("filler_hedges_per_1k_words", "down"),
    ("calibrated_markers_per_1k_words", "up"),
    ("em_dashes_per_1k_words", "down"),
]


def parse_time(value):
    """Parse an ISO 8601 timestamp. Naive values are read as local time."""
    dt = datetime.fromisoformat(value.replace("Z", "+00:00"))
    return dt if dt.tzinfo else dt.astimezone()


def iter_session(path, include_subagents):
    """Yield (timestamp, text) for each assistant text block in one transcript file."""
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            try:
                entry = json.loads(line)
            except json.JSONDecodeError:
                continue
            if entry.get("type") != "assistant":
                continue
            if entry.get("isSidechain") and not include_subagents:
                continue
            content = (entry.get("message") or {}).get("content")
            if not isinstance(content, list):
                continue
            for block in content:
                if isinstance(block, dict) and block.get("type") == "text" and block.get("text"):
                    yield entry.get("timestamp"), block["text"]


def session_start(path):
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            try:
                ts = json.loads(line).get("timestamp")
            except (json.JSONDecodeError, AttributeError):
                continue
            if ts:
                return parse_time(ts)
    return None


def collect(args):
    root = Path(args.root).expanduser()
    if not root.is_dir():
        sys.exit(f"ste-score: transcript root not found: {root}")
    split = parse_time(args.split) if args.split else None
    since = parse_time(args.since) if args.since else None
    until = parse_time(args.until) if args.until else None

    buckets = {name: Bucket(name) for name in (("before", "after") if split else ("all",))}
    for path in sorted(root.glob("*/*.jsonl")):
        if args.project and args.project not in path.parent.name:
            continue
        start = session_start(path)
        if start is None:
            continue
        if (since and start < since) or (until and start >= until):
            continue
        bucket = buckets["all"] if not split else buckets["before" if start < split else "after"]
        for _, text in iter_session(path, args.include_subagents):
            bucket.add_text(path.stem, text, args.min_words)
    return {name: b.metrics() for name, b in buckets.items()}


def fmt(value):
    return "n/a" if value is None else str(value)


def render_markdown(results):
    names = list(results)
    header = ["Metric"] + names + (["Delta", "Target"] if len(names) == 2 else ["Target"])
    lines = ["| " + " | ".join(header) + " |", "|" + "---|" * len(header)]
    for metric, direction in REPORT_ROWS:
        values = [results[n][metric] for n in names]
        row = [metric] + [fmt(v) for v in values]
        if len(names) == 2:
            a, b = values
            row.append(fmt(round(b - a, 2)) if a is not None and b is not None else "n/a")
        row.append(direction)
        lines.append("| " + " | ".join(row) + " |")
    return "\n".join(lines)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", default=str(DEFAULT_ROOT), help="Transcript root (default: %(default)s).")
    parser.add_argument("--project", help="Only score project dirs whose name contains this substring.")
    parser.add_argument("--split", help="ISO time. Compare sessions started before vs. after it.")
    parser.add_argument("--since", help="ISO time. Skip sessions started before it.")
    parser.add_argument("--until", help="ISO time. Skip sessions started at or after it.")
    parser.add_argument("--min-words", type=int, default=DEFAULT_MIN_WORDS,
                        help="Ignore shorter sentences in sentence metrics (default: %(default)s).")
    parser.add_argument("--include-subagents", action="store_true", help="Also score sidechain (subagent) text.")
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of Markdown.")
    args = parser.parse_args(argv)

    results = collect(args)
    if args.json:
        print(json.dumps(results, indent=2))
    else:
        print(render_markdown(results))


if __name__ == "__main__":
    main()
