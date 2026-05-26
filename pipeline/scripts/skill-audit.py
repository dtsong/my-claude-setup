#!/usr/bin/env python3
"""skill-audit.py — Tool-agnostic skill inventory audit.

Reports the audit signals that survive across any SKILL.md-based agent
(Claude, generic Markdown skill sets, …): duplicate detection, always-loaded
description cost, and an inventory summary. Unlike vendor-specific cleaners
this script has no hardcoded home paths, no model/budget assumptions, and no
usage-log scanning — pass it the roots you want and it audits them.

Principles adapted (and stripped of Codex specifics) from
steipete/agent-scripts skill-cleaner. See pipeline/scripts/README.md.

Usage:
    skill-audit.py                       # audit this repo's skills/
    skill-audit.py --root ~/.claude/skills
    skill-audit.py --root A --root B     # cross-root duplicate detection
    skill-audit.py --json                # machine-readable output
    skill-audit.py --desc-token-threshold 150 --top 15
"""

import argparse
import hashlib
import json
import math
import os
import re
import sys

# Words-to-tokens ratio, matching the rest of the governance pipeline
# (pipeline/hooks/_utils.py). Kept here so the script stays self-contained,
# consistent with the other pipeline/scripts entry points.
TOKEN_RATIO = 1.33

FRONTMATTER_RE = re.compile(r"^---\s*\n(.*?)\n---\s*\n?", re.DOTALL)


def find_repo_root(start):
    """Walk up from ``start`` looking for pipeline/config/; None if not found."""
    d = os.path.abspath(start)
    while True:
        if os.path.isdir(os.path.join(d, "pipeline", "config")):
            return d
        parent = os.path.dirname(d)
        if parent == d:
            return None
        d = parent


def estimate_tokens(words):
    return int(math.ceil(words * TOKEN_RATIO))


def parse_frontmatter(text):
    """Return (frontmatter_dict, body) for a SKILL.md.

    Minimal YAML reader: top-level ``key: value`` pairs plus folded scalars
    (``key: >`` / ``key: |``). Sufficient for name/description extraction
    without a YAML dependency.
    """
    match = FRONTMATTER_RE.match(text)
    if not match:
        return {}, text
    raw, body = match.group(1), text[match.end():]
    fields, key, folded = {}, None, []

    def flush():
        if key is not None and folded:
            fields[key] = " ".join(s.strip() for s in folded).strip()

    for line in raw.split("\n"):
        if re.match(r"^[A-Za-z0-9_-]+\s*:", line) and not line.startswith(" "):
            flush()
            folded = []
            k, _, v = line.partition(":")
            key = k.strip()
            v = v.strip()
            if v in (">", "|", ">-", "|-", ">+", "|+"):
                fields[key] = ""  # value continues on indented lines
            else:
                fields[key] = v.strip().strip('"').strip("'")
                key = None
        elif key is not None and (line.startswith(" ") or line.startswith("\t")):
            folded.append(line)
    flush()
    return fields, body


def normalize_body(body):
    """Collapse whitespace so cosmetic edits don't hide real body duplicates."""
    return re.sub(r"\s+", " ", body).strip()


def discover_skills(roots, follow_symlinks):
    """Find every SKILL.md under ``roots`` and extract audit metadata."""
    skills = []
    seen_real = set()
    for root in roots:
        root = os.path.abspath(os.path.expanduser(root))
        if not os.path.isdir(root):
            print(f"WARNING: root not found, skipping: {root}", file=sys.stderr)
            continue
        for dirpath, dirnames, filenames in os.walk(root, followlinks=follow_symlinks):
            dirnames[:] = [d for d in dirnames if d not in (".git", "node_modules")]
            if "SKILL.md" not in filenames:
                continue
            path = os.path.join(dirpath, "SKILL.md")
            real = os.path.realpath(path)
            if real in seen_real:  # same file reached via two roots/symlinks
                continue
            seen_real.add(real)
            try:
                with open(path, "r", encoding="utf-8") as f:
                    text = f.read()
            except (OSError, UnicodeDecodeError):
                continue
            fields, body = parse_frontmatter(text)
            norm = normalize_body(body)
            name = fields.get("name") or os.path.basename(dirpath)
            desc = fields.get("description", "")
            skills.append({
                "name": name,
                "description": desc,
                "desc_chars": len(desc),
                "desc_tokens": estimate_tokens(len(desc.split())),
                "path": path,
                "root": root,
                "body_hash": hashlib.sha1(norm.encode("utf-8")).hexdigest(),
            })
    return skills


def report_duplicates(skills):
    """Cluster skills by name and by normalized body hash."""
    by_name, by_body = {}, {}
    for s in skills:
        by_name.setdefault(s["name"], []).append(s)
        by_body.setdefault(s["body_hash"], []).append(s)

    name_dupes = {k: v for k, v in by_name.items() if len(v) > 1}
    body_dupes = {k: v for k, v in by_body.items() if len(v) > 1}
    return name_dupes, body_dupes


def render_markdown(skills, name_dupes, body_dupes, roots, desc_threshold, top):
    lines = ["# Skill Audit", ""]
    lines.append(f"Roots audited: {len(roots)}")
    for r in roots:
        lines.append(f"- {r}")
    total_desc_tokens = sum(s["desc_tokens"] for s in skills)
    lines += [
        "",
        f"Skills discovered: {len(skills)}",
        f"Always-loaded description cost: ~{total_desc_tokens} tokens "
        f"(sum of all `description` fields)",
        "",
    ]

    # --- Description cost ---
    lines += ["## Description Cost", ""]
    flagged = sorted(
        (s for s in skills if s["desc_tokens"] > desc_threshold),
        key=lambda s: s["desc_tokens"], reverse=True,
    )
    if flagged:
        lines.append(
            f"{len(flagged)} skill(s) over {desc_threshold} description tokens "
            f"(top {min(top, len(flagged))} shown):"
        )
        lines += ["", "| ~Tokens | Chars | Name | Path |", "|--------:|------:|------|------|"]
        for s in flagged[:top]:
            lines.append(
                f"| {s['desc_tokens']} | {s['desc_chars']} | {s['name']} | {s['path']} |"
            )
    else:
        lines.append(f"No descriptions exceed {desc_threshold} tokens.")
    lines.append("")

    # --- Duplicates by name ---
    lines += ["## Duplicate Names", ""]
    if name_dupes:
        lines.append(
            "Same `name` in multiple locations. Cross-tool/plugin copies are "
            "often intentional — confirm before removing:"
        )
        lines.append("")
        for name in sorted(name_dupes):
            lines.append(f"- **{name}**")
            for s in sorted(name_dupes[name], key=lambda x: x["path"]):
                same_body = s["body_hash"] == name_dupes[name][0]["body_hash"]
                tag = "identical body" if same_body else "DIFFERENT body"
                lines.append(f"  - {s['path']} ({tag})")
    else:
        lines.append("No duplicate names found.")
    lines.append("")

    # --- Duplicates by body ---
    lines += ["## Identical Bodies (different names)", ""]
    cross_name = {
        h: v for h, v in body_dupes.items()
        if len({s["name"] for s in v}) > 1
    }
    if cross_name:
        lines.append("Byte-identical bodies under different names (possible drift/copy):")
        lines.append("")
        for h, v in cross_name.items():
            names = ", ".join(sorted({s["name"] for s in v}))
            lines.append(f"- {names}")
            for s in sorted(v, key=lambda x: x["path"]):
                lines.append(f"  - {s['path']}")
    else:
        lines.append("No identical bodies across differing names.")
    lines.append("")

    # --- Inventory ---
    lines += ["## Inventory By Root", ""]
    lines += ["| Root | Skills |", "|------|-------:|"]
    per_root = {}
    for s in skills:
        per_root[s["root"]] = per_root.get(s["root"], 0) + 1
    for r in roots:
        lines.append(f"| {r} | {per_root.get(os.path.abspath(os.path.expanduser(r)), 0)} |")
    lines.append("")
    return "\n".join(lines)


def build_json(skills, name_dupes, body_dupes, roots, desc_threshold):
    return {
        "roots": roots,
        "skill_count": len(skills),
        "total_description_tokens": sum(s["desc_tokens"] for s in skills),
        "description_threshold_tokens": desc_threshold,
        "over_threshold": [
            {"name": s["name"], "desc_tokens": s["desc_tokens"],
             "desc_chars": s["desc_chars"], "path": s["path"]}
            for s in sorted(skills, key=lambda s: s["desc_tokens"], reverse=True)
            if s["desc_tokens"] > desc_threshold
        ],
        "duplicate_names": {
            name: [s["path"] for s in v] for name, v in name_dupes.items()
        },
        "identical_bodies": [
            {"names": sorted({s["name"] for s in v}), "paths": [s["path"] for s in v]}
            for v in body_dupes.values()
            if len({s["name"] for s in v}) > 1
        ],
    }


def main():
    parser = argparse.ArgumentParser(description="Tool-agnostic skill inventory audit.")
    parser.add_argument(
        "--root", action="append", default=[],
        help="Skill root to scan (repeatable). Defaults to this repo's skills/.",
    )
    parser.add_argument(
        "--desc-token-threshold", type=int, default=120,
        help="Flag descriptions above this estimated token count (default: 120).",
    )
    parser.add_argument(
        "--top", type=int, default=20,
        help="Max rows in the description-cost table (default: 20).",
    )
    parser.add_argument(
        "--follow-symlinks", action="store_true",
        help="Descend into symlinked directories while scanning.",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of Markdown.")
    args = parser.parse_args()

    roots = args.root
    if not roots:
        repo_root = find_repo_root(os.path.dirname(os.path.abspath(__file__)))
        if repo_root is None:
            print("ERROR: no --root given and repo root not found", file=sys.stderr)
            sys.exit(1)
        roots = [os.path.join(repo_root, "skills")]

    skills = discover_skills(roots, args.follow_symlinks)
    if not skills:
        print("No SKILL.md files found under the given roots.", file=sys.stderr)
        sys.exit(1)

    name_dupes, body_dupes = report_duplicates(skills)

    if args.json:
        print(json.dumps(
            build_json(skills, name_dupes, body_dupes, roots, args.desc_token_threshold),
            indent=2,
        ))
    else:
        print(render_markdown(
            skills, name_dupes, body_dupes, roots,
            args.desc_token_threshold, args.top,
        ))


if __name__ == "__main__":
    main()
