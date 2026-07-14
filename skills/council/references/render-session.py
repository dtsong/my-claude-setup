#!/usr/bin/env python3
"""Council session page scribe (F11).

Regenerates session.html from the contents of a council session directory.
Idempotent full regeneration from disk state: concurrent invocations are
race-safe because the last writer includes everything present at that
moment. Python stdlib only.

Usage: python3 render-session.py <session-dir>

Template resolution: <session-dir>/session-page.template.html first, then
this script's own directory. Every input file is optional; missing content
renders as a pending state. Exit 1 only when the session dir is missing.
"""
import html as html_mod
import json
import re
import sys
from pathlib import Path

PHASE_ORDER = ["interview", "assembly", "deliberation", "verdict", "planning", "verification"]
PHASE_TITLES = {
    "interview": "Interview",
    "assembly": "Assembly",
    "deliberation": "Deliberation",
    "verdict": "Verdict",
    "planning": "Planning",
    "verification": "Verification",
}
BADGE_LABEL = {"pending": "Pending", "active": "In progress", "done": "Complete"}


def esc(value):
    return html_mod.escape(str(value), quote=True)


_INLINE = [
    (re.compile(r"`([^`]+)`"), r"<code>\1</code>"),
    (re.compile(r"\*\*([^*]+)\*\*"), r"<strong>\1</strong>"),
    (re.compile(r"(?<!\*)\*([^*]+)\*(?!\*)"), r"<em>\1</em>"),
    (re.compile(r"\[([^\]]+)\]\(([^)\s]+)\)"), r'<a href="\2">\1</a>'),
]


def inline_md(text):
    out = esc(text)
    for pattern, replacement in _INLINE:
        out = pattern.sub(replacement, out)
    return out


def md_to_html(text):
    """Minimal markdown: headings, fences, tables, lists, hr, paragraphs."""
    lines = text.splitlines()
    out, i, n = [], 0, len(lines)
    while i < n:
        stripped = lines[i].strip()
        if not stripped:
            i += 1
            continue
        if stripped.startswith("```"):
            block = []
            i += 1
            while i < n and not lines[i].strip().startswith("```"):
                block.append(lines[i])
                i += 1
            i += 1
            out.append("<pre><code>%s</code></pre>" % esc("\n".join(block)))
            continue
        heading = re.match(r"^(#{1,6})\s+(.*)$", stripped)
        if heading:
            level = min(len(heading.group(1)) + 2, 6)  # demote so page h1/h2 stay unique
            out.append("<h%d>%s</h%d>" % (level, inline_md(heading.group(2)), level))
            i += 1
            continue
        if re.match(r"^(-{3,}|_{3,}|\*{3,})$", stripped):
            out.append("<hr>")
            i += 1
            continue
        if stripped.startswith("|") and i + 1 < n and re.match(r"^\|[\s:|-]+\|?$", lines[i + 1].strip()):
            header_cells = [inline_md(c.strip()) for c in stripped.strip("|").split("|")]
            i += 2
            rows = []
            while i < n and lines[i].strip().startswith("|"):
                rows.append([inline_md(c.strip()) for c in lines[i].strip().strip("|").split("|")])
                i += 1
            thead = "".join("<th>%s</th>" % c for c in header_cells)
            tbody = "".join(
                "<tr>%s</tr>" % "".join("<td>%s</td>" % c for c in row) for row in rows
            )
            out.append(
                '<div class="tbl-wrap"><table><thead><tr>%s</tr></thead><tbody>%s</tbody></table></div>'
                % (thead, tbody)
            )
            continue
        if re.match(r"^([-*+]|\d+\.)\s+", stripped):
            ordered = bool(re.match(r"^\d+\.", stripped))
            items = []
            while i < n and re.match(r"^([-*+]|\d+\.)\s+", lines[i].strip()):
                item = re.sub(r"^([-*+]|\d+\.)\s+", "", lines[i].strip())
                items.append("<li>%s</li>" % inline_md(item))
                i += 1
            tag = "ol" if ordered else "ul"
            out.append("<%s>%s</%s>" % (tag, "".join(items), tag))
            continue
        paragraph = [stripped]
        i += 1
        while i < n and lines[i].strip() and not re.match(
            r"^(#{1,6}\s|```|\||[-*+]\s|\d+\.\s|-{3,}$)", lines[i].strip()
        ):
            paragraph.append(lines[i].strip())
            i += 1
        out.append("<p>%s</p>" % inline_md(" ".join(paragraph)))
    return "\n".join(out)


def read_text(path):
    try:
        return path.read_text(encoding="utf-8")
    except OSError:
        return ""


def load_state(session_dir):
    state = {}
    state_path = session_dir / "session-state.json"
    if state_path.exists():
        try:
            loaded = json.loads(state_path.read_text(encoding="utf-8"))
            if isinstance(loaded, dict):
                state = loaded
        except (OSError, json.JSONDecodeError):
            state = {}
    session_md = read_text(session_dir / "session.md")

    def meta(key, default=""):
        found = re.search(r"^%s:\s*(.+)$" % re.escape(key), session_md, re.MULTILINE)
        return found.group(1).strip() if found else default

    if "idea" not in state:
        first_line = session_md.splitlines()[0].strip() if session_md.strip() else ""
        idea = re.sub(r"^#\s*[^:]*:\s*", "", first_line).strip("# ").strip()
        state["idea"] = idea or session_dir.name
    state.setdefault("themeName", "Council")
    state.setdefault("mode", "standard")
    state.setdefault("profile", meta("Profile", "balanced"))
    state.setdefault("backend", meta("Backend", "workflow"))
    state.setdefault("sessionId", meta("Session ID", session_dir.name))
    state.setdefault("date", meta("Date", ""))
    state.setdefault("phase", meta("Phase", "interview"))
    state.setdefault("complete", False)
    state.setdefault("roster", [])
    state.setdefault("tensionPairs", [])
    state.setdefault("costEstimate", "")
    state.setdefault("phases", list(PHASE_ORDER))
    return state


def phase_status(state, phase_id, phases):
    if state.get("complete"):
        return "done"
    current = state.get("phase", phases[0] if phases else "interview")
    try:
        current_idx = phases.index(current)
    except ValueError:
        current_idx = 0
    idx = phases.index(phase_id)
    if idx < current_idx:
        return "done"
    if idx == current_idx:
        return "active"
    return "pending"


def badge(status):
    return '<span class="badge b-%s">%s</span>' % (status, BADGE_LABEL[status])


def card(title, color, status, body_html, summary_label="View"):
    dot = '<i class="dot" style="background:%s"></i>' % esc(color or "#6b7078")
    head = '<div class="card-head">%s<span class="card-title">%s</span>%s</div>' % (
        dot,
        esc(title),
        badge(status),
    )
    body = ""
    if body_html:
        body = '<details><summary>%s</summary><div class="card-body">%s</div></details>' % (
            esc(summary_label),
            body_html,
        )
    return '<div class="card">%s%s</div>' % (head, body)


def section_html(section_id, title, status, inner):
    return (
        '<section class="wrap" id="%s"><div class="sec-head"><h2>%s</h2>%s</div>%s</section>'
        % (section_id, esc(title), badge(status), inner)
    )


def roster_color(state, name):
    for member in state.get("roster", []):
        if member.get("name") == name:
            return member.get("color")
    return None


def build_interview(state, session_dir, status):
    parts = []
    transcript = read_text(session_dir / "interview-transcript.md")
    if transcript:
        parts.append('<div class="prose">%s</div>' % md_to_html(transcript))
    detail_files = sorted(session_dir.glob("detail-*.md"))
    if detail_files:
        cards = "".join(
            card(path.stem.replace("-", " ").title(), None, "done", md_to_html(read_text(path)), "View detail")
            for path in detail_files
        )
        parts.append("<h3>Detail asides</h3><div class=\"cards\">%s</div>" % cards)
    summary = read_text(session_dir / "interview-summary.md")
    if summary:
        parts.append(
            '<details><summary>Interview summary</summary><div class="card-body prose">%s</div></details>'
            % md_to_html(summary)
        )
    if not parts:
        parts.append('<p class="muted">Waiting for this phase.</p>')
    return "".join(parts)


def build_assembly(state, session_dir, status):
    roster = state.get("roster", [])
    if not roster:
        return '<p class="muted">Assembly has not selected a bench yet.</p>'
    rows = []
    for member in roster:
        skills = ", ".join(member.get("skills", [])) or "&mdash;"
        dot = '<i class="dot" style="background:%s"></i> ' % esc(member.get("color", "#6b7078"))
        score = member.get("score", "")
        rows.append(
            "<tr><td>%s%s</td><td>%s</td><td>%s</td><td>%s</td></tr>"
            % (dot, esc(member.get("name", "?")), esc(score), esc(member.get("rationale", "")), skills)
        )
    table = (
        '<div class="tbl-wrap"><table><thead><tr><th>Agent</th><th>Score</th><th>Rationale</th>'
        "<th>Loaded skills</th></tr></thead><tbody>%s</tbody></table></div>" % "".join(rows)
    )
    cost = state.get("costEstimate")
    cost_html = '<p class="muted">Estimated cost: %s</p>' % esc(cost) if cost else ""
    return table + cost_html


def round_cards(state, session_dir, round_dir, empty_note):
    roster = state.get("roster", [])
    cards = []
    seen = set()
    for member in roster:
        name = member.get("name", "?")
        path = round_dir / ("%s.md" % name)
        if path.exists():
            seen.add(path.name)
            cards.append(card(name, member.get("color"), "done", md_to_html(read_text(path)), "View position"))
        else:
            cards.append(card(name, member.get("color"), "pending", ""))
    for path in sorted(round_dir.glob("*.md")):
        if path.name not in seen and not roster:
            cards.append(card(path.stem, None, "done", md_to_html(read_text(path)), "View position"))
    if not cards:
        return '<p class="muted">%s</p>' % esc(empty_note)
    return '<div class="cards">%s</div>' % "".join(cards)


def build_deliberation(state, session_dir, status):
    parts = ["<h3>Round 1: Position</h3>"]
    parts.append(round_cards(state, session_dir, session_dir / "deliberation" / "round1", "No positions yet."))

    pairs = state.get("tensionPairs", [])
    if pairs:
        chips = []
        for pair in pairs:
            if isinstance(pair, dict):
                a, b, tension = pair.get("a", "?"), pair.get("b", "?"), pair.get("tension", "")
            else:
                a, b = (list(pair) + ["?", "?"])[:2]
                tension = ""
            dot_a = '<i class="dot" style="background:%s"></i>' % esc(roster_color(state, a) or "#6b7078")
            dot_b = '<i class="dot" style="background:%s"></i>' % esc(roster_color(state, b) or "#6b7078")
            label = ": %s" % esc(tension) if tension else ""
            chips.append(
                '<span class="pair">%s%s<span class="vs">VS</span>%s%s%s</span>'
                % (dot_a, esc(a), dot_b, esc(b), label)
            )
        parts.append("<h3>Tension pairs</h3><div>%s</div>" % "".join(chips))

    round2 = sorted((session_dir / "deliberation" / "round2").glob("*.md")) if (session_dir / "deliberation" / "round2").is_dir() else []
    if round2:
        cards = []
        for path in round2:
            match = re.match(r"^(.+?)-responds-to-(.+)$", path.stem)
            title = "%s responds to %s" % (match.group(1), match.group(2)) if match else path.stem
            color = roster_color(state, match.group(1)) if match else None
            cards.append(card(title, color, "done", md_to_html(read_text(path)), "View challenge"))
        parts.append('<h3>Round 2: Challenge</h3><div class="cards">%s</div>' % "".join(cards))
    elif pairs:
        parts.append('<h3>Round 2: Challenge</h3><p class="muted">Challenges in progress.</p>')

    round3_dir = session_dir / "deliberation" / "round3"
    if (round3_dir.is_dir() and any(round3_dir.glob("*.md"))) or status == "done":
        parts.append("<h3>Round 3: Converge</h3>")
        parts.append(round_cards(state, session_dir, round3_dir, "No final positions yet."))
    return "".join(parts)


def build_verdict(state, session_dir, status):
    design = read_text(session_dir / "design.md")
    if not design:
        return '<p class="muted">Synthesis has not produced a design yet.</p>'
    parts = []
    overview = re.search(r"##\s+Overview\s*\n(.*?)(?=\n##\s|\Z)", design, re.DOTALL)
    if overview:
        parts.append('<div class="prose">%s</div>' % md_to_html(overview.group(1).strip()))
    if (session_dir / "design.html").exists():
        parts.append('<p><a href="design.html">Open the full design verdict page</a></p>')
    parts.append(
        '<details><summary>Full design document</summary><div class="card-body prose">%s</div></details>'
        % md_to_html(design)
    )
    return "".join(parts)


def extract_block(text, heading):
    found = re.search(r"##\s+%s\s*\n(.*?)(?=\n##\s|\Z)" % re.escape(heading), text, re.DOTALL)
    return found.group(1).strip() if found else ""


def build_planning(state, session_dir, status):
    prd = read_text(session_dir / "prd.md")
    contract = read_text(session_dir / "acceptance-contract.md")
    if not prd and not contract:
        return '<p class="muted">Planning has not produced a PRD yet.</p>'
    parts = []
    if prd:
        goals = extract_block(prd, "Goals")
        if goals:
            parts.append('<h3>Goals</h3><div class="prose">%s</div>' % md_to_html(goals))
        parts.append(
            '<details><summary>Full PRD</summary><div class="card-body prose">%s</div></details>'
            % md_to_html(prd)
        )
    if contract:
        summary = extract_block(contract, "Verification Summary")
        if summary:
            parts.append('<h3>Acceptance contract</h3><div class="prose">%s</div>' % md_to_html(summary))
    return "".join(parts)


def build_verification(state, session_dir, status):
    contract = read_text(session_dir / "acceptance-contract.md")
    if not contract:
        return '<p class="muted">Verification has not started.</p>'
    summary = extract_block(contract, "Verification Summary")
    if not summary:
        return '<p class="muted">No verification summary recorded yet.</p>'
    return '<div class="prose">%s</div>' % md_to_html(summary)


SECTION_BUILDERS = {
    "interview": build_interview,
    "assembly": build_assembly,
    "deliberation": build_deliberation,
    "verdict": build_verdict,
    "planning": build_planning,
    "verification": build_verification,
}


def build_page(state, session_dir, template):
    phases = [p for p in state.get("phases", PHASE_ORDER) if p in SECTION_BUILDERS]
    if not phases:
        phases = list(PHASE_ORDER)

    tracker_items = []
    sections = []
    for phase_id in phases:
        status = phase_status(state, phase_id, phases)
        css = {"done": ' class="t-done"', "active": ' class="t-active"', "pending": ""}[status]
        tracker_items.append("<li%s>%s</li>" % (css, PHASE_TITLES[phase_id]))
        inner = SECTION_BUILDERS[phase_id](state, session_dir, status)
        sections.append(section_html(phase_id, PHASE_TITLES[phase_id], status, inner))

    roster = state.get("roster", [])
    if roster:
        colors = [m.get("color", "#6b7078") for m in roster]
        step = 100.0 / len(colors)
        stops = []
        for idx, color in enumerate(colors):
            stops.append("%s %d%%" % (color, round(idx * step)))
            stops.append("%s %d%%" % (color, round((idx + 1) * step)))
        spectrum = ", ".join(stops)
        bench = "".join(
            '<span><i class="dot" style="background:%s"></i>%s</span>'
            % (esc(m.get("color", "#6b7078")), esc(m.get("name", "?")))
            for m in roster
        )
    else:
        spectrum = "#3a3f4a 0%, #3a3f4a 100%"
        bench = '<span class="muted">Bench not yet assembled</span>'

    refresh = "" if state.get("complete") else '<meta http-equiv="refresh" content="10">'
    replacements = {
        "{{META_REFRESH}}": refresh,
        "{{TITLE}}": esc("%s Live: %s" % (state["themeName"], state["idea"][:60])),
        "{{THEME_NAME}}": esc(state["themeName"]),
        "{{SESSION_ID}}": esc(state["sessionId"]),
        "{{DATE}}": esc(state["date"] or ""),
        "{{MODE}}": esc(state["mode"]),
        "{{PROFILE}}": esc(state["profile"]),
        "{{BACKEND}}": esc(state["backend"]),
        "{{IDEA}}": esc(state["idea"]),
        "{{SPECTRUM_STOPS}}": spectrum,
        "{{BENCH}}": bench,
        "{{TRACKER}}": "".join(tracker_items),
        "{{SECTIONS}}": "\n".join(sections),
    }
    page = template
    for placeholder, value in replacements.items():
        page = page.replace(placeholder, value)
    return page


def main(argv):
    if len(argv) != 2:
        print("usage: render-session.py <session-dir>", file=sys.stderr)
        return 1
    session_dir = Path(argv[1])
    if not session_dir.is_dir():
        print("session dir not found: %s" % session_dir, file=sys.stderr)
        return 1
    template_path = session_dir / "session-page.template.html"
    if not template_path.exists():
        template_path = Path(__file__).resolve().parent / "session-page.template.html"
    if not template_path.exists():
        print("template not found: %s" % template_path, file=sys.stderr)
        return 1
    template = read_text(template_path)
    state = load_state(session_dir)
    (session_dir / "session.html").write_text(build_page(state, session_dir, template), encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
