"""Tests for the council session page scribe (F11).

The scribe regenerates session.html from whatever exists in a session dir.
These tests exercise the three lifecycle states (empty, mid-deliberation,
complete), idempotency, and the minimal markdown converter.
"""
import json
import subprocess
import sys
from pathlib import Path

REFS = Path(__file__).resolve().parents[2] / "skills" / "council" / "references"
SCRIPT = REFS / "render-session.py"

ROSTER5 = [
    {"name": "Architect", "color": "#60a5fa", "score": 9, "rationale": "Core systems", "skills": ["codebase-context"], "status": "active"},
    {"name": "Advocate", "color": "#34d399", "score": 8, "rationale": "UX shape", "skills": [], "status": "active"},
    {"name": "Skeptic", "color": "#e5484d", "score": 8, "rationale": "Risk", "skills": [], "status": "active"},
    {"name": "Guardian", "color": "#c0c5ce", "score": 7, "rationale": "Privacy", "skills": [], "status": "active"},
    {"name": "Oracle", "color": "#8b7cf6", "score": 7, "rationale": "AI surface", "skills": [], "status": "active"},
]


def run_scribe(session_dir):
    return subprocess.run(
        [sys.executable, str(SCRIPT), str(session_dir)],
        capture_output=True,
        text=True,
    )


def make_state(**overrides):
    state = {
        "phase": "interview",
        "complete": False,
        "idea": "Test Idea",
        "mode": "standard",
        "profile": "balanced",
        "backend": "workflow",
        "roster": [],
        "tensionPairs": [],
        "phases": ["interview", "assembly", "deliberation", "verdict", "planning", "verification"],
    }
    state.update(overrides)
    return state


def write_session(tmp_path, state):
    (tmp_path / "session-state.json").write_text(json.dumps(state), encoding="utf-8")
    return tmp_path


def test_empty_session_renders_pending_with_refresh(tmp_path):
    write_session(tmp_path, make_state())
    result = run_scribe(tmp_path)
    assert result.returncode == 0, result.stderr
    html = (tmp_path / "session.html").read_text(encoding="utf-8")
    assert 'http-equiv="refresh"' in html
    assert "Pending" in html
    assert "Test Idea" in html


def test_mid_round1_shows_partial_positions(tmp_path):
    write_session(tmp_path, make_state(phase="deliberation", roster=ROSTER5))
    r1 = tmp_path / "deliberation" / "round1"
    r1.mkdir(parents=True)
    (r1 / "Architect.md").write_text("# Position\n\nUse a **modular** engine.", encoding="utf-8")
    (r1 / "Skeptic.md").write_text("# Position\n\nScope risk is real.", encoding="utf-8")
    result = run_scribe(tmp_path)
    assert result.returncode == 0, result.stderr
    html = (tmp_path / "session.html").read_text(encoding="utf-8")
    assert html.count("b-done") >= 2
    assert "modular" in html
    assert "b-pending" in html  # remaining agents still deliberating


def test_complete_session_drops_refresh_tag(tmp_path):
    write_session(tmp_path, make_state(phase="verification", complete=True, roster=ROSTER5))
    (tmp_path / "design.md").write_text(
        "# Design Document: Test Idea\n\n## Overview\n\nA unified verdict.\n\n## Architecture\n\nDetails here.",
        encoding="utf-8",
    )
    result = run_scribe(tmp_path)
    assert result.returncode == 0, result.stderr
    html = (tmp_path / "session.html").read_text(encoding="utf-8")
    assert 'http-equiv="refresh"' not in html
    assert "A unified verdict." in html


def test_regeneration_is_idempotent(tmp_path):
    write_session(tmp_path, make_state(roster=ROSTER5))
    assert run_scribe(tmp_path).returncode == 0
    first = (tmp_path / "session.html").read_bytes()
    assert run_scribe(tmp_path).returncode == 0
    assert (tmp_path / "session.html").read_bytes() == first


def test_markdown_tables_render(tmp_path):
    write_session(tmp_path, make_state())
    (tmp_path / "interview-transcript.md").write_text(
        "## Round 1\n\n**Q:** Shape?\n**A:** Hybrid.\n\n| Option | Cost |\n|---|---|\n| Lean | Low |\n| Full | High |\n",
        encoding="utf-8",
    )
    result = run_scribe(tmp_path)
    assert result.returncode == 0, result.stderr
    html = (tmp_path / "session.html").read_text(encoding="utf-8")
    assert "<table>" in html
    assert "<td>Lean</td>" in html


def test_missing_session_dir_fails(tmp_path):
    result = run_scribe(tmp_path / "does-not-exist")
    assert result.returncode == 1
