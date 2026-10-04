"""Tests for the STE-lite transcript scorer (pipeline/scripts/ste-score.py).

The scorer is heuristic, so these tests pin the behavior of each detector on
small, unambiguous inputs and check before/after bucketing end to end.
"""
import importlib.util
import json
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "ste-score.py"
_spec = importlib.util.spec_from_file_location("ste_score", SCRIPT)
ste = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ste)


def write_transcript(path, start, texts, sidechain=False):
    lines = [{"type": "user", "timestamp": start, "message": {"content": "hi"}}]
    for text in texts:
        lines.append({
            "type": "assistant",
            "timestamp": start,
            "isSidechain": sidechain,
            "message": {"content": [{"type": "thinking", "thinking": "x"}, {"type": "text", "text": text}]},
        })
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(json.dumps(line) for line in lines) + "\n")


def test_strip_markdown_drops_code_headers_and_table_separators():
    text = "# Title\n\n```py\nx = 1\n```\n\n| A | B |\n|---|---|\n| one cell | two cell |\n- **Bold** bullet with `code`."
    assert ste.strip_markdown(text) == ["A", "B", "one cell", "two cell", "Bold bullet with CODE."]


def test_split_sentences():
    assert ste.split_sentences("The hook runs. It blocks the commit! Done?") == [
        "The hook runs.", "It blocks the commit!", "Done?"
    ]


def test_passive_detection():
    assert ste.PASSIVE_RE.findall("The commit is blocked by the hook.")
    assert ste.PASSIVE_RE.findall("The file was written twice.")
    assert not ste.PASSIVE_RE.findall("The hook blocks the commit.")
    assert not ste.PASSIVE_RE.findall("You will need it.")
    assert not ste.PASSIVE_RE.findall("The speed is high.")


def test_noun_cluster_detection():
    assert ste.count_noun_clusters("Fix the session token refresh retry policy now.") == 1
    assert ste.count_noun_clusters("Fix the retry policy for the session token refresh.") == 0
    assert ste.count_noun_clusters("Install token refresh, retry policy.") == 0
    assert ste.count_noun_clusters("The school is in North County San Diego.") == 0


def test_bucket_metrics_count_hedges_markers_and_dashes():
    bucket = ste.Bucket("all")
    bucket.add_text("s1", "Perhaps the hook fails \u2014 check it. Unverified: the gate exits 2.", 3)
    m = bucket.metrics()
    assert m["sessions"] == 1
    assert m["filler_hedges_per_1k_words"] > 0
    assert m["calibrated_markers_per_1k_words"] > 0
    assert m["em_dashes_per_1k_words"] > 0


def test_short_fragments_excluded_from_sentence_stats():
    bucket = ste.Bucket("all")
    bucket.add_text("s1", "| Adopt | Skip |\n|---|---|\n\nThe hook blocks the commit.", 3)
    assert bucket.metrics()["sentences"] == 1


def test_split_buckets_by_session_start(tmp_path, capsys):
    proj = tmp_path / "-proj-a"
    write_transcript(proj / "old.jsonl", "2026-01-01T00:00:00Z", ["The commit is blocked by the hook today."])
    write_transcript(proj / "new.jsonl", "2026-02-01T00:00:00Z", ["The hook blocks the commit today."])
    write_transcript(proj / "sub.jsonl", "2026-02-01T00:00:00Z", ["Ignored subagent text here."], sidechain=True)
    ste.main(["--root", str(tmp_path), "--split", "2026-01-15T00:00:00Z", "--json"])
    out = json.loads(capsys.readouterr().out)
    assert out["before"]["passive_per_100_sentences"] == 100.0
    assert out["after"]["passive_per_100_sentences"] == 0.0
    assert out["after"]["sessions"] == 1


def test_markdown_report_has_delta_column(tmp_path, capsys):
    proj = tmp_path / "-proj-a"
    write_transcript(proj / "a.jsonl", "2026-01-01T00:00:00Z", ["The hook blocks the commit today."])
    ste.main(["--root", str(tmp_path), "--split", "2026-06-01T00:00:00Z"])
    out = capsys.readouterr().out
    assert "| Metric | before | after | Delta | Target |" in out
    assert "| sessions | 1 | 0 | -1 |" in out
