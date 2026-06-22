import json
import os

import routing


def test_default_routing_path_points_at_council_config():
    assert routing.DEFAULT_ROUTING_PATH.replace("\\", "/").endswith(
        "skills/council/model-routing.json"
    )


def test_load_routing_reads_real_config():
    data = routing.load_routing()
    assert data["tasks"]["classification"] == "openai/gpt-4o-mini"
    assert data["defaults"]["fallback"] == "claude"


def test_load_routing_missing_file_returns_empty():
    assert routing.load_routing("/no/such/file.json") == {}


def test_load_routing_bad_json_returns_empty(tmp_path):
    bad = tmp_path / "bad.json"
    bad.write_text("{not json")
    assert routing.load_routing(str(bad)) == {}


def test_resolve_task_model_known():
    data = {"tasks": {"classification": "openai/gpt-4o-mini"},
            "defaults": {"fallback": "claude"}}
    assert routing.resolve_task_model(data, "classification") == "openai/gpt-4o-mini"


def test_resolve_task_model_unknown_falls_back():
    data = {"tasks": {}, "defaults": {"fallback": "claude"}}
    assert routing.resolve_task_model(data, "mystery") == "claude"


def test_resolve_task_model_empty_routing_falls_back():
    assert routing.resolve_task_model({}, "classification") == "claude"


def test_resolve_lens_model_default():
    data = {"lenses": {}, "defaults": {"lens": "claude"}}
    assert routing.resolve_lens_model(data, "skeptic") == "claude"


def test_resolve_lens_model_override():
    data = {"lenses": {"scout": "google/gemini-flash-1.5"},
            "defaults": {"lens": "claude"}}
    assert routing.resolve_lens_model(data, "scout") == "google/gemini-flash-1.5"
