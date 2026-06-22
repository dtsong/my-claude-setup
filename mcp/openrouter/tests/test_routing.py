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


SUCCESS_BODY = {
    "model": "openai/gpt-4o-mini",
    "choices": [{"message": {"content": "spam"}}],
    "usage": {"prompt_tokens": 4, "completion_tokens": 1},
}


def test_routed_consult_routes_to_cheap_model():
    captured = {}

    def fake_transport(url, headers, payload, timeout):
        captured["model"] = payload["model"]
        return 200, SUCCESS_BODY

    table = {"tasks": {"classification": "openai/gpt-4o-mini"},
             "defaults": {"fallback": "claude"}}
    out = routing.routed_consult(
        "classification", "classify this", "input text",
        routing=table, api_key="sk-x", transport=fake_transport,
    )
    assert out["text"] == "spam"
    assert captured["model"] == "openai/gpt-4o-mini"


def test_routed_consult_claude_task_skips_network():
    def boom(*a, **k):
        raise AssertionError("network must not be called for claude routing")

    table = {"tasks": {"summary": "claude"}, "defaults": {"fallback": "claude"}}
    out = routing.routed_consult("summary", "s", "p",
                                 routing=table, transport=boom)
    assert out["fallback"] == "claude"
    assert "reason" in out


def test_routed_consult_unmapped_task_falls_back_to_claude():
    table = {"tasks": {}, "defaults": {"fallback": "claude"}}
    out = routing.routed_consult("mystery", "s", "p", routing=table)
    assert out["fallback"] == "claude"


def test_routed_consult_propagates_consult_failure():
    table = {"tasks": {"classification": "openai/gpt-4o-mini"},
             "defaults": {"fallback": "claude"}}
    out = routing.routed_consult(
        "classification", "s", "p", routing=table, api_key="sk-x",
        transport=lambda *a, **k: (500, {}),
    )
    assert out["fallback"] == "claude"
    assert out["error_kind"] == "http"
