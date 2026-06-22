import io
import urllib.error

import openrouter_client as oc


def test_build_payload_minimal():
    payload = oc.build_payload("openai/gpt-4o-mini", "be terse", "hello")
    assert payload["model"] == "openai/gpt-4o-mini"
    assert payload["messages"] == [
        {"role": "system", "content": "be terse"},
        {"role": "user", "content": "hello"},
    ]
    assert payload["max_tokens"] == oc.DEFAULT_MAX_TOKENS
    assert "temperature" not in payload  # omitted when None


def test_build_payload_with_temperature():
    payload = oc.build_payload("m", "s", "p", max_tokens=42, temperature=0.2)
    assert payload["max_tokens"] == 42
    assert payload["temperature"] == 0.2


def test_build_headers():
    headers = oc.build_headers("sk-test")
    assert headers["Authorization"] == "Bearer sk-test"
    assert headers["Content-Type"] == "application/json"
    assert "HTTP-Referer" in headers
    assert "X-Title" in headers


SUCCESS_BODY = {
    "model": "openai/gpt-4o-mini",
    "choices": [{"message": {"role": "assistant", "content": "hi there"}}],
    "usage": {"prompt_tokens": 7, "completion_tokens": 3},
}


def test_parse_success():
    out = oc.parse_success(SUCCESS_BODY)
    assert out == {
        "text": "hi there",
        "model": "openai/gpt-4o-mini",
        "usage": {"prompt_tokens": 7, "completion_tokens": 3},
    }


def test_fallback_error_shape():
    err = oc.fallback_error("boom", kind="http")
    assert err["error"] == "boom"
    assert err["error_kind"] == "http"
    assert err["fallback"] == "claude"


def test_consult_happy_path():
    captured = {}

    def fake_transport(url, headers, payload, timeout):
        captured["url"] = url
        captured["headers"] = headers
        captured["payload"] = payload
        return 200, SUCCESS_BODY

    out = oc.consult("openai/gpt-4o-mini", "sys", "usr",
                     api_key="sk-x", transport=fake_transport)
    assert out["text"] == "hi there"
    assert captured["url"] == oc.OPENROUTER_URL
    assert captured["headers"]["Authorization"] == "Bearer sk-x"
    assert captured["payload"]["model"] == "openai/gpt-4o-mini"


def test_consult_missing_key_fails_soft(monkeypatch):
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
    out = oc.consult("m", "s", "p", transport=lambda *a, **k: (200, SUCCESS_BODY))
    assert out["fallback"] == "claude"
    assert out["error_kind"] == "missing_key"


def test_consult_http_error_fails_soft():
    out = oc.consult("m", "s", "p", api_key="sk-x",
                     transport=lambda *a, **k: (500, {"error": "nope"}))
    assert out["fallback"] == "claude"
    assert out["error_kind"] == "http"


def test_consult_transport_exception_fails_soft():
    def boom(*a, **k):
        raise TimeoutError("slow")

    out = oc.consult("m", "s", "p", api_key="sk-x", transport=boom)
    assert out["fallback"] == "claude"
    assert out["error_kind"] == "transport"


def test_consult_bad_shape_fails_soft():
    out = oc.consult("m", "s", "p", api_key="sk-x",
                     transport=lambda *a, **k: (200, {"unexpected": 1}))
    assert out["fallback"] == "claude"
    assert out["error_kind"] == "parse"


def test_urllib_transport_maps_http_error_to_status(monkeypatch):
    """urllib_transport should return (code, body) on HTTPError, not raise."""
    exc = urllib.error.HTTPError(
        url="https://openrouter.ai/api/v1/chat/completions",
        code=429, msg="rate", hdrs=None,
        fp=io.BytesIO(b'{"error":"slow down"}'),
    )

    def fake_urlopen(req, timeout):
        raise exc

    monkeypatch.setattr(oc.urllib.request, "urlopen", fake_urlopen)
    status, body = oc.urllib_transport(oc.OPENROUTER_URL, {}, {}, 10)
    assert status == 429
    assert body == {"error": "slow down"}


def test_consult_null_content_fails_soft():
    """content=None in a 200 response should produce error_kind='parse', not succeed."""
    null_content_body = {
        "choices": [{"message": {"content": None}}],
        "usage": {},
    }

    out = oc.consult("m", "s", "p", api_key="sk-x",
                     transport=lambda *a, **k: (200, null_content_body))
    assert out["fallback"] == "claude"
    assert out["error_kind"] == "parse"
