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
