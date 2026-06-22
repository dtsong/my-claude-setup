"""OpenRouter `consult` primitive — pure, fail-soft, transport-injectable.

Single-shot chat completion against OpenRouter. The HTTP call is isolated
behind a `transport` callable so the core logic is unit-testable with no
network. Every failure returns a structured fallback signal rather than
raising, so callers degrade gracefully to their normal Claude path.
"""

import json
import os
import urllib.request

OPENROUTER_URL = "https://openrouter.ai/api/v1/chat/completions"
DEFAULT_MAX_TOKENS = 1024
DEFAULT_TIMEOUT = 60

ATTRIBUTION = {
    "HTTP-Referer": "https://github.com/danielsong/my-claude-setup",
    "X-Title": "my-claude-setup council",
}


def build_payload(model, system, prompt,
                  max_tokens=DEFAULT_MAX_TOKENS, temperature=None):
    """Build the OpenRouter chat-completions request body."""
    payload = {
        "model": model,
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": prompt},
        ],
        "max_tokens": max_tokens,
    }
    if temperature is not None:
        payload["temperature"] = temperature
    return payload


def build_headers(api_key):
    """Build request headers including bearer auth and attribution."""
    return {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json",
        **ATTRIBUTION,
    }


def parse_success(resp_json):
    """Extract the normalized result from an OpenRouter success body.

    Raises KeyError/IndexError/TypeError on an unexpected shape; the caller
    (`consult`) converts that into a fallback signal.
    """
    text = resp_json["choices"][0]["message"]["content"]
    usage = resp_json.get("usage", {})
    return {
        "text": text,
        "model": resp_json.get("model", ""),
        "usage": {
            "prompt_tokens": usage.get("prompt_tokens", 0),
            "completion_tokens": usage.get("completion_tokens", 0),
        },
    }


def fallback_error(message, *, kind):
    """Structured, non-raising failure signal. Callers fall back to Claude."""
    return {"error": message, "error_kind": kind, "fallback": "claude"}


def urllib_transport(url, headers, payload, timeout):
    """Default transport: POST JSON via stdlib urllib. Returns (status, json)."""
    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(url, data=data, headers=headers, method="POST")
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        body = resp.read().decode("utf-8")
        return resp.status, json.loads(body)


def consult(model, system, prompt,
            max_tokens=DEFAULT_MAX_TOKENS, temperature=None,
            *, api_key=None, transport=urllib_transport, timeout=DEFAULT_TIMEOUT):
    """Single-shot call to an OpenRouter model. Never raises.

    Returns the normalized success dict, or a fallback_error signal on any
    failure (missing key, transport error, HTTP >=400, or bad response shape).
    """
    key = api_key if api_key is not None else os.environ.get("OPENROUTER_API_KEY")
    if not key:
        return fallback_error("OPENROUTER_API_KEY not set", kind="missing_key")

    payload = build_payload(model, system, prompt, max_tokens, temperature)
    headers = build_headers(key)
    try:
        status, resp_json = transport(OPENROUTER_URL, headers, payload, timeout)
    except Exception as exc:  # network / timeout / dns — fail soft
        return fallback_error(f"request failed: {exc}", kind="transport")

    if status >= 400:
        return fallback_error(f"http {status}", kind="http")
    try:
        return parse_success(resp_json)
    except (KeyError, IndexError, TypeError) as exc:
        return fallback_error(f"bad response shape: {exc}", kind="parse")
