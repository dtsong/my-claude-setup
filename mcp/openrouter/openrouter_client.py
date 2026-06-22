"""OpenRouter `consult` primitive — pure, fail-soft, transport-injectable.

Single-shot chat completion against OpenRouter. The HTTP call is isolated
behind a `transport` callable so the core logic is unit-testable with no
network. Every failure returns a structured fallback signal rather than
raising, so callers degrade gracefully to their normal Claude path.
"""

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
