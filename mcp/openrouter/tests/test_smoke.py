import os

import pytest

import openrouter_client as oc


@pytest.mark.skipif(
    os.environ.get("OPENROUTER_SMOKE") != "1",
    reason="set OPENROUTER_SMOKE=1 (and OPENROUTER_API_KEY) to run the live call",
)
def test_live_cheap_call():
    out = oc.consult(
        "openai/gpt-4o-mini",
        "You reply with exactly one word.",
        "Say the word: ping",
    )
    assert "fallback" not in out, f"live call failed: {out}"
    assert isinstance(out["text"], str) and out["text"].strip()
    assert out["usage"]["completion_tokens"] >= 1
