#!/usr/bin/env python3
"""Flag stale model IDs in skills/council/model-routing.json (issue #62, AC-011).

Fetches the public OpenRouter catalog (no API key required) and verifies every
model ID referenced in the routing table still exists. Exit 0 when all IDs are
live, exit 1 listing any stale IDs. Run monthly and before enabling any
routed_consult caller; candidate for a scheduled routine once telemetry lands.
"""

import json
import sys
import urllib.request

from routing import DEFAULT_ROUTING_PATH, load_routing

CATALOG_URL = "https://openrouter.ai/api/v1/models"
SENTINEL = "claude"  # in-family sentinel, never an OpenRouter ID


def referenced_ids(routing):
    ids = set(routing.get("tasks", {}).values())
    ids.update(routing.get("lenses", {}).values())
    ids.discard(SENTINEL)
    return ids


def live_ids(url=CATALOG_URL, timeout=20):
    with urllib.request.urlopen(url, timeout=timeout) as resp:
        catalog = json.load(resp)
    return {m["id"] for m in catalog.get("data", [])}


def main():
    routing = load_routing()
    if not routing:
        print(f"check_models: routing table missing or invalid at {DEFAULT_ROUTING_PATH}", file=sys.stderr)
        return 1
    wanted = referenced_ids(routing)
    if not wanted:
        print("check_models: no OpenRouter IDs referenced; nothing to verify")
        return 0
    try:
        live = live_ids()
    except Exception as exc:  # network failure is not staleness; report and fail loud
        print(f"check_models: could not fetch catalog ({exc}); IDs unverified", file=sys.stderr)
        return 1
    stale = sorted(wanted - live)
    if stale:
        print("check_models: STALE model IDs (would 404 at request time):", file=sys.stderr)
        for mid in stale:
            print(f"  - {mid}", file=sys.stderr)
        return 1
    print(f"check_models: all {len(wanted)} referenced IDs are live ({len(live)} models in catalog)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
