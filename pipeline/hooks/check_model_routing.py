#!/usr/bin/env python3
"""Pre-commit guard for skills/council/model-routing.json (issue #63, AC-014).

The routing table is the single source of truth for model selection; this hook
keeps it structurally sound:

  R1  spawn_sites values are tier aliases (opus|sonnet|haiku|fable), 'inherit',
      or 'openrouter'; pinned claude-* IDs in a spawn-site slot are forbidden
  R2  every spawn site has an entry for every profile (max-plan, api-billed)
  R3  any spawn site routing to an external destination (openrouter) requires
      a matching egress_policy entry with send_allowlist, zdr, no_train,
      audit_actual_model, kill_switch
  R4  every tier alias referenced by a spawn site exists in tiers, and tiers
      carry a concrete ID per profile (the ONE sanctioned home for claude-* IDs)
  R5  legacy keys (tasks/lenses/defaults) keep the shapes mcp/openrouter/routing.py
      expects, and defaults.fallback stays 'claude' (fail-soft invariant)

Exit 0 on pass, 1 with findings on stderr.
"""

import json
import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DEFAULT_TARGET = os.path.join(REPO, "skills", "council", "model-routing.json")

PROFILES = ("max-plan", "api-billed")
TIER_ALIASES = {"opus", "sonnet", "haiku", "fable"}
SPECIAL = {"inherit", "openrouter"}
EGRESS_REQUIRED = ("send_allowlist", "zdr", "no_train", "audit_actual_model", "kill_switch")


EFFORT_VALUES = {"low", "medium", "high", "max", "inherit"}


def _dict_section(routing, key, errors):
    value = routing.get(key, {})
    if not isinstance(value, dict):
        errors.append(f"{key}: expected object, got {type(value).__name__}")
        return {}
    return value


def check(routing):
    errors = []
    tiers = _dict_section(routing, "tiers", errors)
    spawn_sites = _dict_section(routing, "spawn_sites", errors)
    egress = _dict_section(routing, "egress_policy", errors)
    defaults = _dict_section(routing, "defaults", errors)

    if not spawn_sites:
        errors.append("spawn_sites: missing or empty (the table is the single source of truth)")

    referenced_aliases = set()
    external_used = False
    for site, entry in spawn_sites.items():
        if not isinstance(entry, dict):
            errors.append(f"R2 spawn_sites.{site}: expected object with per-profile entries")
            continue
        for profile in PROFILES:
            value = entry.get(profile)
            if value is None:
                errors.append(f"R2 spawn_sites.{site}: missing entry for profile '{profile}'")
                continue
            if not isinstance(value, str):
                errors.append(f"R1 spawn_sites.{site}.{profile}: expected string, got {type(value).__name__}")
                continue
            if value.startswith("claude-"):
                errors.append(f"R1 spawn_sites.{site}.{profile}: pinned ID '{value}' forbidden; concrete IDs live only in tiers")
            elif value in TIER_ALIASES:
                referenced_aliases.add(value)
            elif value == "openrouter":
                external_used = True
            elif value != "inherit":
                errors.append(f"R1 spawn_sites.{site}.{profile}: '{value}' is not a tier alias, 'inherit', or 'openrouter'")
        effort = entry.get("effort")
        if effort not in EFFORT_VALUES:
            errors.append(f"R6 spawn_sites.{site}: effort must be one of {sorted(EFFORT_VALUES)}, got {effort!r}")

    if external_used:
        policy = egress.get("openrouter")
        if not isinstance(policy, dict):
            errors.append("R3 egress_policy.openrouter: required (a spawn site routes to openrouter) but missing")
        else:
            for key in EGRESS_REQUIRED:
                if key not in policy:
                    errors.append(f"R3 egress_policy.openrouter: missing required field '{key}'")

    for alias in sorted(referenced_aliases):
        tier = tiers.get(alias)
        if not isinstance(tier, dict):
            errors.append(f"R4 tiers.{alias}: referenced by a spawn site but missing from tiers")
            continue
        for profile in PROFILES:
            if not isinstance(tier.get(profile), str) or not tier.get(profile):
                errors.append(f"R4 tiers.{alias}.{profile}: concrete model ID required")

    if defaults.get("fallback") != "claude":
        errors.append("R5 defaults.fallback: must stay 'claude' (fail-soft invariant for routing.py)")
    for legacy in ("tasks", "lenses"):
        if legacy in routing and not isinstance(routing[legacy], dict):
            errors.append(f"R5 {legacy}: expected object (mcp/openrouter/routing.py contract)")
    return errors


def check_file(path):
    try:
        routing = json.load(open(path, encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [f"{path}: unreadable or invalid JSON ({exc})"]
    return [f"{path}: {e}" for e in check(routing)]


def main(argv):
    targets = [a for a in argv if a.endswith(".json")] or [DEFAULT_TARGET]
    findings = []
    for t in targets:
        findings.extend(check_file(t))
    if findings:
        print("check_model_routing: routing table failed validation:", file=sys.stderr)
        for f in findings:
            print(f"  - {f}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
