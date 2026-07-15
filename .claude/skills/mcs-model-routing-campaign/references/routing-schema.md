# Phase 2 detail: unified routing schema (US-005, issue #63)

## The three-surfaces problem this kills

As of 2026-07-02, "which model runs where" is answered by three disconnected files with three vocabularies, and nothing cross-checks them:

1. `settings.json` `.model` (a single tier alias for the session default: `opus`, `sonnet`, `fable`, `haiku`). Fixed by US-002/#60; currently `opus`.
2. `commands/_council-engine.md`'s "Cost Profiles & Model Routing" prose table (lines ~97-105): per-spawn-site tier aliases keyed by council profile (`lean`/`balanced`/`max`). Hand-maintained prose, not machine-readable.
3. `skills/council/model-routing.json`: OpenRouter vendor-model IDs keyed by task class (`classification`, `scout-research`, `scoring`) and, separately, an empty `lenses: {}` stub for Phase 2.

The same design fact (which model answers at a given spawn site) can drift independently in all three places, and has: the `[1m]` pin incident (US-002) was exactly this kind of drift, caught only because someone diffed `settings.json` against the engine's own governance rule. US-005's job is to collapse these into one file that the other two either read from or are validated against, not to add a fourth surface.

## Target schema (design.md, ships as this shape)

```json
{
  "tiers": {
    "opus": "<claude tier alias>",
    "sonnet": "<claude tier alias>",
    "fable": "<claude tier alias>",
    "haiku": "<claude tier alias>"
  },
  "profiles": {
    "max-plan": { "cheap_task_route": "haiku-in-family" },
    "api-billed": { "cheap_task_route": "openrouter-or-haiku" }
  },
  "spawn_sites": {
    "session_default": "<alias>",
    "council.lean": "<alias>",
    "council.balanced": "<alias>",
    "council.max": "<alias>",
    "brainstorm": "<alias>",
    "challenge": "<alias>",
    "audit": "<alias>",
    "ship_implement": "<alias>",
    "ship_review": "<alias>",
    "looper": "<alias>",
    "subagent": "<alias>",
    "routed_consult": "<alias-or-openrouter-id>",
    "cheap_tasks": "<alias-or-openrouter-id>"
  },
  "egress_policy": {
    "<external_dest, e.g. openrouter>": {
      "send_allowlist": ["<field names permitted to leave the process>"],
      "zdr": true,
      "no_train": true,
      "audit_actual_model": true,
      "kill_switch": true
    }
  },
  "tasks": { "...": "existing Pattern B task-class map, unchanged" },
  "lenses": { "...": "existing Pattern A lens map, unchanged, still empty" },
  "defaults": { "lens": "claude", "fallback": "claude" }
}
```

`tiers`/`profiles`/`spawn_sites`/`egress_policy` are additive to the existing `tasks`/`lenses`/`defaults` block already shipped in Phase 1 (OpenRouter): this is an extension, not a rewrite. The 11-entry `spawn_sites` list above is the full acceptance-criterion enumeration from `prd.md` AC-013; a schema missing any one of these sites fails validation.

## Validator (AC-014): what it must reject

The AC-014 test (`test_ac_014_routing_validator` in `test-stubs/test_acceptance.py`, currently a `NotImplementedError` stub) must fail validation on each of these fixture cases independently:

1. A pinned `claude-*` ID (e.g. `claude-fable-5-20260615`) sitting in a `tiers` or `spawn_sites` value: only tier aliases are legal there.
2. A `spawn_sites` entry missing a value for one of the two `profiles` (max-plan vs api-billed): every site must resolve on both billing profiles.
3. An entry under `egress_policy`'s parent map (any external, non-Claude destination referenced anywhere in the file) that has no corresponding `egress_policy.<dest>` block, or one missing any of the five required keys (`send_allowlist`, `zdr`, `no_train`, `audit_actual_model`, `kill_switch`).

"The correct thing is the only thing that validates" (design.md's own phrasing): do not write a validator that merely warns on these cases; AC-014 requires hard failure.

## Definition of done, in numbers

- AC-013: schema-shape test passes: file parses and contains all four new top-level keys plus the pre-existing three.
- AC-014: validator rejects all three negative-case families above; zero false negatives on the fixtures the reviewer supplies.
- AC-015: `docs/model-routing.md` renders the full spawn-site × profile table (11 sites × 2 profiles = 22 cells minimum) with the Max/API escalation rule already documented under AC-006.
- AC-016: `commands/_council-engine.md`'s cost-profile section references `model-routing.json` as source of truth: `grep -c model-routing.json commands/_council-engine.md` returns `>= 1`.
- Campaign-level metric this phase feeds: "spawn sites with documented routing → 100% on both accounts" (design.md success metrics).

## What Phase 2 explicitly does NOT do

Ships as a design doc + validator only. The machine-readable loader that makes `settings.json` and the engine actually *read* this file at runtime, and the first live model change driven by it, are both gated behind the 12-case smoke eval (F11, v1.1): see `references/openrouter-phase2-gate.md`. Do not wire a live spawn site to read this file's `spawn_sites` block until that gate opens; US-005 on its own changes no live model dispatch.
