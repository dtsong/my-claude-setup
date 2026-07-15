# my-claude-setup Project Skill Library

Sixteen project-scoped skills that let a zero-context mid-level engineer or Sonnet-class Claude session debug, extend, validate, and advance this repo unaided. Authored 2026-07-02 by parallel Sonnet 5 agents from a full-repo discovery sweep; reviewed and corrected 2026-07-05 (factual, doctrine, usability passes). Volatile facts inside each skill carry a date stamp and a one-line re-verification command in its "Provenance and maintenance" section: trust the command, not the stamp.

## How to use this library

Load exactly one skill for the task at hand; each description ends with a negative boundary naming the sibling to use instead. History has one home (mcs-failure-archaeology), live triage another (mcs-debugging-playbook), measurement another (mcs-diagnostics-and-tooling); cross-references, not copies.

## Inventory

| Skill | One-line scope |
|---|---|
| mcs-change-control | How changes are classified, gated, and merged here; the non-negotiables (symlinked settings.json is production, never --no-verify, no history rewrite without owner, tier aliases only) with the incident behind each |
| mcs-debugging-playbook | Symptom-to-cause triage for this repo's failure modes: hooks that silently do not block, gate false positives, workflow args errors, MCP venv failures, with a discriminating experiment per trap |
| mcs-failure-archaeology | The chronicle: acceptance-gate saga, Fable-5 sweep, academy removal, branch graveyard, OpenRouter Phase 1, registry telemetry era, privacy exposure; settled battles nobody should re-fight |
| mcs-architecture-contract | Load-bearing design decisions and why; invariants with enforcement status (hook-backed vs prose-only); known-weak points stated plainly |
| mcs-claude-code-platform | Claude Code platform mechanics as wired here: hook stdin-JSON contract and blocking semantics, settings layering, skill discovery, MCP registration, Workflow/agent-teams preflight |
| mcs-config-and-flags | Catalog of every configuration axis with current value, status (production/experimental/parked), guard, and re-verification one-liner; checklist for adding an axis |
| mcs-build-and-env | Bare machine to working environment: real prerequisites, install.sh anatomy and traps, post-install bootstrap (pre-commit, openrouter venv), health-check commands |
| mcs-run-and-operate | Day-to-day operation: council modes and profiles, session artifacts, ship/looper/ralf execution paths, handover protocol, in-flight-run etiquette |
| mcs-diagnostics-and-tooling | Measure instead of eyeball: every diagnostic script with invocation, interpretation, and thresholds; ships hook-contract-check.sh and doc-drift-check.sh |
| mcs-validation-and-qa | What counts as evidence: the honest verification surface, acceptance-contract discipline, eval tiers 1-3, the tested-vs-merely-present inventory, how to add tests and evals |
| mcs-docs-of-record | The doc map, authority ranking for conflicts, the current drift fix-queue, house style, handover/design templates |
| mcs-external-positioning | What may be claimed publicly and what must be true first: novelty ranking, v1.0 ledger, licensing/attribution, privacy exposure options (owner-only decisions) |
| mcs-model-routing-campaign | The executable, decision-gated campaign for the hardest live problem: model-routing unification (US-001..008) then OpenRouter multi-model lenses behind explicit gates |
| mcs-analysis-toolkit | First-principles proof recipes: token math, trigger-reliability analysis, hook live-fire, instrument-trust audits, refute-first review, each with a worked example from repo history |
| mcs-research-frontier | Open problems where this repo could advance state of the art, each with the asset, first three steps in-repo, and a falsifiable milestone; all labeled open/candidate |
| mcs-research-methodology | Hunch to accepted result: the evidence bar, predict-numbers-first, the council-to-contract-to-gated-ship idea lifecycle, experiment lanes, historical sources of good ideas |

## Governance note

These skills live under `.claude/skills/`, which is OUTSIDE the pre-commit governance globs (`^skills/`) as of 2026-07-05. They were hand-validated against `pipeline/hooks/check_frontmatter.py`, `check_references.py`, `check_isolation.py`, and `check_context_load.py` at review time. If this library is adopted long-term, extend `.pre-commit-config.yaml` globs to cover `^\.claude/skills/` (owner decision).

Re-verify library integrity: `for f in .claude/skills/mcs-*/SKILL.md; do python3 pipeline/hooks/check_frontmatter.py "$f" || echo "FAIL $f"; done`
