---
name: mcs-research-frontier
description: Use when scoping a genuinely open, publishable-flavor problem this repo could advance rather than a bug to fix or a feature to ship, e.g. "could this become a paper", "what's the interesting unsolved part here", "is anyone else doing this", or "what would make this evidence-worthy" for closed-loop skill evolution, heterogeneous multi-model council, contract-gated autonomous execution, config-as-production, or cross-session memory. Not for executing the OpenRouter/model-routing campaign itself (mcs-model-routing-campaign) or for how an idea graduates from hunch to accepted result (mcs-research-methodology).
---

# mcs-research-frontier

## Overview

This repo has working, load-bearing infrastructure (a hardened acceptance gate, a durable skill-eval pipeline, a fail-soft OpenRouter substrate, a symlink-deployed production config, a deliberate no-auto-memory decision) that happens to also be raw material for open problems in agent-harness engineering. This skill is a scoping map, not a build guide: every entry below is labeled `open` or `candidate`, none is proven, and "advance the state of the art" means "produce a falsifiable result no public write-up already has," not "ship a feature."

## When to use and when NOT to

Use when: asking whether something in this repo is research-worthy, not just useful; scoping what evidence a claim of novelty would need; deciding which of several half-built ideas to invest in next; picking a first concrete step for one of the five candidates below.

Do NOT use for: actually executing the model-routing/OpenRouter campaign (`mcs-model-routing-campaign` owns issues #59-#66 and the campaign's phase state); the general hunch-to-accepted-result lifecycle and evidence bar (`mcs-research-methodology`); what counts as evidence for a normal (non-research) change (`mcs-validation-and-qa`); running a diagnostic script (`mcs-diagnostics-and-tooling`); or history of what was tried and reverted (`mcs-failure-archaeology`, read this first: a "new" idea here may already be a documented dead end).

## Ranked candidates (2026-07-02 snapshot)

All SOTA claims are from training knowledge, dated early 2026, and are the author's characterization, not a literature review: treat as `open, owner-unconfirmed` until checked against current papers/products. Full detail (asset, 3 first steps, milestone) for ranks 1-3 is in `references/candidates-top3.md`; ranks 4-5 are in `references/candidates-rank4-5.md`.

| # | Candidate | Status | Asset strength | Why ranked here |
|---|---|---|---|---|
| 1 | Contract-gated autonomous execution | candidate | Strongest: working hook + 3-generation hardening history with SHAs | Only entry with a real, battle-tested implementation today; smallest gap to a falsifiable adversarial result |
| 2 | Closed-loop eval-driven skill evolution | candidate | Strong but disconnected: 5+ pipeline scripts, 135 eval cases, durable registry, none wired together | Every piece exists in this repo already; the loop itself has never run once |
| 3 | Heterogeneous multi-model deliberation w/ egress policy | open | Medium: substrate merged and idle, egress schema designed, harness not built | Real open research question (does persona transfer across vendors survive, at what cost) but most of the hard work is still on paper; execution owned by `mcs-model-routing-campaign` |
| 4 | Config-as-production discipline | candidate, weak novelty | Strong (schema guard shipped, issue #64/PR #71, 2026-07-05) | Real and buildable now, but symlink/schema-guard config-as-code is well-trodden ground elsewhere (dotfile managers, GitOps); mostly a documentation-of-a-good-pattern claim, not a SOTA gap |
| 5 | Cross-session organizational memory vs auto-memory | open, weakest asset | Weakest: exactly 1 handover file exists, no baseline dataset | Directionally interesting, deliberately chosen over the platform default, but nothing has been measured yet: needs instrumentation before it is even a testable hypothesis |

No entries were dropped from the brief's 5-candidate list; none met a bar to add a 6th today (a 6th would need its own asset, not just an idea).

## How to use this skill

1. Pick a row above. Read its full entry in `references/candidates-top3.md` (ranks 1-3) or `references/candidates-rank4-5.md` (ranks 4-5) before doing anything.
2. Re-run the entry's cited commands yourself: this repo is under active concurrent modification and every fact here has a "verified 2026-07-02" timestamp, not a guarantee.
3. Do the "first three steps" in order; step 1 is always "read the existing design/asset," never "start building," because every candidate already has partial work you would otherwise duplicate.
4. Once you have a real result (not a plan), take it to `mcs-research-methodology` for the evidence bar an "accepted result" needs, or to `mcs-model-routing-campaign` if the result is inside that campaign's scope (candidate 3, the heterogeneous-deliberation entry).

## Where ideas here historically came from

Three repeatable origin patterns, each with a citable instance (full narratives: `mcs-failure-archaeology`):

- **Incident postmortem to hardened primitive.** The acceptance-gate's 3-generation fix chain (299a264 to 6bc7c1a to 4bb8bf2 to 605112d) turned a decorative hook into the asset behind candidate 1. Nobody designed a "contract-gated execution" research idea up front; it fell out of fixing the same bug three times and writing down why each fix was still incomplete.
- **Dogfooding pain → deletion or consolidation.** The one-night Fable-5 sweep (8c0cf14..9cee199, 2026-06-10) deleted babysitting directives, duplicate skills, and per-agent model pins because using the repo daily made the dead weight obvious; this is also the origin of the "no cross-vendor model pins" convention candidate 3 relies on.
- **Council session → design doc → PRD → issues.** OpenRouter Phase 1 and the entire candidate-2/3 substrate originated in a `/council` deliberation (`docs/superpowers/specs/2026-06-22-openrouter-integration-design.md`), not an ad hoc idea; today's `claude-config-model-optimization-20260702-0003` session is the same pattern producing candidates 3's schema-guard and candidate 5's handover-vs-auto-memory decision record (design.md:88).

`mcs-research-methodology` owns the general lifecycle (hunch → evidence → accepted); this section only answers "where did this specific idea come from," which matters for judging whether a candidate is a fresh hypothesis or a documented-and-settled question in disguise.

## Gotchas

- **"Asset exists" is not "asset is wired."** Candidate 2's five scripts (`run-evals.sh`, `judge-skill-quality.sh`, `check-regressions.py`, `skill-audit.py`, `registry.json`) all work standalone today; none has ever called another in sequence. Verify with `grep -rn "run-evals\|judge-skill-quality\|check-regressions" pipeline/scripts/*.py pipeline/scripts/*.sh`: the only hits are each script's own file, confirming zero cross-calls.
- **The registry being "durable" (committed) is not the same as "automatic."** `registry.json`'s increment is still a prose instruction to the conductor LLM (`commands/_council-engine.md:672-677`), not a forced write. A future session can silently skip it exactly like every session before 2026-07-02 did.
- **"Egress policy" in design.md is a schema field, not code.** `mcp/openrouter/routing.py` has no `send_allowlist`/ZDR/kill-switch enforcement today; `routed_consult` has zero *production* callers, but it is not caller-less (as of 2026-07-05, `mcp/openrouter/tests/test_routing.py` exercises it directly via dependency-injected fake transports, since commit 4d9694e7). Do not treat candidate 3's design-doc language as a shipped guardrail, and do not cite "zero callers" as if the function were untested.
- **A single handover file is not a dataset.** Candidate 5's milestone needs >=10 sessions of comparable data; as of 2026-07-02 there is exactly 1 file in `memory/`. Treat any rework-reduction claim made before that instrumentation exists as fabricated.
- **`pipeline/evals/` does not exist yet.** Both the 12-case smoke set (F11) and the 38-case golden harness that design.md cites are planned paths, not files on disk (`ls pipeline/evals` fails today). Do not cite either as a working eval suite.
- **Status columns rot.** Issue #64 (settings.json schema guard, feeding candidate 4) went from mid-implementation to merged (PR #71) between authoring and first review, and the whole campaign closed 2026-07-06. Re-run `git log --oneline -5` and `gh issue list --state open` before trusting any status claim here.
- **A "first step" that duplicates existing work is a wasted step.** The mcs-diagnostics-and-tooling skill's `hook-contract-check.sh` tool already does exactly the exit-code-capture probing candidate 3's adversarial harness needs: hand off to that skill for it, do not rewrite it.

## Provenance and maintenance

Last verified: 2026-07-02, against a repo mid-execution of a concurrent `/ship` run (HEAD at verification time: `936322e`). That run has since completed: issues #58-#66 all closed, PR train #67-#74 merged, `main` at `74e34c5` (2026-07-06).

Re-verification commands (run from repo root):

- Current HEAD and open issues: `git log --oneline -5` and `gh issue list --state open --limit 15`.
- Registry telemetry is still committed and current: `git show HEAD:skills/council/registry.json | python3 -c "import json,sys; d=json.load(sys.stdin); print(d['last_updated'])"`.
- Eval-case inventory (9 departments, 15 cases each as of writing): `for f in skills/council/*/eval-cases/trigger-evals.json; do python3 -c "import json;print('$f', len(json.load(open('$f'))))"; done`.
- Pipeline scripts are still disconnected: `grep -rln "run-evals\.sh\|judge-skill-quality\.sh\|check-regressions\.py" pipeline/scripts/*.py pipeline/scripts/*.sh`.
- `routed_consult` still has zero *production* callers (test-only callers in `mcp/openrouter/tests/test_routing.py` are expected and do not count), as of 2026-07-05: `grep -rn "routed_consult(" --include=*.py . | grep -v mcp/openrouter/routing.py | grep -v mcp/openrouter/tests/`.
- `pipeline/evals/` still absent: `ls pipeline/evals 2>&1`.
- Handover file count: `ls -t memory/HANDOVER-*.md | wc -l`.
- Settings schema guard merge status: `git log --oneline -3 -- pipeline/config/settings.schema.json pipeline/hooks/check_settings.py` and `git branch --show-current`.
