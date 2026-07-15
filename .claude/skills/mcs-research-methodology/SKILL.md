---
name: mcs-research-methodology
description: Use when turning a hunch into a shipped change here, deciding if a claim survives adversarial refutation before trusting it, writing a predicted number/exit-code/pass-rate before running an experiment or eval, tracing an idea through council deliberation, PRD non-goals, a numbered acceptance contract, gated /ship or /looper execution, to verified or retired, or picking settings.local.json as the experiment lane instead of settings.json. Not for measurement techniques (mcs-analysis-toolkit) or formal evidence tiers and AC mechanics (mcs-validation-and-qa).
---

# mcs-research-methodology

## Overview

This repo turns a hunch into a merged change through one discipline: a claim counts once it survives adversarial refutation and its predicted number matches the observed one. The council Skeptic lens and the local review loop `/ship` invokes are the two in-repo adversaries; skipping either has shipped decorative enforcement before (the acceptance-gate hook was rewritten three times before it actually blocked anything). Read this before trusting a hunch, writing a PRD non-goal, or flipping an acceptance criterion to verified.

## When to use and when NOT to

Use when: deciding if a hypothesis is ready to test or ship, writing an acceptance criterion, choosing where an experiment should live before it earns `settings.json`, or explaining why an idea was retired instead of dropped silently.

Route instead to:
- **mcs-analysis-toolkit**: the measurement recipes (token accounting, trigger reliability, cost estimation) producing the numbers this skill asks you to predict.
- **mcs-validation-and-qa**: formal evidence tiers, AC mechanics, hard vs warn pre-commit tiers, CI's actual scope.
- **mcs-failure-archaeology**: full incident timelines beyond the illustrative citations here.
- **mcs-change-control**: commit/PR conventions and non-negotiables once an idea is ready to land.

## The evidence bar

One mechanism must explain every observation, negatives included, and survive an adversary trying to break it. Two adversaries live here:

| Instrument | Catches | Evidence |
|---|---|---|
| Council Skeptic (`agents/council-skeptic.md`) | "What if this isn't true," on every claim | design.md's "registry works" vs "broken instrument" tension: Scout/Operator retracted once Skeptic/Craftsman showed 0/67 committed uses, all nonzero counts session-local |
| `/ship`'s review loop (`commands/ship.md` Steps 8-9, `--max-review-cycles`, default 3) | Critical/Important findings block merge | `898174d`: pre-merge review on the "shipped" OpenRouter branch found `urlopen` misclassifying HTTP errors and a null-content crash, both fixed before merge |

A mechanism explaining only the positive case is not done. "The registry isn't used" fails to explain why nonzero counts appear at all; "counters are session-local, never persist" explains both the zero baseline and the spikes. Prefer the mechanism that survives the negative.

Cost of skipping this: `hooks/acceptance-gate.sh` shipped broken three times over four months (`299a264` create, `6bc7c1a`/`4bb8bf2` partial fixes) before `605112d` verified both the block path (`exit 2`, stderr) and the happy path. Each earlier commit was accepted without adversarially testing the thing it claimed to fix.

## Predict before you run

Write the expected number, exit code, or output before the experiment. A prediction that can't be falsified isn't a hypothesis.

**Hook exit code.** Before running `hooks/telemetry-dispatch.sh` with a missing target: predict exit 0, a stderr warning, nothing on stdout (its own comment says it never exits 2, normalizes any child failure to exit 1). Verified live: `CLAUDE_TELEMETRY_HOOK=/nonexistent bash hooks/telemetry-dispatch.sh` warns on stderr and exits `0`, as predicted. The tempting wrong prediction, exit 1 because "the target is missing," conflates the dispatcher's exit with the child's; that exact confusion is what `4bb8bf2`/`605112d` had to fix in `acceptance-gate.sh`.

**Eval pass rate.** `pipeline/specs/SKILL-GOVERNANCE-SPEC.md` §7.4: run evals at current length, record pass rate, refactor to target, re-run, keep the shorter version only if pass rate holds, else restore and document the override with the data. This repo's contract mirrors that outside skill budgets: AC-012's evidence cell was a predicted string ("OpenRouter pytest suite passes with new IDs") that reproduces exactly: `python3 -m pytest mcp/openrouter/tests/ -q` → `31 passed, 1 skipped`.

## The idea lifecycle

| Stage | Artifact | Exemplar |
|---|---|---|
| Hunch | GitHub issue, or nothing yet | #53, acceptance-gate mis-wired |
| Council deliberation | `design.md`: Tension Resolutions + Decision Log tables | this session: 7 tension rows, 7 decision rows |
| PRD non-goals discipline | `prd.md` Non-Goals section | "No live model flips... gated by F11 smoke eval (12-case); 38-case harness gates Phase 2," both v1.1 |
| Acceptance contract | `acceptance-contract.md`, numbered `AC-NNN` rows | 26 ACs, 15/26 verified as of 2026-07-02 |
| Gated execution | `/ship`'s queue in `.claude/ship-state.md`; each issue via `/looper` | US-001..US-004 (#59-#62), merged only after 0 Critical/0 Important |
| Verification | AC row flips `pending` to `verified` with a reproducible Evidence cell | AC-012's `31 passed, 1 skipped`, above |
| Adoption or retirement | merged PR + docs, or a deletion commit stating what and why | adoption: `docs/model-routing.md` (#60); retirement below |

Retirement is not silence. `16833bd` ("remove redundant skills") names each deleted skill and its reason; `12c34df` ("remove academy theme") states the counterfactual (38 to 21 agents, no functionality lost). A deletion commit body is what keeps a battle settled: a future session can `git log --grep <name>` and get the original reasoning instead of re-litigating from zero. Full walkthrough: `references/idea-lifecycle-ledger.md`.

## Experiment lanes

`settings.json` is live production (symlinked to `~/.claude/settings.json`; a merge deploys instantly), so nothing experimental lands there directly. Issue #61 (US-003, merged PR #69) formalized the local lane: `.claude/settings.local.json`, gitignored, documented in `docs/model-routing.md`'s "Experiment Lane" section. Rule: an experiment graduates to `settings.json` only via a reviewed PR; anything sitting local past two weeks is promoted or deleted. Same discipline for `${VAR}` env-flag passthrough (e.g. `OPENROUTER_API_KEY`): declared once, gated behind a feature with zero live callers today, never a silent default.

## Where good ideas came from (ranked by hit rate)

| Source | Example |
|---|---|
| 1. Dogfooding pain | `acceptance-gate.sh` (`299a264`): unenforced plans kept "completing"; handover system (`8a56757`): knowledge evaporated across compactions |
| 2. Incident postmortem to doctrine | `#53`'s misdiagnosis, fixed in `605112d`, generalized into fail-soft doctrine (`3e99a66` `consult` never raises; dispatcher never exits 2) |
| 3. Upstream adoption, divergence recorded | `9cee199` adopted `agentic-council` v1.2.0, documented what stayed local (roster, `DEPARTMENT.md` layout, `registry.json`) |
| 4. Deliberate deletion sweeps | `16833bd`, `12c34df`: both cut scope with a rationale in the commit body, not a silent `git rm` |

Where time was lost: enforcement built and never wired (`/careful`, `/freeze`: zero `PreToolUse` registration); a private-repo hard dependency with no existence check, breaking every clone until #59; specs documenting CI stages `validate.yml` has never run. Full ledger: `references/idea-lifecycle-ledger.md`.

## Anti-patterns

- **Success-by-eyeball.** WRONG: "looks right, ship it." RIGHT: an exit code or a literal Evidence cell, captured verbatim, as every AC row in `acceptance-contract.md` does.
- **Instrument trust without a write-path audit.** WRONG: citing `registry.json` nonzero counts as "the skill gets used." RIGHT: check whether counts persist across sessions or only appear when the current session touches the file (evidence-bar table above).
- **"Refs" instead of "Fixes."** WRONG: a commit resolving a bug says "Refs #NN"; the issue stays open forever as a zombie. `605112d` fixed `#53`, which is still OPEN today because the commit says "Refs," not "Fixes." RIGHT: "Fixes #NN" for a complete resolution.
- **Enforcement theater.** WRONG: trusting a spec claiming a hook exists (`check_security.py`, `check_triggers.py`, absent from `pipeline/hooks/`) or a command claiming protection (`/careful`, `/freeze`, no `PreToolUse` entry in `settings.json`). RIGHT: grep for the actual registration before trusting the doc.

## Gotchas

- WRONG: treating "merged" as the finish line. RIGHT: the AC row must flip to `verified` with an Evidence cell; `ship-state.md` tracks PR merges and `acceptance-contract.md` tracks proof (two different counters, don't conflate them).
- WRONG: assuming a `design.md` Decision Log or Tension Resolutions row is a final compromise. RIGHT: some rows record one side retracting under evidence (Reasoning column tells which); rows still face PRD/AC stages, where this session's F3 tension was overturned by its own inconsistency before drafting.
- WRONG: predicting "it will probably pass." RIGHT: predict the literal string or exit code (AC-012's evidence cell); a vague prediction can't be falsified.
- WRONG: trusting an open GitHub issue count as "still live." RIGHT: #3, #16, #26 have had zero activity since February 2026; check `gh issue view <n> --json state,updatedAt` first.
- WRONG: assuming a type-check or lint gate exists. RIGHT: state explicitly when none does (CLAUDE.md directive 2); it's pre-commit (`^skills/`-scoped hooks only) plus `pytest`, and CI checks shell syntax/JSON validity/installer smoke/secrets only.

## Provenance and maintenance

Last verified 2026-07-02, branch `feat/64-settings-schema-guard` at commit `8b36965` (US-001..US-004 then merged via PRs #67-#70; the full campaign has since completed, 2026-07-06, PR train #67-#74, contract 26/26). Treat every SHA and AC count here as a snapshot, not a target, and re-run the commands below.

Re-verification commands:
- HEAD and issue queue: `git log --oneline -5`, `sed -n '1,15p' .claude/ship-state.md`
- AC verification count: `C=.claude/council/sessions/claude-config-model-optimization-20260702-0003/acceptance-contract.md; grep -c '\*\*Status:\*\* verified' $C; grep -c '^#### AC-' $C` (15/26 as of this writing)
- Zombie-issue check: `gh issue list --state open --json number,title,updatedAt`
- Dispatcher contract: `CLAUDE_TELEMETRY_HOOK=/nonexistent bash hooks/telemetry-dispatch.sh; echo $?` (expect `0` + stderr warning)
- OpenRouter test reproduction: `python3 -m pytest mcp/openrouter/tests/ -q`
- Careful/freeze non-wiring: `grep -c 'careful\|freeze' settings.json` (expect `0`)
- §7.4 still at that number: `grep -n '7.4 Using Evals' pipeline/specs/SKILL-GOVERNANCE-SPEC.md`
- Full ledger and worked walkthrough: `references/idea-lifecycle-ledger.md`
