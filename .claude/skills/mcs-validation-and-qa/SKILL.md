---
name: mcs-validation-and-qa
description: Use when deciding what counts as evidence in this repo, adding a pytest to mcp/openrouter, writing eval-cases/trigger-evals.json for a council department, flipping an acceptance-contract AC row to verified, running run-evals.sh or judge-skill-quality.sh, or someone claims a change "looks right" without a number or exit code. Covers hard vs warn pre-commit tiers, CI's actual (narrow) scope, and the acceptance-gate block mechanics. Not for running diagnostic tools themselves (mcs-diagnostics-and-tooling) or the history of why an enforcement gap exists (mcs-failure-archaeology).
---

# mcs-validation-and-qa

## Overview

Evidence here is a passing command with a captured exit code, or a flipped
and cited acceptance-contract row, never a visual check. Two things are true
at once: strong contract and eval machinery exists, and its live enforcement
surface is narrower than the specs imply (no CI governance, 0 required
reviews). Both facts must inform every claim of "done."

## When to use, and when NOT to

Use this to decide what evidence a change needs, to add a test/eval/AC, or
to interpret a pre-commit/CI/gate result correctly.

Route instead to:
- **mcs-diagnostics-and-tooling**: how to run and interpret a specific diagnostic script (this skill only says which command counts as evidence).
- **mcs-failure-archaeology**: why an enforcement gap exists, what was tried and reverted (the registry-telemetry saga in full).
- **mcs-change-control**: commit/PR conventions and non-negotiables (assumed here, not re-taught).
- **mcs-architecture-contract**: why the acceptance-gate hook is shaped PreToolUse/exit-2 (design rationale, not usage).

## The verification surface, honestly stated (2026-07-05)

| Layer | Scope | Notes |
|---|---|---|
| pre-commit hooks | skill-governance scoped to `^skills/.*\.md$`; two more hard hooks sit outside it | Skill-governance: 4 hard (`check_frontmatter`, `check_references`, `check_isolation`, `check_context_load`) + 1 hard commit-msg stage + 2 warn (`check_token_budget`, `check_prose`, always exit 0). As of 2026-07-05 (`82292e1`, US-005/US-006): `model-routing` (hard, `^skills/council/model-routing\.json$`) and `settings-schema` (hard, `^settings\.json$`) also exist. `.claude/` is still outside every glob: never governance-checked. |
| CI (`validate.yml`) | repo-wide | `bash -n` on `install.sh`/`hooks/*.sh`/`scripts/*.sh`, `python3 -m json.tool` on `settings.json`/`hooks.json`, installer smoke test, gitleaks. Zero governance hooks, zero pytest. |
| Branch protection (main) | pull requests | Required checks: `validation (ubuntu-latest)`, `validation (macos-latest)`, `secret-scan`. 0 required approving reviews. `pre-commit run --all-files` is never re-run by CI; `git commit --no-verify` bypasses it entirely. |
| pytest | `mcp/openrouter/` + session `test-stubs/` | 32 tests in `mcp/openrouter/tests/`, plus `test_acceptance.py` per council session. Real, runnable, not wired into CI. |
| Type-check | none | Bash/python/markdown repo, no `tsc`/`eslint` surface. State that explicitly (owner CLAUDE.md directive 2) rather than run or claim one. |

Run the actual local gate:

```bash
pre-commit run --all-files
python3 -m pytest mcp/openrouter/tests/ -q     # 31 passed, 1 skipped (live call, network-gated)
```

`pre-commit run --all-files` only sees git-tracked files. `skills/soc-security`,
`skills/resume-tailor`, `skills/ece` are gitignored local symlinks (this
machine only); running a hook directly against them still exits 1, but that
can never block a commit here since the path is never staged.

## Acceptance-contract discipline

Format (`commands/_council-engine.md:1038`, live example: the active council
session's `acceptance-contract.md`): a Quality Gates table, per-AC blocks
(`Method`, `Test`, `Status`, `Evidence`, `Verified-by`), then a
`## Verification Summary` table the gate hook actually parses, ending
`Progress: N/M verified`. Status is exactly one of `pending`, `verified`,
`failed`, `pending-manual`. BDD stubs generate per AC into `test-stubs/`,
each raising `Not implemented, AC-NNN pending` so the suite starts RED.

**How to verify an AC properly:**
1. Run the exact command in the AC's `Test:` field.
2. Only on a real pass, flip `Status` in both the detail block and the
   summary table (the gate hook reads only the summary; a mismatched detail
   block is a lie left in the file).
3. Fill `Evidence` with what ran and its result, not a description of intent.
   Fill `Verified-by` with the issue/PR that did it.
4. Never hand-edit a row to `verified` without a run. The discipline is
   entirely on you; nothing checks whether the row is true.
5. Adding a new AC to a `locked` contract is a scope change to a negotiated
   agreement: treat it as needing owner sign-off first (inferred,
   owner-unconfirmed, no script enforces this).

**Gate mechanics** (`hooks/acceptance-gate.sh`, PreToolUse on `TaskUpdate`):
fires only when `tool_input.status == "completed"`, selects the
most-recently-modified contract across the known session/PRD locations,
skips one untouched for `ACCEPTANCE_GATE_STALE_HOURS` (default 72h), counts
`| pending |` plus `| failed |` rows, and if that sum is nonzero, denies with
exit 2 and a stderr list of unverified criteria. `pending-manual` never
blocks. It gates only `TaskUpdate -> completed`, not `git commit` or `gh pr
merge`.

## Eval tiers and trigger evals

| Tier | Method | Cost | When |
|---|---|---|---|
| 1 | pre-commit hooks (static) | free | every commit |
| 2 | `claude -p` execution of eval cases against Must-Pass criteria | paid API | before shipping |
| 3 | LLM-as-judge: Clarity/Completeness/Actionability, 1-5 each | paid API | before shipping |

Trigger-eval minimum for a skill's `eval-cases/trigger-evals.json`: 5
positive cases (should activate) plus 3 negative cases (should not, with
`expected_skill: null` and the correct routing target noted). As of
2026-07-02, exactly 9 council departments carry trigger-evals.json:
`alchemist, architect, cipher, forge, guardian, oracle, prover, skeptic,
warden`.

```bash
pipeline/scripts/run-evals.sh --tier 2 --targets <skill> --model sonnet   # or --tier all / --diff
pipeline/scripts/judge-skill-quality.sh --targets <skill>                 # --diff for changed-only
```

Both shell out to the `claude` CLI, cost real API spend per run, and write
results to `eval-results/tier2-<timestamp>/results.jsonl` or
`eval-results/judge-<timestamp>/results.jsonl`. Read the JSONL; do not judge
by terminal scroll. Per governance spec 7.4, budget disputes are settled
empirically: run evals at current length, refactor to target, run again, and
keep the shorter version only if the pass rate holds. A shorter skill that
fails more eval cases is a regression, not a win.

## How to add evidence

Full recipes, conventions, and gotchas: `references/adding-evidence.md`.
Summary: a pytest to `mcp/openrouter/tests/` imports the module directly
(`conftest.py` puts `mcp/openrouter/` on `sys.path`), stays network-free by
default, gating any live call behind
`@pytest.mark.skipif(os.environ.get("X") != "1")`. An eval case is 5-7 cases
per skill with Must Pass/Should Pass/Bonus tiers, plus the trigger-eval
minimums above. A new pre-commit validator goes in `pipeline/hooks/`, wires
into `.pre-commit-config.yaml` with the right `files:` glob and tier, and
must land in `.github/workflows/validate.yml` too, given 0 required reviews
and universal `--no-verify` bypass; none of the 6 skill-governance hooks do
this today (owner-unconfirmed whether that gap is accepted).

## The golden and certified inventory

Full table (component, evidence type, re-run command):
`references/inventory.md`. Headline numbers, verified 2026-07-06:
`mcp/openrouter/tests/` = 32 tests (31 pass, 1 skipped without
`OPENROUTER_SMOKE=1`; `test_check_models.py` added by PR #70); the
config-optimization session's `test_acceptance.py` = 12 passed, zero
remaining stubs; that session's acceptance contract closed at 26/26
verified (2026-07-06).

## Acceptance-threshold discipline

Success is always a number or an exit code: `pytest -q` status, a `grep -c`
count, a `jq` equality check, the contract's `Progress: N/M` line. Never "ran
it and it looked right." The cautionary example lives in this repo:
`skills/council/registry.json` usage counters were nearly used to justify
pruning council skills on 0/67 committed uses, because every nonzero count
was uncommitted session-local noise that `git checkout .` would have erased.
The instrument was correctly distrusted only because someone ran `git show
HEAD:<path>` instead of `cat <path>`. Treat any counter or telemetry file as
untrustworthy until its number survives that check.

## Gotchas

- A clean `pre-commit run --all-files` says nothing about `skills/soc-security/`,
  `skills/resume-tailor/`, `skills/ece/`: gitignored symlinks excluded from
  every check, while still failing `check_context_load.py`/`check_isolation.py`
  run directly.
- Suite ceiling is contested in docs, not enforcement: `pipeline/config/budgets.json`
  and `_utils.py` use 5,500 tokens; root `CLAUDE.md:57` says 5,000, a stale
  doc, not a second live rule.
- `check_token_budget.py` and `check_prose.py` always exit 0. "Pre-commit
  passed" is not "no budget or prose issues": read the WARNING/INFO lines.
- CI checks JSON and shell syntax only. A PR can merge with every governance
  hook broken and zero pytest run, as long as `settings.json`/`hooks.json`
  parse and the installer smoke test passes.
- The acceptance gate fires only on `TaskUpdate -> completed`. Marking work
  done in a commit message or in prose is not gated at all.
- A `Verified-by` field citing a closed issue/PR is only real evidence if
  that issue/PR's own test run is inspectable; trace it back once instead of
  trusting the URL.
- `is_excluded()` in `pipeline/hooks/_utils.py` skips path segments named
  `pipeline`, `eval-cases`, `node_modules`, `.github`, `templates`: any
  markdown files inside a skill's own templates directory are never checked
  by any hook.

## Provenance and maintenance

Last verified 2026-07-05 by direct command execution against commit
`82292e1` plus the then-in-flight working tree (that campaign completed
2026-07-06; `main` is now at or past `74e34c5`).

Re-verify:
- Pre-commit scope (all hooks, not just skill-governance): `grep -B2 "files:" .pre-commit-config.yaml`
- CI scope: `cat .github/workflows/validate.yml`
- Branch protection: `gh api repos/dtsong/my-claude-setup/branches/main/protection`
- openrouter pytest count: `pytest mcp/openrouter/tests/ -q`
- Gate mechanics: `cat hooks/acceptance-gate.sh`
- Live contract progress: `grep -n "^Progress:" .claude/council/sessions/*/acceptance-contract.md`
- Eval-case department count: `find skills/council -name trigger-evals.json | wc -l`
- Suite ceiling constant: `grep max_simultaneous_tokens pipeline/config/budgets.json`
- soc-security/resume-tailor symlink status (this machine only): `git check-ignore -v skills/soc-security skills/resume-tailor`
- Governance spec section numbers: `grep -n "^## 7\.\|^## 8\." pipeline/specs/SKILL-GOVERNANCE-SPEC.md`
