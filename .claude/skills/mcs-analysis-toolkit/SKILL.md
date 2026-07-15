---
name: mcs-analysis-toolkit
description: Use when you must prove a claim about this repo's token budgets, description trigger-reliability, hook-blocking behavior, multi-agent session cost, or a counter's trustworthiness before citing it in a review or merge decision, rather than eyeballing it or trusting a hook that merely looks wired. Covers hand-deriving token math, live-fire hook payloads, write-path-to-commit tracing, refute-first fix verification, each with a worked example. Not for routine tool invocation or exit-code reading (mcs-diagnostics-and-tooling), acceptance-evidence tiers (mcs-validation-and-qa), or the hunch-to-accepted-result idea lifecycle (mcs-research-methodology).
---

# mcs-analysis-toolkit

## Overview

Six first-principles recipes for proving a claim about this repo instead of asserting it: derive it by hand from source, confirm with read-only tools, and (for review claims) build a discriminating experiment that refutes a wrong belief. Each recipe ends in a worked example reproduced 2026-07-02, with a command to re-verify it.

## When to use, and when NOT to

Use when: sizing a suite's worst-case context load before shipping, auditing whether a description will actually trigger, verifying a hook truly blocks before depending on it, sanity-checking a multi-agent cost estimate, deciding whether a counter is trustworthy enough to cite, or reviewing a "fix" before merge.

Do NOT use for: routine tool runs once you already trust them, that is mcs-diagnostics-and-tooling (inventory counts, budget reports, eval runs, exit-code tables). What counts as sufficient acceptance evidence is mcs-validation-and-qa. How a hunch becomes an accepted result over time is mcs-research-methodology.

## Recipe 1: Token / context-load accounting

**Formula:** `tokens = ceil(words * 1.33)` (`TOKEN_RATIO`, `pipeline/hooks/_utils.py:13`). Worst-case simultaneous load, per specialist: coordinator + specialist + its single largest reference file (only one specialist and one reference load at runtime). Hard ceiling: 5,500 tokens (`pipeline/config/budgets.json: max_simultaneous_tokens`), overridable per suite. Root `CLAUDE.md:57`'s "5,000" is a stale outlier; enforcement uses 5,500.

**Procedure:**
- `wc -w` the coordinator, specialist, and largest `references/` file; apply the formula to each, round up, sum.
- Check `budgets.json.overrides` for a key equal to the *exact relative path the hook computes*, not a guessed path.
- Confirm: `python3 pipeline/hooks/check_context_load.py <coordinator SKILL.md>` (hard hook).

**Worked example** (`skills/soc-security/skills/threat-model-skill`): 468 + 2828 + 1275 words → 623 + 3762 + 1696 = 6081 tokens, 581 over ceiling. A 6,100-token override exists in `budgets.json` but never matches the hook's computed key (nested-suite path mismatch). Full evidence: `references/worked-examples.md` §1.

## Recipe 2: Trigger-reliability analysis

**Formula** (`pipeline/specs/SKILL-TRIGGER-RELIABILITY-SPEC.md` §1.2): activation directive + positive triggers + 2-5 quoted phrases + a negative boundary naming the alternative. Target 40-80 words (§1.5); under 20 "almost always" under-activates. The only *hard* floor is 10 words (`check_frontmatter.py: MIN_DESCRIPTION_WORDS = 10`), so 10-40 words passes silently.

**Procedure:**
- Count the description's words; score against the formula (activation verb? quoted phrases? negative boundary?).
- Sum always-loaded description cost library-wide: `python3 pipeline/scripts/skill-audit.py --json` (`total_description_tokens`, `over_threshold`).
- Design positive/negative eval pairs using the as-built shape from an existing department (`{id, input, expected_skill, type, description}`), not the spec's fuller markdown template (unimplemented).

**Worked example:** `skill-audit.py --json` over `skills/`: 123 skills, 5,966 description tokens, 0 over threshold. Under-target cluster: `git-workflows` (10-word description) and `prompt-wizard` (11 words) clear the floor but sit at a quarter of target, no quoted phrases or negative boundary; git-workflows is a *coordinator* (13 nested specialists) that per §1.6 should "cast a wide net" and does not. Full evidence: `references/worked-examples.md` §2.

## Recipe 3: Hook-blocking verification experiment

**Rule:** a hook wired into `settings.json` is not proof it fires or blocks. Prove, in order: its event+exit-code contract (`PreToolUse` + exit 2 denies the tool, stderr feeds back as the reason; `PostToolUse` + any non-zero exit is *non-blocking*, whatever the script prints), which stream carries its message, then a live-fire test plus a control payload that should pass.

**Procedure:** Read the `settings.json` registration (event, matcher) and the script's stdin contract. `echo '<crafted JSON>' | bash <hook.sh>`, check exit code and stream. Repeat with a control payload, confirm exit 0. Trust the hook only after both pass.

**Precondition (checked 2026-07-05):** the live-fire result below needs a fresh (<`ACCEPTANCE_GATE_STALE_HOURS`, default 72; see mcs-change-control) contract with an unresolved `| pending |`/`| failed |` row. A stale or fully-resolved contract makes the payload exit 0 with no output, that is the staleness guard working, not the hook failing to block. Check the newest contract's mtime first (`ls -lt .claude/council/sessions/*/acceptance-contract.md | head -1`).

**Worked example** (`hooks/acceptance-gate.sh`): with a fresh (<72h) contract carrying a pending/failed row, a `TaskUpdate → completed` payload exits 2, message on stderr; a `status: in_progress` control exits 0. Same experiment would have caught the gate's 4-month decorative period: before `605112d` (2026-06-22) the identical script was `PostToolUse`, printed to stdout, exited 1 (non-blocking), so completion always went through from creation (`299a264`, 2026-02-16). Full transcript: `references/worked-examples.md` §3.

## Recipe 4: Cost/latency estimation for multi-agent runs

**Model:** the engine's table (`commands/_council-engine.md` §Cost Profiles & Model Routing) gives a 5-agent-baseline token range per mode × profile, scaled by `selected_agents / 5`: brainstorm 10-15K flat; quick 20-35K/30-50K/45-75K; standard 80-120K/120-180K/180-270K; deep = standard + 50-150K audit, for lean/balanced/max.

**Procedure:** Read mode + profile off the session; take the baseline range; multiply by `agents_selected / 5`. Label the result an estimate: do not convert to dollars from memory, the engine points to a README "Cost guide" for $/MTok that does not exist in `README.md` (verified 2026-07-02).

**Worked example** (session `claude-config-model-optimization-20260702-0003`): profile `max`, 7 agents, standard-mode artifacts. Baseline (5-agent, standard, max) = 180-270K tokens, scaled by 7/5 = 252K-378K tokens. **Estimate, not a committed actual**: no telemetry here captures real per-session totals as of 2026-07-02. Full derivation: `references/worked-examples.md` §4.

## Recipe 5: Instrument-trust audit

**Rule:** before citing any counter, trace its write path: who writes it under what condition, prose or enforced code, does it land in a commit, can it be contaminated by something outside its scope.

**Procedure:** Grep for the field name in the code/prose that writes it; classify the step (prose vs. enforced code). `git log -- <file>`, diff HEAD vs. working tree, an uncommitted write is invisible to everyone else. Check for contamination (a machine-wide symlink shared across projects?). Trust the counter only after one full write-through-commit cycle by SHA.

**Worked example** (`skills/council/registry.json`): write step is prose only (`commands/_council-engine.md:672-677`), no code enforces it. Last commit before today: `729adcd` (2026-04-24, all `uses: 0`); next: `dc44611` (2026-07-02, 18 uses), a 69-day gap where the write never got committed. One session slug has no matching directory in this repo, because `~/.claude/skills` symlinks here, so every workspace on this machine shares one file with no workspace tag. Cite it as "at least these sessions ran," never full usage history. Full evidence: `references/worked-examples.md` §5.

## Recipe 6: Refute-first review

**Rule:** for any "fix," before approving it: state the exact wrong behavior it prevents as input → wrong output; build one discriminating experiment whose result differs pre-fix vs. post-fix; run it. Reading the diff and agreeing with its narrative is not verification.

**Procedure:** State the failure scenario in one sentence. Isolate the code path (inject a fake dependency/transport/stdin rather than the real network or tool). Run the same experiment against `git show <fix_commit>^:<file>` (pre-fix) and the current file (post-fix). Confirm the two disagree on a caller-visible field, not just internal structure.

**Worked example** (commit `898174d`, `mcp/openrouter/openrouter_client.py`): claimed failure was that `urlopen` raises `HTTPError` on 4xx/5xx, misclassified as transport failure. Monkeypatching `urlopen` to raise `HTTPError(code=429, ...)` and reading `consult(...)["error_kind"]` gives `"http"` on the current file, `"transport"` on `898174d^`, both reproduced directly: a caller-visible field changes, so the fix is genuinely load-bearing. PR #55 has zero GitHub reviews and comments: the review that mattered was this self-run experiment. Full script: `references/worked-examples.md` §6.

## Gotchas

- WRONG: "the override is in budgets.json, covered." RIGHT: the key must equal the hook's *computed* relpath; `skills/<suite>/skills/<specialist>` almost never matches a flat `skills/<specialist>` key (Recipe 1).
- `classify_file()` treats any path containing a `skills/` segment as "specialist," even repo-root `skills/` itself, so nearly every top-level `skills/*/SKILL.md` gets the 1,500-word target regardless of intent. Only a sibling `skills/` subdirectory makes it "coordinator" (git-workflows qualifies, prompt-wizard doesn't).
- Passing `check_frontmatter.py` proves only the 10-word floor, not that a description will trigger; trigger reliability has no hard hook.
- `PostToolUse` + non-zero exit is silently non-blocking; only `PreToolUse` + exit 2 denies a call. Confusing the two shipped a 4-month decorative hook (Recipe 3).
- A cost/token estimate from the engine's table is a range, not a telemetry-backed actual; nothing here records real per-session totals as of 2026-07-02.
- A counter present and non-zero may not be committed, or scoped to the project you're standing in; check both (Recipe 5).
- "Passed review" can mean zero human reviewers plus a local Claude review loop (`gh pr view <n> --json reviews,comments`); a merged-without-review fix still needs your own experiment.
- `skill-audit.py`, `budget-report.py`, `context-load-analysis.py` are read-only, never fail a commit; a clean report is not a passing hard gate.

## Provenance and maintenance

Last verified: 2026-07-02, against a live ship run (session `claude-config-model-optimization-20260702-0003`, commits through `dc44611`). Volatile numbers (registry counts, token totals, PR/issue state) will drift as work continues; re-verify:

- Token ratio: `grep -n TOKEN_RATIO pipeline/hooks/_utils.py`
- Ceiling + override mismatch: `python3 pipeline/hooks/check_context_load.py skills/soc-security/SKILL.md`
- Description formula/word target: `sed -n '100,176p' pipeline/specs/SKILL-TRIGGER-RELIABILITY-SPEC.md`
- Library-wide description cost: `python3 pipeline/scripts/skill-audit.py --json`
- Hard description floor: `grep -n MIN_DESCRIPTION_WORDS pipeline/hooks/check_frontmatter.py`
- Hook live-fire (requires a fresh, unresolved contract first, see Recipe 3 precondition): `echo '{"tool_name":"TaskUpdate","tool_input":{"status":"completed"}}' | bash hooks/acceptance-gate.sh; echo $?`
- Cost table: `grep -n "Estimated session cost" -A 10 commands/_council-engine.md`
- registry.json commit history: `git log --oneline -- skills/council/registry.json`
- Discriminating-experiment source: `git show 898174d -- mcp/openrouter/openrouter_client.py`
- PR review count: `gh pr view 55 --json reviews,comments`
