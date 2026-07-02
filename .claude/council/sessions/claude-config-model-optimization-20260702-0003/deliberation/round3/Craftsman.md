# Craftsman Final Position — Claude Config & Model-Routing Optimization

**Revised recommendation:** Ship the config-hygiene + unified-routing-doc MVP (F1 alias fix, F2 permissions, F3a fail-soft telemetry wrapper, F4 ID refresh, F5 routing schema doc) ungated, because none of these flip live model behavior. Gate the *first* live model flip and the pruning decision behind tests, following the test pyramid: a 12-case smoke set at every activation boundary, the full 38-case harness as the entry gate for Phase 2 lens relay and any prune-on-evidence claim. Treat the skill registry as a broken instrument until the engine-level increment is proven deterministic over a real window; extract dormant suites now on workload judgment, independent of that instrument.

## Concessions made and why

1. **Dropped "eval-before-everything" in favor of eval-before-activation.** Oracle and Strategist are right that F1/F2/F5 change no live model behavior and F4's stale IDs have zero callers, so an eval gate on them is testing theater. This is actually *correct* pyramid discipline: match test cost to change risk. Doc-only and dead-code changes get the type/lint/pre-commit gate they already have; the expensive smoke and harness suites attach to the boundaries where a wrong model actually reaches a user (first `routed_consult` caller, `/ship` or council-profile flips, Phase 2 relay). I relaxed the timing, not the requirement.

2. **Accepted a 2-4 week telemetry window before council-skill pruning** (Operator's window), conditioned on hardening. I had argued the instrument is void; Scout retracted "tracking works" and confirmed my facts (HEAD = 67/67 zero uses; the 10 nonzero entries are this session's uncommitted writes). Scout's retained point stands: the engine-level increment at `_council-engine.md:672-673` is the *right* layer and did fire today, so a deterministic-increment fix plus a real window can produce genuine data. I concede that waiting for that data beats pruning blind.

3. **Conceded that a tracking mechanism exists** (engine prose), so my Round 1 "unwired, wrong-layer" framing over-indexed on `skill-telemetry.sh`. The correct fix is not to wire that script (wrong layer: council skills inline via `skillContent`, engine line ~612) but to make the engine increment durable.

## Non-negotiables

1. **F3a ships in the v1 MVP, not v1.1.** The private path `$HOME/Development/my-claude-setup-private/hooks/session_telemetry.py` is called bare on 5 events (settings.json lines 71/82/93/104/115) with no existence guard. This breaks on a fresh clone, on the second machine, and on the API work account, and it leaks a private path into public config. Both my v1 routing metrics and the evidence-based prune *depend* on this telemetry pipeline being reliable, so the fail-soft dispatcher wrapper is a gate, not a nicety. F3b (vendoring, per-call perf, batching) can wait.

2. **The routing config is one schema-validated source of truth.** Two configs (engine tier-alias table + `model-routing.json` with vendor IDs) is pattern drift. The unified schema must have a validation test that: rejects pinned `claude-*` IDs in Claude-tier slots, flags stale OpenRouter IDs, and asserts every spawn site has an entry for every profile. Types-as-documentation: the correct thing is the only thing that validates.

3. **No council-skill pruning on current registry data.** Zero uses is inconclusive (broken odometer); any use is keep. This is irreversible-destruction territory. Extraction of dormant *suites* (ECE, resume-tailor, soc-security) is a separate, reversible move justified by workload fit and proceeds now.

4. **The 12-case smoke set is an acceptance criterion inside the F-item that first activates a live flip**, and the OpenRouter relay (if Pattern A trials) ships with a contract test that asserts the actual vendor model returned and that the send-allowlist blocked file contents/secrets. A relay you cannot assert the identity of is untestable and therefore not shippable.

## Implementation notes

- **F1 (alias):** `settings.json` `"model": "claude-fable-5[1m]"` -> `"fable"` (or `"default"`); remove the `[1m]` suffix OR flip `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` in `env` so the context signal is single and coherent. These two currently contradict.
- **F2 (permissions):** replace the npm/tsc/git allow-list with the real workload: `Bash(pre-commit run *)`, `Bash(pytest *)`, `Bash(python3 *)`, `Bash(gh *)`, `Bash(jq *)`, and `Write(agents/**|commands/**|skills/**|hooks/**|pipeline/**)`. The allow-list should encode intent, not an imagined TS project.
- **F3a:** one ~5-line dispatcher script (existence-check + `|| exit 0`) plus five string edits in settings.json routing the hooks through it. Removes the private path from public config in the same edit.
- **F5 (routing schema):** add `pipeline/specs/` JSON Schema for the routing file; validation test lives outside skill dirs per governance. Cover session default, brainstorm/council/round-2/audit spawns, `/ship` + `/looper`, OpenRouter Pattern A relay + Pattern B task classes. Max-plan profile: quality ceiling + Haiku-in-family for cheap tasks (Oracle). API profile: cost-per-session with Pattern B and Skeptic's cost ceiling.
- **Eval assets:** `pipeline/evals/` holds the 12-case smoke set (v1.1 gate for first `routed_consult` caller) and the 38-case harness (entry gate for F6 relay + F7 prune evidence). Eval cases live outside skill directories per the governance spec.
- **Telemetry fix (feeds the prune window):** make the engine increment at `_council-engine.md:672-673` durable via an untracked sidecar or auto-commit, so uses survive without a session hand-write; register a working recorder for standalone suites; scope the 2-4 week window to the council long tail only.
- **Extraction:** move ECE (15 `ece-*` agents, ~15 skill dirs, `/ece` command, own registry, ~120 KB) + resume-tailor + soc-security to a private attic repo with a pointer/manifest left behind. Prerequisite: settle whether `/ece` shares `_council-engine.md` or duplicates it before the cut. `docx-to-pdf` is cheap and generically useful; keeping it local is defensible.
- **Verification (user directive):** run `pre-commit run --all-files` after each F-item; there is no tsc/eslint surface in this bash/python/markdown repo, so state that explicitly rather than claiming a JS type-check passed.
