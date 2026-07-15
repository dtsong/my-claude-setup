# Phase 3 detail: OpenRouter Phase 2 lens relay, gated

This phase is a candidate, not a queued issue. The track-1 campaign closed 2026-07-06 without ever ticketing it; `prd.md`'s non-goals explicitly park it ("No OpenRouter Phase 2 lens relay (F6: future, gated by 38-case harness + egress safeguards)"). Read this file before writing any code that gives `mcp/openrouter/routing.py`'s `routed_consult()` its first caller, or before touching `.claude/workflows/`.

## Prerequisite checklist (all re-verified live, 2026-07-02)

| # | Prerequisite | Status | Re-verify with |
|---|---|---|---|
| 1 | 38-case golden eval harness | Does not exist. No `pipeline/evals/` directory anywhere in the repo. Design-doc gate only (design.md: "~20 common, ~10 edge, ~8 adversarial including prompt-injection in retrieved text"). | `ls pipeline/evals` |
| 2 | Egress controls: send-allowlist, ZDR flags, actual-model audit, kill switch | Designed (schema field `egress_policy` specified in US-005's target shape), zero implementation. `openrouter_client.py` forwards `system + prompt` verbatim today, no redaction. | `grep -rn "send_allowlist\|zdr\|kill_switch\|no_train" mcp/openrouter/*.py` (expect empty) |
| 3 | Fresh OpenRouter model IDs | Done (US-004/AC-010..012, PR #70): `openai/gpt-5.4-nano`, `google/gemini-3.5-flash`, `openai/gpt-5.4-mini`, all verified live against a 338-model catalog. Re-verify monthly; IDs rot. | `python3 mcp/openrouter/check_models.py` |
| 4 | `OPENROUTER_API_KEY` provisioned | Unset on this machine as of 2026-07-06. `consult()` fails soft (`missing_key` → `fallback: claude`) without it, nothing breaks, but nothing real can be tested either. | `[ -n "${OPENROUTER_API_KEY:-}" ] && echo SET \|\| echo UNSET` |
| 5 | 12-case smoke eval (F11) | Not built. This is the *smaller* gate (v1.1) that unlocks Pattern B's first live caller; the 38-case harness above is a separate, larger gate for Pattern A specifically. Neither exists yet. | `gh issue list --search "F11" --state all` |

The design doc's own risk framing: "OpenRouter egress (Critical if unconstrained)." Gated with allowlist + ZDR + no-training flags + actual-model audit + kill switch, residual risk drops to Medium for this mostly-public meta-repo. Ungated, it is a hard no regardless of how small the change looks.

## Solution menu, ranked, with obligations

### 1. Pattern B, routed `consult()` relay (recommended first step)

`mcp/openrouter/routing.py`'s `routed_consult(task, system, prompt)` already exists, is fail-soft (`{"fallback": "claude", "reason": ...}` on any unmapped task or failure, never raises), and has zero callers anywhere in the repo (`grep -rn "routed_consult(" --include=*.py .` finds only its own test file). It runs in main-loop or subagent context directly, no relay hop needed, because those contexts already have MCP tool access.

Obligations before wiring its first caller:
- **Fail-soft contract preservation proof.** Write a test that kills the network mid-call and asserts the caller's downstream behavior is bit-identical to "route this task to Claude", not merely that the function returns without raising.
- **Token/cost model.** OpenRouter bills per-token plus a 5.5% platform fee on the API-billed account. Compute cost-per-call for the target task class at expected volume and compare against the Claude-native cost for the same task at the same tier. On the Max plan, cheap tasks route in-family to Haiku 4.5 (free under plan rate limits), Pattern B on Max is a net cost *increase* unless the target task class cannot run on Haiku at all. Design.md's converged position: Pattern B is Hold on Max, Trial on API-billed only.
- **Quality eval vs all-Claude baseline.** The 12-case smoke set (4 classification, 4 scoring/structured-output, 4 council-lens fidelity) must pass with composite ≥4.0 and 100% format compliance before this caller merges. "It worked in a manual test" is not evidence.

### 2. Pattern A, thin Claude relay for council lenses (gated, larger lift)

Per `docs/superpowers/specs/2026-06-22-openrouter-integration-design.md`: Workflow scripts run sandboxed (no shell, no HTTP), so a Workflow `agent()` cannot call OpenRouter directly. The relay pattern spawns a Claude subagent whose only job is (1) call `consult(model=<routing>, system=<existing lens persona prompt>, prompt=<round prompt>)`, (2) return the model's `text` verbatim as that lens's contribution. Claude-routed lenses keep the current native-subagent path untouched.

Target file `.claude/workflows/council-deliberate.js` does not exist locally (design.md rates this XL effort). Obligations, additive to Pattern B's three above:
- **Persona-transfer proof.** Each candidate lens persona must run the golden set on both Claude and the target vendor model; only lenses whose non-Claude score is within threshold promote. No measurable diversity value collapses that lens back to Pattern B (or to plain Claude) automatically, not by later cleanup.
- **Full 38-case harness pass**, not the 12-case smoke set, Pattern A is the higher-risk, quality-shaping change (it replaces reasoning content a human reads and acts on, not a routing decision).
- **Actual-model audit.** The relay must log and assert which vendor model actually answered; a silent Claude fallback must never masquerade as cross-vendor diversity in a session transcript.

### 3. Direct lens replacement without a relay, rejected

Considered and explicitly rejected in the June 22 design spec: running non-Claude rounds via direct MCP calls from the main-loop council command, skipping the relay hop. Saves one hop but forfeits the Workflow tool's deterministic round-to-round orchestration (parallel R1 → judge pairing → parallel R2 → parallel R3 → synthesis). Do not resurrect this without a new, explicit design decision recorded in a council session, it was not merely deprioritized, it was decided against.

## If asked to "just try it" before the gates open

Don't. The fail-soft contract already means an ungated attempt degrades silently to Claude on any real failure, which makes a shortcut look safe right up until it silently forwards real repo content to a third party on the one call that doesn't fail. Point back to prerequisite #2 (egress controls) and #1 (harness) in the table above; both are concrete, checkable absences, not judgment calls.
