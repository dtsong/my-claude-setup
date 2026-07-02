# Design Document: Claude Code Configuration + Model Optimization

## Overview

The council converged on a two-track plan. Track one is an ungated MVP shipped as one `/ship` PR of six items that change no live model behavior: F1 (revert `settings.json` model from pinned `claude-fable-5[1m]` to a tier alias and resolve the `[1m]` vs `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` contradiction), F2 (rewrite the permissions allowlist to the repo's real bash/python/markdown workload), F3a (fail-soft telemetry dispatcher that removes the private-repo path from public `settings.json`), F4 (refresh the stale 2024-era OpenRouter model IDs), F5 (a unified two-account routing design doc covering every spawn site), and F7 (extract the dormant suites: ECE, resume-tailor, docx-to-pdf, soc-security to the existing `my-claude-setup-private` sibling repo). Track two is eval-gated activation: a 12-case smoke set (F11, v1.1) gates the first live model flip (first `routed_consult` caller, any `/ship` or council-profile model change), and a full 38-case golden harness gates OpenRouter Phase 2 lens relay (F6) and any evidence-based council-skill prune.

The routing philosophy: one schema-validated source of truth (`skills/council/model-routing.json`, extended) keyed by spawn site and parameterized by account profile (`max-plan` vs `api-billed`), with a per-destination egress policy for any external model. On the Max plan, cheap tasks route in-family to Haiku 4.5 (rate-limit cost, zero dollars, no egress); OpenRouter Pattern B is Hold on Max and Trial on the API account only, behind a cost ceiling. Council-skill pruning is deferred: the usage registry was proven a broken instrument (0/67 committed uses; all nonzero entries were this session's own uncommitted writes), so the increment must be made durable and a 2-4 week window observed before any prune, with zero-use treated as inconclusive and any-use as keep.

## Architecture

Perspectives: Architect (structure, single source of truth), Oracle (routing design), Scout (model landscape, chokepoint evidence).

### Single routing source of truth (Architect, non-negotiable)

Routing currently lives on three disconnected surfaces with three vocabularies: `settings.json` `model` (pinned ID), the `_council-engine.md` prose cost-profile table (tier aliases), and `skills/council/model-routing.json` (OpenRouter vendor IDs). The design promotes `model-routing.json` to the single routing table; everything else reads from or is validated against it. Phase 2 lens relay MUST extend this file, never add a fourth surface.

Schema shape (ships as the F5 design doc in v1; machine-readable loader follows behind the smoke-eval gate):

```
{
  "tiers":   { "<alias>": { "max-plan": "<id>", "api-billed": "<id>" } },
  "profiles":{ "max-plan": {...}, "api-billed": {...} },
  "spawn_sites": { "session_default|council.<profile>|ship|looper|subagent|routed_consult": "<alias>" },
  "egress_policy": { "<external_dest>": { "send_allowlist": [...], "zdr": true, "no_train": true, "audit_actual_model": true, "kill_switch": true } }
}
```

Key structural properties:
- Tier aliases resolve to concrete IDs per active profile; `settings.json.model` holds only an alias, never a pinned `claude-*` ID.
- `egress_policy` is a schema field, so Skeptic's send-allowlist is a structural invariant: any external destination without one is a schema violation.
- Subagents carry no `model:` frontmatter (verified 0 of 38 agent files), so the engine routing table is the single chokepoint to extend, not 38 files to edit (Scout).
- The engine's prose cost table is generated from or validated against this file; a model rename becomes a one-file edit.

### Concrete per-spawn-site routing (Oracle, adopted by all)

| Spawn site | Max plan (quality ceiling, rate-limit efficiency) | API-billed (cost per session) |
|---|---|---|
| Session default (`settings.json`) | `opus` daily, `fable` for ceiling; drop `[1m]` | `sonnet`, escalate manually |
| Council profile | `balanced` (Opus deliberation, Sonnet audits); `max` reserved for ceiling runs | `lean` (Sonnet positions/converge, Opus challenges only) |
| Brainstorm agents | `sonnet` (already correct) | `sonnet` |
| Round-2 adversarial challenge | `fable` (opus fallback), cap pair count | `opus` |
| Audit agents | `sonnet` (`opus` only in `max`) | `sonnet` |
| /ship and /looper implement | `opus` | `sonnet` |
| /ship PR review | `fable`/`opus` | `sonnet`, `opus` on repeat failure |
| Cheap tasks (classify/score/scout) | `claude` -> `claude-haiku-4-5-20251001`, temp 0; NOT OpenRouter | OpenRouter current-gen cheap model, eval-gated, temp 0, cost ceiling |
| OpenRouter Pattern A (lens relay) | Gated Trial only, one lens, 38-case harness entry gate | Same; forbidden for proprietary work-account code |

### F3a telemetry dispatcher (Operator design, Architect endorsed)

Create `hooks/telemetry-dispatch.sh` in this repo (~5 lines): resolve the private hook path from an env var defaulting to the known location, `[ -f "$path" ] || exit 0`, else `exec python3 "$path" "$@"`. Point all five hook events (`settings.json` lines 71, 82, 93, 104, 115) at the dispatcher. Net effect: no private path in public config, fresh clones no-op cleanly, the API work account stops erroring on every tool call.

### OpenRouter integration state

Phase 1 is implemented and pushed (`mcp/openrouter/{server,routing,openrouter_client}.py` + tests, fail-soft verified) but has zero callers and stale IDs. F4 refreshes IDs (candidates to evaluate at wire time via `list_models()`: `google/gemini-2.5-flash`, `ling-2.6-flash`, `minimax-m3`, `qwen3.7`) and wires a periodic `list_models()` refresh so IDs never rot again. The MCP server stays gated behind a flag until a caller exists. F6 (Phase 2 relay) is out of this PRD: its target `.claude/workflows/council-deliberate.js` does not exist locally, making it XL effort.

## User Experience

Perspectives: Strategist (scoping, sequencing, metrics), Craftsman (DX, permissions, pruning quality bar).

### MVP and roadmap (Strategist)

One `/ship` PR, sequenced by dependency then RICE: F3a (RICE ~1350, unblocks telemetry) -> F1 (2000) -> F2 (400) -> F4 (240) -> F5 (128) -> F7. Each finding maps to a GitHub issue.

| Phase | Items | Gate |
|---|---|---|
| v1 (now) | F1, F2, F3a, F4, F5 (doc), F7 (extraction) | None: no live model behavior changes; `pre-commit run --all-files` per item |
| v1.1 | F3b (hook hardening/perf), F11 (12-case smoke eval), F9 (harness leverage) | F11 gates first `routed_consult` caller and any live model flip |
| v1.1+ | Full 38-case harness; then gated Pattern A trial; evidence-based council-skill prune | 38-case pass is the entry gate |
| Future | F6 (Phase 2 relay), F8 (new data/ML skills) | Only on validated demand + harness |

Success metrics: settings.json config conflicts -> 0; permission prompts per session -> -50%; spawn sites with documented routing -> 100% on both accounts; telemetry hook survives a clean clone with the private repo absent -> true; dormant suites resident locally -> 0 with a preserved record; F11 pass rate -> 100% before any activation.

### Permissions rewrite (Craftsman, F2)

Replace the imagined-TypeScript allowlist (`npm run`, `npx tsc`, `Write(src/**)`, `Write(tests/**)`) with the real workload: `Bash(pre-commit run *)`, `Bash(pytest *)`, `Bash(python3 *)`, `Bash(gh *)`, `Bash(jq *)`, and `Write(agents/**|commands/**|skills/**|hooks/**|pipeline/**)`. The allowlist should encode intent, not mask a mismatch via `skipAutoPermissionPrompt`. Introduce a `settings.local.json` experiment lane so `settings.json` stays clean and verified (Operator).

### Skill gap and pruning plan

- Extract now, on workload judgment, independent of the registry: ECE (15 `ece-*` agents, ~15 skill dirs, the 266-line `/ece` command, own registry, ~252K), soc-security (1.8M, largest dormant suite), resume-tailor (136K), docx-to-pdf (~8K, flagged optional keep-local since it is cheap and generically useful; default is extract with the rest). Total ~2.2M of the 3.9M skills tree. Destination: the existing `my-claude-setup-private` sibling repo, one atomic commit, manifest/pointer left in this repo's README, all references grepped first (`/ece` body, registry entries, cross-links), reference-integrity pre-commit hook must pass, no secrets follow the suites. Prerequisite: settle whether `/ece` shares `_council-engine.md` or duplicates it before the cut.
- Council-skill pruning (the 67-skill long tail): deferred and evidence-gated. No prune cites usage counts collected before the increment is durable. Rule: any-use = keep; zero-use = inconclusive, never auto-prune.
- New skills (F8): Won't-now. TS/React is already covered (vercel-react-best-practices, web-design-guidelines, frontend-qa); data/ML gaps are unvalidated demand.

### Harness leverage (F9, v1.1; Scout radar)

- Swap the swift-lsp plugin (stack mismatch) for a TypeScript/Python LSP: Trial.
- Agent Teams (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`): keep enabled, isolate reliance to the council engine, watch release notes (experimental flag).
- Cron/scheduled routines: Assess; candidate use is the registry usage-decay report once telemetry is durable.
- Auto-memory: keep disabled; the bespoke `memory/HANDOVER-*.md` protocol wins until auto-memory demonstrably beats it.
- Workflows (council-deliberation template): Adopt, already proven.

## Risk Assessment

Perspectives: Skeptic (trust boundary, validation gates), Operator (production config, blast radius).

### Critical and High findings

1. **OpenRouter egress (Critical if unconstrained).** `openrouter_client.py` sends `system + prompt` verbatim to third-party vendors with zero redaction. No routed egress ships without: (a) a send-allowlist in `routing.py` forbidding file contents and secrets; (b) ZDR + no-training flags per request; (c) the relay logging and asserting the actual vendor model returned (a silent Claude fallback must not masquerade as diversity); (d) a kill switch (`defaults.fallback=claude`, empty `tasks` map). Gated, the residual risk on this mostly-public meta-repo is Medium; work-account proprietary code egress remains forbidden outright.
2. **Telemetry hook blast radius (High).** Five lifecycle events bare-call a private-repo Python script; `PostToolUse` fires on every tool call (~50-150ms interpreter cold start). On any clone without `my-claude-setup-private` (guaranteed on the API work account) every tool call errors. F3a is the v1 ship-blocker; F3b (vendoring, batching, alert tuning) is v1.1.
3. **Live symlinked config (High).** `settings.json` is symlinked to `~/.claude/settings.json`, so a malformed edit breaks the running harness with no gate. A pre-commit JSON-schema validator for settings.json is an acceptance criterion.
4. **1M-context contradiction (High).** `claude-fable-5[1m]` requests a 1M variant that `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` removes from the picker (Anthropic docs; GitHub #50803 notes the suffix is silently dropped elsewhere). Resolve to one deliberate state before F1 lands.
5. **API-account runaway spend (High).** A routing typo on the dollar-billed account has no cap. Mitigation: per-model `max_tokens` clamp, frontier-ID denylist in the `tasks` block, routed-call volume alert.
6. **Extraction dangling references (Medium).** Non-atomic ECE moves break `/ece`, registry entries, cross-links. Mitigation: grep all refs, single commit, manifest, reference-integrity hook.

### Rollback posture

`git checkout settings.json` (the symlink picks up immediately); OpenRouter off via empty `tasks` map; extraction reverts as a single commit; no destructive data ops while pruning stays deferred.

## Quality Strategy

Perspectives: Oracle (eval framework), Craftsman (test pyramid, validation), Scout (evidence standards).

### Eval-before-activation (the converged rule)

The MVP ships ungated because none of it flips live model behavior; the gates attach at activation boundaries:

- **12-case smoke set (F11, v1.1, ~0.5 day):** 4 classification, 4 scoring/structured-output, 4 council-lens fidelity cases. Merge gate for the first `routed_consult` caller and any live model flip in `/ship`, `/looper`, or council profiles. Pass = composite >= 4.0 and format compliance 100%.
- **38-case golden harness (v1.1+):** ~20 common, ~10 edge, ~8 adversarial (including prompt-injection in retrieved text). Entry gate for F6 (Phase 2 relay) and any prune-by-evidence decision. Composite: correctness (LLM-judge >= 4.0) x 0.45 + format 100% x 0.25 + persona fidelity >= 4.0 x 0.20 + cost/latency within profile x 0.10.
- Eval assets live in `pipeline/evals/`, outside skill dirs per the governance spec.
- Pattern A promotion rule: each candidate lens persona runs the golden set on both Claude and the target vendor model; only lenses whose non-Claude score is within threshold promote. No measurable diversity value means OpenRouter collapses to Pattern B on the API account only.

### Telemetry as a trustworthy instrument

Verified: committed HEAD shows 0/67 council-skill uses across 4+ prior sessions; all 10 nonzero entries were this session's uncommitted writes. The engine-level increment (`_council-engine.md:672-673`) is the right layer (fires at inline `skillContent` load) but is a prose instruction that was skipped in every prior session. Fixes before the 2-4 week prune window opens: make increments durable (untracked sidecar such as `skills/council/registry.uses.jsonl`, or auto-commit), replace the prose step with a deterministic script/hook, and register a telemetry path for standalone suites (which load via the Skill tool, uncovered by the unwired `skill-telemetry.sh`). Interpret the window as evidence of life, not death (opt-in counters undercount by design, per Scout's prior art).

### Validation and verification

- Routing schema validation test: rejects pinned `claude-*` IDs in Claude-tier slots, flags stale OpenRouter IDs, asserts every spawn site has an entry for every profile. The correct thing is the only thing that validates.
- settings.json JSON-schema pre-commit check (Skeptic non-negotiable).
- Structured output from any cheap-routed model must be schema-constrained and pass a rule-based validator in the caller before trust.
- Council personas get a prompt changelog linked to eval scores before any persona is promoted to a non-Claude model.
- Every F-item verified with `pre-commit run --all-files` (token budgets, frontmatter, reference integrity, isolation). There is no tsc/eslint surface in this bash/python/markdown repo; state that explicitly rather than claiming a JS type-check passed.

## Tension Resolutions

| Tension | Agents | Resolution | Reasoning |
|---|---|---|---|
| Eval harness before everything vs MVP ships now | Oracle, Craftsman, Skeptic vs Strategist | Eval-before-activation: MVP ships ungated; 12-case smoke set gates the first live model flip; 38-case harness gates Phase 2 relay and prune evidence | F1/F2/F4/F5/F3a change no live model dispatch and F4's stale IDs have zero callers, so gating them was misapplied rigor; the gate moves to where behavior actually changes |
| F3 telemetry hardening: v1 blocker vs v1.1 fill-in | Operator vs Strategist | Split: F3a (fail-soft dispatcher + private-path removal, XS) joins v1; F3b (vendoring, batching, alert tuning, M) defers to v1.1 | The ship-blocking piece is 5 string edits + a 5-line script (RICE ~1350); the M-sized work is optimization, not correctness. Strategist's own RICE table had F3 above F5, so the original cut-line was inconsistent |
| "Registry tracking works" vs "broken instrument" | Scout, Operator vs Craftsman | Scout and Operator retracted: committed HEAD shows 0/67 uses; all nonzero entries were this session's uncommitted writes. Durable increment + deterministic step, then a 2-4 week window; zero-use = inconclusive, any-use = keep | The only data points were session-local noise erasable by `git checkout .`; an instrument that persisted 0 events across 4+ sessions is untrustworthy by construction |
| OpenRouter Pattern A egress: block vs trial | Skeptic vs Scout | Gated Trial on one lens only: send-allowlist in `routing.py`, ZDR + no-training flags, provider allowlist, actual-model audit assertion, kill switch; must prove measurable diversity or collapse to Pattern B API-only | Verbatim `system+prompt` forwarding is confirmed, but OpenRouter platform controls (ZDR, no-training, provider allowlists) address the controllable half; gated residual is Medium for this mostly-public repo. The trial doubles as Oracle's persona-transfer test |
| OpenRouter Pattern B economics on Max plan | Scout, Skeptic, Oracle vs the June 22 spec's intent | Hold on Max (cheap tasks route in-family to Haiku 4.5); Trial on API account only, after F4 ID refresh, behind a cost ceiling | OpenRouter bills real dollars + 5.5% fee where Haiku on Max is rate-limit-free; routing cheap work off-platform on Max spends money to avoid a free call |
| Dormant-suite extraction timing: now vs v1.1 vs data-gated | Craftsman, Scout, Operator vs Strategist (timing); Oracle (data-gating) | F7 moves into the MVP PR: extract now on workload judgment, independent of the registry | Usage data will never accrue for suites the user is not exercising; extraction is reversible, record-preserving, and the workload evidence (no ECE/hardware work) is independent and sufficient |
| Routing consolidation: one landing vs phased | Architect vs Strategist, Oracle | F5 ships as a design doc in v1 (no behavior change, ungated); the machine-readable loader and first live caller are gated behind the 12-case smoke eval | A config that reroutes models is only safe once a smoke set proves the reroute holds; the single-source-of-truth requirement itself is non-negotiable regardless |
| Council-skill pruning aggression | Skeptic, Craftsman vs earlier prune-lean framings | Deferred entirely: no prune on current registry data; only the council long tail is in scope after the hardened 2-4 week window, gated on the 38-case harness | Deleting on a newborn/unplugged counter is Chesterton's-fence destruction; irreversible-change territory demands evidence |

## Decision Log

| Decision | Options Considered | Chosen | Reasoning |
|---|---|---|---|
| Session default model (F1) | Keep pinned `claude-fable-5[1m]`; tier alias | Tier alias (`opus` daily / `fable` ceiling on Max; `sonnet` on API); resolve `[1m]` vs `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` to one deliberate state | Pinned ID violates the repo's own governance (engine line 105) and self-cancels against the env flag; a meta-config repo does not need 1M context |
| Routing source of truth | Three surfaces as-is; new fourth config; unified `model-routing.json` | Extend `skills/council/model-routing.json` with `tiers`/`profiles`/`spawn_sites`/`egress_policy`; engine prose table generated from or validated against it | Same decision expressed in three vocabularies can never stay consistent; subagents have no model frontmatter, so one chokepoint suffices |
| Cheap-task routing, Max plan | OpenRouter cheap models; native Haiku 4.5 | Haiku 4.5 in-family, temp 0 | Free under plan rate limits, no key, no cross-vendor egress; OpenRouter there converts free calls into billed ones |
| OpenRouter Pattern B | Enable both accounts; API-only; disable | Hold on Max; Trial on API after ID refresh, with cost ceiling, max_tokens clamp, frontier-ID denylist, volume alert | Economics invert by billing profile; stale IDs would 404 and silently never fire the cheap path |
| OpenRouter Pattern A (Phase 2 relay, F6) | Build now; block; gated trial later | Out of this PRD; later gated Trial (one lens) behind the 38-case harness + egress safeguards; collapse to Pattern B if no measurable diversity | Target `council-deliberate.js` does not exist locally (XL effort); persona transfer to non-Claude models is unproven; egress ungated is Critical |
| Stale OpenRouter IDs (F4) | Leave until Phase 2; refresh now | Refresh now (zero callers, so ungated) + wire periodic `list_models()` refresh | 2024-era `gpt-4o-mini`/`gemini-flash-1.5` are ~2 years stale; refresh cadence prevents future rot |
| Telemetry hook (F3) | Defer whole; fix whole in v1; split | Split: F3a fail-soft dispatcher in v1; F3b hardening in v1.1 | Ship-blocker is XS (break-on-clone, API-account errors, private-path leak); perf work is M and non-blocking |
| Dormant suites disposition (F7) | Keep; delete; extract to private repo | Extract ECE + resume-tailor + soc-security + docx-to-pdf to `my-claude-setup-private` now, atomic commit, manifest/pointer in README; docx-to-pdf flagged optional keep-local; verify `/ece` vs `_council-engine.md` coupling first | ~2.2M of 3.9M skills tree, off-workload; extraction preserves the record the user wants, deletion is off the table |
| Council-skill pruning | Prune on zero-use now; prune on heuristics; defer to evidence | Defer: durable increment first, 2-4 week window, zero-use inconclusive, any-use keep, 38-case harness gates any prune | Committed registry has zero real data; pruning on an unplugged odometer destroys unmeasured work |
| Eval gating | Full harness before everything; no evals; activation-boundary gates | 12-case smoke set (F11) gates first live model flip; 38-case harness gates F6 + pruning; MVP ungated; assets in `pipeline/evals/` | Match test cost to change risk: gate what changes behavior, not what corrects config |
| Permissions allowlist (F2) | Keep npm/tsc list; rewrite to workload | Rewrite: pre-commit/pytest/python3/gh/jq + `Write(agents|commands|skills|hooks|pipeline)`; add `settings.local.json` experiment lane | Current list describes an imagined TS project; the allowlist should encode real intent |
| settings.json safety | Trust manual edits; schema validator | Pre-commit JSON-schema validation before the symlink serves the file | The file is live production config with instant blast radius and no staging |
| Harness leverage (F9, v1.1) | Adopt everything; status quo | Swap swift-lsp for TS/Python LSP; keep Agent Teams isolated to the council engine; Assess cron for the usage-decay report; auto-memory stays disabled | Match features to the TS/React + Python + bash workload; experimental flags stay contained; handover protocol currently beats auto-memory |
| MVP composition and order | F1/F2/F4/F5 only; everything at once | One PR: F3a -> F1 -> F2 -> F4 -> F5 -> F7, each an issue for `/ship` | Highest value-per-effort core; F3a first because F5 metrics and F7 records read the telemetry pipeline; F6/F8 stay Won't-now |
| F10: HTML presentation at council touchpoints (user-added post-synthesis, approved 2026-07-02) | Text-only AskUserQuestion; HTML render + AskUserQuestion | Engine design-approval touchpoint generates a self-contained design.html from the synthesis payload, opens it in the browser, keeps AskUserQuestion as the approval mechanism; template derived from this session's render | User request during design review; no model behavior change, so it joins the ungated MVP |
