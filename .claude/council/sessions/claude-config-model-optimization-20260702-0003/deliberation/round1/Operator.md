# Operator Position — Claude Config & Model-Routing Optimization

**Core recommendation:** Treat `settings.json` as production config: revert the pinned `claude-fable-5[1m]` to a tier alias (governance-compliant), harden the every-tool-call telemetry hook against its cross-repo dependency, and unify Claude-tier + OpenRouter routing into ONE profile-aware table. Do not prune skills on zero-data — telemetry now works; instrument, then prune with evidence, while extracting off-workload suites (ece/resume/docx/soc) to a private repo now.

## Key argument

This repo IS the live harness (`~/.claude/settings.json` symlinks here), so every config edit is a production deploy with no staging and instant blast radius across every future session. Three operational faults are shippable-blocking. **(1) The model pin.** `settings.json:52` sets `"claude-fable-5[1m]"`: a pinned model ID (the repo's own council engine forbids this at `_council-engine.md:105`) carrying a `[1m]` 1M-context suffix that directly contradicts `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` two lines up. At best the suffix is inert; at worst it is undefined behavior. Fix: `"model": "fable"` (or `"opus"` for routine sessions) and resolve the 1M question deliberately — drop `[1m]` OR set the env flag to `0`, never both. **(2) The telemetry hook.** Five lifecycle events (`SessionStart`/`PostToolUse`/`PostToolUseFailure`/`Stop`/`SessionEnd`) shell out to `python3 $HOME/Development/my-claude-setup-private/hooks/session_telemetry.py` — `PostToolUse` fires on *every tool call*, cold-spawning a Python interpreter each time (~50-150ms), against a path in a *separate* repo. This is a reliability landmine: on the API work account (started from this repo, later branched) or any fresh clone that private repo will not exist, and the hook will error on every tool use. Wrap it fail-soft with an existence guard (or vendor the hook into this repo). **(3) One routing system, not two.** The council engine already has clean tier-alias routing (lean/balanced/max keyed by spawn site); OpenRouter has a parallel `model-routing.json` with stale 2024 IDs (`gpt-4o-mini`, `gemini-flash-1.5`) and Phase 1/2 unwired. Merge them into a single profile-aware routing table covering session default, council profiles, workflow/subagent spawns, /ship + /looper, and OpenRouter Pattern A/B — with a documented model-ID review cadence so IDs never rot again. On skill pruning: the registry now records uses (`uses:1` this session), so "60 zero-use skills" is a pre-instrumentation baseline, not evidence. Pruning on zero-data is deleting before the dashboard populates. Let telemetry run 2-4 weeks, then prune with data; but extract the clearly off-workload suites (ece, resume-tailor, docx-to-pdf, soc-security) to a private repo now — reversible, record-preserving, and it shrinks the classification/load surface.

## Risks if ignored

- **Config-deploy with no rollback.** The uncommitted `fable[1m]` diff is exactly the failure pattern: an unverified edit to the live symlinked config that could pin a stale/unavailable model or trip the 1M conflict, breaking every new session with no staging layer to catch it. No settings.local.json experiment lane means every change ships straight to prod.
- **Cross-repo hook dependency on the hot path.** If `my-claude-setup-private` is moved, renamed, or absent (guaranteed on the API work-account clone), every tool call fires a failing hook — cumulative latency, process churn, and a private path leaking through public config.
- **Cost/dependency at rest with zero payoff.** The OpenRouter MCP server spawns a Python venv per session and needs `OPENROUTER_API_KEY`, yet no skill/subagent calls `routed_consult` and Phase 2 lens relay is unbuilt. Stale routing IDs mean the first real call would hit deprecated models. Ship the wiring or gate the server behind a flag; don't carry live infra that does nothing.

## Dependencies on other domains

- **Architect:** the unified routing-table schema (one system spanning Claude tiers + OpenRouter, profile-aware) and the clean module seam for extracting dormant suites to a private repo.
- **Economist/Strategist:** whether OpenRouter Pattern B is worth the extra dependency vs native Haiku 4.5 for the API account (native avoids a second API key + MCP process). See cost appendix.
- **Skeptic/Security:** `OPENROUTER_API_KEY` handling and the private-path leakage through public `settings.json`.
- **Craftsman/Maintainer:** implementing the fail-soft hook wrapper, the routing loader wiring, and settings.local.json experiment discipline.

---

## Appendix A — Cost Analysis (cost-analysis skill)

Note: this is a config repo, so "infrastructure cost" is **model-token economics** across two billing profiles. Absolute per-token prices are 2026-07 estimates and MUST be verified against the live pricing page before the PRD locks dollar figures; the *relative tier multipliers and structural conclusions* hold regardless.

### Cost components (the two profiles)

| Profile | Unit of cost | Scarce resource | Optimization target |
|---|---|---|---|
| **Max plan** (this account) | Rate-limit budget (5-hour + weekly caps), not dollars | Fable quota (frontier tier drains fastest) | Quality ceiling within rate budget |
| **API-billed** (work account) | Dollars per token | Fable per-token price (highest tier) | Cost per session |

### Relative tier cost (illustrative multipliers, Haiku = 1x baseline)

| Tier | Rel. token cost | Best use | Worst use |
|---|---|---|---|
| Haiku 4.5 | 1x | Classification, scoring, scout research, routine edits | Adversarial synthesis |
| Sonnet 5 | ~4-6x | Positions, converge, audits, most /ship work | High-volume low-stakes tasks |
| Opus 4.8 | ~15-20x | Deliberation, design review, hard synthesis | Bulk sub-tasks |
| Fable 5 | ~30-40x | Round-2 adversarial challenge, ceiling-quality synthesis | Default session model, routine loops |

### Per-spawn-site routing (recommended default per profile)

| Spawn site | Max-plan default | API default | Rationale |
|---|---|---|---|
| Session default (`settings.json`) | `fable` or `opus` | `sonnet` | Max: quality within rate budget. API: Fable-as-default is the #1 cost sink. |
| Council profile | `balanced` (Opus delib, Sonnet audit) | `lean` (Sonnet positions/converge, Opus only for challenges) | `max` profile puts Fable on every Round-2 pair — drains Max quota / multiplies API cost fast. |
| Brainstorm agents | sonnet | sonnet | Already correct in engine. |
| Round-2 challenge | fable (with opus fallback) | opus | Where debate quality pays most; cap the count. |
| Audit agents | sonnet | sonnet | Opus only in `max`. |
| /ship, /looper loops | sonnet, opus for review | sonnet, opus for review | Long-running loops: never leave on fable. |
| OpenRouter Pattern B (classify/score/scout) | cheap OR model — offloads OFF the rate budget | native Haiku 4.5 (avoids 2nd dependency) | Max: rate-limit relief for small $. API: native Haiku beats OR on integration simplicity. |

### Scaling projections (per-session cost driver)

| Workload | Current driver | 2x sessions | 5x | Cost cliff |
|---|---|---|---|---|
| Routine meta-repo edits | Session default tier | linear | linear | Fable default = 30-40x cliff vs Sonnet the moment volume rises |
| Council deliberation | N agents x 3 rounds x tier | linear in topics | linear | `max` profile x many tension pairs = Fable quota exhaustion (Max) / $$ spike (API) |
| Pattern B sub-tasks | Volume x cheap-model price | linear | linear | Routing to Opus/Fable instead of Haiku/OR = 15-40x overspend |

### Optimization recommendations

| Optimization | Est. savings | Effort | Risk | Priority |
|---|---|---|---|---|
| Session default `fable[1m]` → `opus`/`sonnet` (API) or `fable` (Max) | 30-40x on routine turns (API); frees Fable quota (Max) | Low | Low | P1 |
| Default council to `balanced` (Max) / `lean` (API), cap Round-2 fable pairs | Large per-deliberation | Low | Low | P1 |
| Pattern B routing → native Haiku (API) / cheap OR (Max) with current IDs | 15-40x per sub-task | Med | Med (dependency) | P2 |
| Extract dormant suites → private repo | Classification + load-surface reduction | Med | Low (reversible) | P2 |
| Refresh stale OpenRouter model IDs + review cadence | Avoids deprecated-model failures | Low | Low | P2 |

### Cost monitoring & alerting (leverage existing telemetry)

The private-repo hooks already include `cost_sink_alert.py`, `context_decay_alert.py`, `analyze_telemetry.py`. Once the hook is hardened and fail-soft, these give: per-session tier attribution, cost-sink detection (fable-on-routine), and skill-usage trending to drive the evidence-based prune. Alert thresholds: warn when session default = fable on a non-council session; warn when a single deliberation exceeds a Fable-spawn budget; monthly skill-usage review to prune zero-use skills with data.

---

## Appendix B — Config hygiene checklist (pre-ship)

- [ ] `settings.json:52` model → tier alias; resolve `[1m]` vs `CLAUDE_CODE_DISABLE_1M_CONTEXT` conflict
- [ ] Telemetry hook wrapped fail-soft + private-path existence guard (or vendored in-repo)
- [ ] Permissions allow-list matches real tooling: `Bash(python3 -m pytest *)`, `Bash(pre-commit run *)`, `Bash(gh *)`, `Write(agents/**)`, `Write(commands/**)`, `Write(skills/**)` (repo is bash/python/markdown, not npm/tsc/src)
- [ ] Introduce `settings.local.json` experiment lane; keep `settings.json` clean/verified
- [ ] Unified routing table: single source spanning Claude tiers + OpenRouter, profile-aware
- [ ] OpenRouter: wire Pattern B or gate the MCP server behind a flag; refresh stale model IDs
- [ ] Verify each config change (governance pre-commit: `pre-commit run --all-files`)
