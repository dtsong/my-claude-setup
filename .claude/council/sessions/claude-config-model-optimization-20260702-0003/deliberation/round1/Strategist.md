# Strategist Position — Claude Config & Model-Routing Optimization

**Core recommendation:** Ship config hygiene + a unified two-account model-routing config (Claude tiers AND OpenRouter, both accounts) as the MVP; fast-follow with dormant-suite extraction. Defer OpenRouter Phase 2 lens relay and speculative new skills. Everything here fits one PRD executable by `/ship` in issue-sized chunks.

**Key argument:**
The highest value-per-effort lives in the config-hygiene fixes, because they touch every single session and cost minutes to fix. The uncommitted `settings.json` diff pins `model: "claude-fable-5[1m]"` (a pinned ID + 1M suffix) while `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` is still set: a direct conflict, and it violates the repo's own "tier aliases, never pinned IDs" rule (the engine already recognizes the `fable` alias). The permissions allow-list is npm/tsc/git-centric and scopes `Write(src/**)`/`Write(tests/**)` to directories this repo does not use (it writes to `skills/`, `agents/`, `commands/`, `mcp/`) so it generates permission friction on the actual workload. These are RICE 400-2000 fixes. The routing deliverable is NOT a greenfield build: Phase 1 OpenRouter (`consult` + `routed_consult` + `model-routing.json`) is already implemented and its recent commits are pushed. What is missing is (a) current model IDs (the config still names 2024-era `openai/gpt-4o-mini` and `google/gemini-flash-1.5`) and (b) a single documented routing table that spans EVERY spawn site (session default, council lean/balanced/max, `/ship`, `/looper`, subagents, OpenRouter task-classes) for BOTH the Max-plan account (quality ceiling / rate-limit efficiency) and the API-billed account ($/session). The engine's existing lean/balanced/max table is the seed; extend it, do not reinvent it. Dormant-suite extraction (15 ece-* agents, `/ece`, ece/resume-tailor/docx-to-pdf/soc-security skills) is real but low-value/low-urgency: those suites are cheap at rest and the user only wants a record preserved, so it is a clean v1.1, not a launch blocker.

**Risks if ignored:**
- Shipping the whole thing at once (including the 5-day Phase 2 lens relay whose target file `council-deliberate.js` does not even exist in this repo) blows the timeline and buries the 15-minute fixes that remove daily friction.
- Building new "workload-gap" skills speculatively before confirming actual gaps (TS/React is already covered by vercel-react-best-practices + web-design-guidelines + frontend-qa) is effort spent on unvalidated demand.
- Leaving the model pin + 1M conflict live risks a silent config error or degraded context behavior on every session until noticed.

**Dependencies on other agents' domains:**
- **Architect:** validate the unified routing-config shape (one `model-routing.json` covering Claude tiers + OpenRouter task-classes + spawn sites, two account profiles) and whether the Phase 2 relay belongs in scope at all given the missing workflow file.
- **Skeptic/Guardian:** confirm the telemetry hook's fail-soft behavior and the cross-repo dependency risk (private repo fires on every tool call × 5 events) before I rank hardening as Should vs Must.
- **Accountant/Operator:** current per-token $ for Fable 5 / Opus 4.8 / Sonnet 5 / Haiku 4.5 and OpenRouter cheap models to calibrate the API-lean profile.
- **Chronicler:** the 2026-06 handover is stale (says Phase 1 not done, commits unpushed — both false); confirm current reality before the PRD cites it.

---

## Appendix A — MoSCoW Scoping

Candidate improvements enumerated across the four outcome areas (config hygiene, model routing, skill gaps/pruning, harness leverage).

| ID | Improvement | MoSCoW | Effort | Value | Quadrant | Phase |
|----|-------------|--------|--------|-------|----------|-------|
| F1 | Fix session model: `claude-fable-5[1m]` → `fable` alias; resolve 1M-context conflict | Must | XS | High | Quick Win | v1 |
| F2 | Rewrite permissions allow-list to actual workload (bash/python/md/gh); fix Write scopes | Must | S | High | Quick Win | v1 |
| F4 | Refresh `model-routing.json` cheap-model IDs to 2026 models | Must | XS | High | Quick Win | v1 |
| F5 | Unified two-account routing design (Max ceiling vs API-lean) across ALL spawn sites | Must | M | High | Strategic Bet | v1 |
| F3 | Harden/guard telemetry hook (private-repo dep, fires every tool call × 5 events) | Should | M | Medium | Fill-in | v1.1 |
| F7 | Extract dormant suites (ECE/resume/docx/soc) to private repo + registry record | Should | M | Medium | Fill-in | v1.1 |
| F9 | Harness-leverage adoption (Task tracking, worktrees, /schedule) | Could | M | Low | Fill-in | v2 |
| F10 | Registry usage-tracking fix (already largely working — 10 skills logged this session) | Could | S | Low | Fill-in | v2 |
| F8 | New workload-aligned skills (data/ML gaps) — validate gap first | Won't (now) | L | Medium | Avoid until validated | Future |
| F6 | OpenRouter Phase 2 lens relay (target `council-deliberate.js` absent locally) | Won't (now) | XL | Medium | Strategic Bet | Future |

**Value-Effort Matrix:**
```
  High Value │  F5 (routing design)            F1, F2, F4 (config fixes)
             │  [Strategic Bet]                [Quick Wins]
  ───────────┼──────────────────────────────────────────────────
             │  F6, F8                          F3, F7, F9, F10
             │  [Avoid/Defer]                   [Fill-ins]
  Low Value  │
             └──────────────────────────────────────────────────
               High Effort  ←──────────────────→  Low Effort
```

**MVP Feature Set (v1):** F1, F2, F4 (Quick Wins) + F5 (the core routing deliverable).
**MVP cut-line rationale:** v1 = every change that is either near-zero-effort-high-frequency (F1/F2/F4 touch every session) or the irreducible core deliverable the PRD exists for (F5). F3/F7 are safe fast-follows. F6/F8 are high-effort and/or unvalidated — explicitly out of this PRD.

**Phase Roadmap:**
| Phase | Features | Milestone | Decision Point |
|-------|----------|-----------|----------------|
| v1 | F1, F2, F4, F5 | Correct, safe config + one routing doc shipped via /ship | Validate routing on one real /ship + one council run |
| v1.1 | F3, F7 | Hook hardened; dormant suites extracted w/ record | Confirm no telemetry regressions; registry stub resolves |
| v2 | F9, F10 | Harness features adopted; tracking polished | Re-check whether F8/F6 demand is real |
| Future | F8, F6 | Only if usage data shows the gap / multi-vendor need | — |

## Appendix B — RICE Scoring

Reach = share of a nominal 100 sessions/quarter affected. Effort = person-days (solo operator, executed via `/ship`).

| ID | Improvement | Reach | Impact | Conf | Effort | RICE | Tier |
|----|-------------|-------|--------|------|--------|------|------|
| F1 | Model pin + 1M fix | 100 | 2 | 100% | 0.1 | 2000 | 1 |
| F2 | Permissions allow-list rewrite | 100 | 1 | 80% | 0.2 | 400 | 1 |
| F4 | Refresh cheap-model IDs | 30 | 2 | 80% | 0.2 | 240 | 1 |
| F3 | Harden telemetry hook | 100 | 1.5 | 60% | 0.5 | 180 | 2 |
| F5 | Unified routing design (2 accounts) | 80 | 2 | 80% | 1.0 | 128 | 2 |
| F7 | Extract dormant suites | 40 | 1 | 90% | 1.0 | 36 | 3 |
| F9 | Harness-leverage adoption | 50 | 1 | 50% | 1.0 | 25 | 3 |
| F10 | Registry tracking fix | 10 | 0.5 | 70% | 0.5 | 7 | 4 |
| F8 | New data/ML skills | 20 | 1.5 | 40% | 3.0 | 4 | 4 |
| F6 | OpenRouter Phase 2 relay | 15 | 2 | 50% | 5.0 | 3 | 4 |

**Priority-ranked:** F1 → F2 → F4 → F3 → F5 → F7 → F9 → F10 → F8 → F6.

**Quick Wins vs Strategic Bets:**
| Category | Features | Note |
|----------|----------|------|
| Quick Wins | F1, F2, F4 | High RICE, <0.25 day each — do first, same PR possible |
| Strategic Bets | F5 | High value, 1 day — the deliverable core |
| Low-Hanging Fruit | F3, F7 | Medium RICE, ~0.5-1 day — v1.1 |
| Money Pits | F6, F8 | Low RICE, high effort — defer/reconsider |

**Success metrics:**
| Feature | Primary metric | Target | Guardrail |
|---------|----------------|--------|-----------|
| F1 | Config-conflict count in settings.json | 0 | No 1M-context regression |
| F2 | Permission prompts per session on real workload | -50% | No over-broad Bash allow |
| F4/F5 | Spawn sites with explicit documented routing (both accounts) | 100% | Fail-soft to Claude preserved |
| F7 | Dormant suites resident locally / record preserved | 0 resident, 1 record | No broken skill-loader refs |

## Appendix C — Verified corrections to the intake scan
- Phase 1 OpenRouter is IMPLEMENTED: `mcp/openrouter/{server,routing,openrouter_client}.py` + tests exist; `routed_consult` present; recent commits (898174d, 4d40c2c) are its fixes.
- `skills/council/model-routing.json` EXISTS; `tasks` populated with STALE IDs (`openai/gpt-4o-mini`, `google/gemini-flash-1.5`); `lenses` empty; defaults route to `claude`. Refresh needed (F4).
- Commits are PUSHED (`git log origin/main..HEAD` empty) — handover's "5 unpushed" is stale.
- `.claude/workflows/council-deliberate.js` (Phase 2 relay target) does NOT exist in this repo → F6 effort/uncertainty is higher than the spec implies.
- Registry tracking WORKS: 10 skills logged `uses:1` this session; "no data" is because the system is new, not broken → F10 is low priority.
- Telemetry hook `$HOME/Development/my-claude-setup-private/hooks/session_telemetry.py` exists (7 KB) and is wired to 5 events, firing per tool call → cross-repo coupling + per-call python startup is the F3 concern.
