# Architect Position — Claude Config & Model-Routing Optimization

**Core recommendation:** Treat model routing as ONE data model with a single source of truth (`skills/council/model-routing.json`, extended), keyed by spawn site and parameterized by an account-profile dimension (`max-plan` vs `api-billed`); everything else (settings default, council cost profiles, OpenRouter task/lens routing, /ship + /looper) reads from that one table instead of the three disconnected routing surfaces that exist today. Fix the settings.json contract violation first (pinned `claude-fable-5[1m]` vs tier-alias governance + the `[1m]`↔`DISABLE_1M_CONTEXT=1` conflict), then consolidate.

**Key argument:**
Routing is currently fragmented across three surfaces with three incompatible vocabularies, and none of them reference each other:

| Surface | Location | Vocabulary | Scope |
|---------|----------|-----------|-------|
| Session default | `settings.json` → `model` | pinned ID `claude-fable-5[1m]` | main loop |
| Council spawn routing | `_council-engine.md` cost-profile table | tier aliases (`sonnet`/`opus`/`fable`), prose markdown | council/ece agents |
| OpenRouter routing | `skills/council/model-routing.json` | OpenRouter IDs (`openai/...`) | Pattern B tasks / Pattern A lenses |

This is the classic data-gravity failure: the same decision ("which model runs here") is expressed in three places, so it can never stay consistent. The uncommitted settings diff is the first casualty. It pins `claude-fable-5[1m]`, which (a) violates the repo's own governance rule ("always use tier aliases, never pinned `claude-*` IDs — they go stale, the validator rejects them") and (b) carries the `[1m]` 1M-context suffix while `env.CLAUDE_CODE_DISABLE_1M_CONTEXT=1` explicitly disables 1M context — a self-canceling contract. The fix is structural, not cosmetic: promote `model-routing.json` into the single routing table. Add a `tiers` map (alias → concrete provider model, resolved per account profile) and a `profiles` object (`max-plan`: quality-ceiling, rate-limit-efficient; `api-billed`: cost-per-session, Sonnet/Haiku-weighted). The council engine already routes by spawn site — that table just needs to be machine-readable and shared rather than duplicated in prose. Set `settings.json.model` back to the `opus` (or `fable`) tier alias and let the routing config own the concrete IDs. This gives you the one system across Claude tiers + OpenRouter the interview asked for, and makes the Max-vs-API split a single config dimension instead of a fork.

Second structural issue independent of routing: the telemetry hook fires `python3 $HOME/Development/my-claude-setup-private/hooks/session_telemetry.py` on FIVE lifecycle events (SessionStart/PostToolUse/PostToolUseFailure/Stop/SessionEnd) — a hard cross-repo boundary crossing on every single tool call. The private script exists today, but this is a fragile seam: if that repo is absent/moved, every session degrades. It also means the council registry's usage tracking (67 skills, only 10 recorded uses, all from this session) is NOT wired to real runs — the telemetry loop is open, so pruning cannot be data-driven yet. Either close the loop (telemetry writes registry uses) or accept that pruning proceeds on workload-fit heuristics, not usage counts.

**Risks if ignored:**
- **Structural/data:** Three routing surfaces drift permanently; a model rename (Fable 5 → Fable 6) requires edits in 3 vocabularies across N files, and the validator will reject pinned IDs the next commit — CI breakage baked in.
- **Performance/scalability:** The 5-event private-repo telemetry hook adds a python3 process spawn to every tool call; on a fullscreen high-effort session that is thousands of subprocess launches, and a missing/renamed private repo silently degrades or errors every session lifecycle event.
- **Integration/migration:** OpenRouter Phase 2 (lens relay) hard-codes lens→model mapping in a table that today only holds tasks; without the unified schema, Phase 2 adds a fourth routing surface instead of extending the third. Pruning dormant suites (ECE 15 agents ~17K words, resume-tailor, docx-to-pdf, soc-security) without a left-behind manifest loses the record the user wants to preserve.

**Dependencies on other domains:**
- **Skeptic/Guardian:** threat-model the OpenRouter key path and the fail-soft behavior of the private telemetry hook; validate that pinned-ID staleness is a real CI failure mode.
- **Craftsman/Artisan:** implement the routing-config loader + schema, the settings.json revert, and the permissions allow-list fix (currently npm/tsc/git-centric; this repo is bash/python/markdown — missing `Bash(python3 *)`, `Bash(pytest *)`, `Bash(pre-commit *)`, `Bash(gh *)`, and `Write(src/**|tests/**)` scoping that excludes the actual `agents/skills/commands/` write targets).
- **Steward/Strategist:** own the pruning-aggression decision and the extract-to-private-repo call; decide whether telemetry loop-closing is worth the per-tool-call cost.
- **Accountant/Operator:** build the per-session cost model for the API-billed account that the `profiles.api-billed` tier map depends on.
- **Advocate:** DX of profile switching (a `--profile` already exists on council; a global account-profile needs a discoverable surface).

---

## Appendix — Context Briefing (codebase-context skill output)

### Tech Stack
- **Runtime substrate:** Claude Code harness config-as-code (agents/commands/skills as markdown, hooks as bash, MCP as python).
- **Languages:** bash (hooks, statusline via bun), Python 3.14 (OpenRouter MCP server, telemetry), markdown-as-code.
- **Tooling:** pre-commit (governance enforcement), gh CLI, pytest 9, bun (claude-hud statusline).
- **Model landscape (2026-07):** Fable 5 (`claude-fable-5`, frontier, current session), Opus 4.8 (`claude-opus-4-8`), Sonnet 5 (`claude-sonnet-5`), Haiku 4.5 (`claude-haiku-4-5-20251001`), plus OpenRouter non-Claude (`openai/gpt-4o-mini`, `google/gemini-flash-1.5`).

### Directory Structure
```
agents/       23 council-* + 15 ece-*  (persona files, ~17K words in ece alone)
commands/     ~30 (_council-engine, council, ece, ship, looper, ralf, roadmap-executor, ...)
skills/       ~22 suites (council [~60 skills/22 depts], ece, dbt, soc-security,
              resume-tailor, docx-to-pdf, data-engineering, research-consulting,
              frontend-qa, prompt-wizard, web-*, cicd/docker/helm-generation)
hooks/        acceptance-gate.sh (PreToolUse/TaskUpdate), + careful/freeze/pre-compact/skill-telemetry
mcp/openrouter/  Phase 1 SHIPPED (PR #55): server.py, openrouter_client.py, routing.py, tests
pipeline/specs/  SKILL-GOVERNANCE-SPEC.md (token budgets, pre-commit enforced)
docs/superpowers/  openrouter spec (approved) + phase1 plan
memory/       session handovers
```

### Architectural Patterns
- **Routing:** file-based command dispatch; `_council-engine.md` is a theme-agnostic orchestration core, `council.md`/`ece.md` inject theme vars. Cost profiles (lean/balanced/max) route models by spawn site.
- **Orchestration backend:** degradation chain workflow → teams → sequential; `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1` enables teams.
- **State:** session dirs under `.claude/council/sessions/`; registry.json as cross-session system-of-record; ship uses a state file with per-issue status machine.
- **Governance:** token budgets enforced via pre-commit (coordinator ≤800, specialist ≤2000, reference ≤1500 tokens, ≤5000 simultaneous load).

### Data Model (config entities)
| Entity | Key Fields | Relationships |
|--------|-----------|---------------|
| `settings.json` | model, env, permissions, hooks, mcpServers, enabledPlugins | root config; symlinked from `~/.claude/settings.json` |
| `model-routing.json` | tasks{}, lenses{}, defaults{lens,fallback} | consumed by OpenRouter `routed_consult`; NOT yet by engine/settings |
| council `registry.json` | version 2.1, departments{skills{uses,last_used,sessions}} | 67 skills, 10 uses (all this session) — tracking exists, data does not |
| cost-profile table | spawn-site × {lean,balanced,max} → tier alias | prose in `_council-engine.md`, NOT machine-readable |

### Integration Points
| Service | Purpose | Auth Method |
|---------|---------|-------------|
| OpenRouter | non-Claude models (Pattern A lenses, Pattern B cheap tasks) | `OPENROUTER_API_KEY` env, fail-soft |
| private telemetry repo | session/tool-use metrics on 5 lifecycle hooks | filesystem path `$HOME/Development/my-claude-setup-private` |
| GitHub (gh) | /ship issue export + PR merge | gh CLI auth |
| context7 MCP + others | library docs, plugins | plugin marketplace |

### Warnings / Tech Debt
- **settings.json (uncommitted):** pinned `claude-fable-5[1m]` violates tier-alias governance; `[1m]` conflicts with `CLAUDE_CODE_DISABLE_1M_CONTEXT=1`.
- **Routing fragmentation:** 3 surfaces, 3 vocabularies, no shared source of truth.
- **Private-repo hook:** hard cross-repo dependency on every tool call × 5 events.
- **Registry telemetry loop is open:** usage data absent → pruning not data-driven.
- **Permissions allow-list mismatch:** npm/tsc/git-centric vs a bash/python/markdown repo; `Write` scoped to src/tests that this repo doesn't use.
- **model-routing.json OpenRouter IDs:** `gpt-4o-mini`, `gemini-flash-1.5` are placeholder-era picks; revisit against 2026-07 cheap-model landscape.
