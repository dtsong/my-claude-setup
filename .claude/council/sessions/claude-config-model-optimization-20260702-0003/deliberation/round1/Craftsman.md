# Craftsman Position — Claude Config & Model-Routing Optimization

**Core recommendation:** Unify model routing into one schema-validated source of truth (Claude tier aliases + OpenRouter IDs in the same system), fix the settings.json hygiene defects that violate this repo's own governance, and treat the "zero-use" skill registry as a broken instrument, not evidence, so pruning/extraction is grounded in workload fit rather than phantom telemetry.

## Key argument

This repo is unusually disciplined about patterns (token budgets enforced by pre-commit, tier-alias-only routing, department isolation), and the highest-value moves are the ones that stop the config from contradicting its own rules. Three concrete pattern violations are live right now:

1. **The uncommitted settings.json breaks the repo's own routing rule.** `_council-engine.md:105` states: "Always use tier aliases (`sonnet`, `opus`, `fable`) — never pinned `claude-*` model IDs (they go stale; the validator rejects them in agent frontmatter)." The diff sets `"model": "claude-fable-5[1m]"` — a pinned ID. Worse, the `[1m]` (1M-context) suffix directly contradicts `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` still set in `env`. That is two contradictory signals in one file: the pit of failure. Use an alias (`"fable"` / `"default"`) and reconcile the 1M flag (drop the suffix or flip the env var) so the easy path is the correct path.

2. **The permissions allow-list describes an imagined TypeScript project, not this repo.** The allow-list is entirely npm/tsc/git (`Bash(npm run *)`, `Bash(npx tsc *)`, `Write(src/**)`, `Write(tests/**)`). This repo's real workload is bash/python/markdown: pre-commit, pytest, python3 (MCP server + pipeline hooks), gh, jq, and Writes to `agents/ commands/ skills/ hooks/ pipeline/`. None of those are allowlisted, so `skipAutoPermissionPrompt` is silently masking a mismatch instead of the allow-list encoding intent. This is a DX and safety smell: the allow-list should describe what this repo actually does.

3. **The usage tracking that would justify pruning is not wired and measures the wrong thing.** `hooks/skill-telemetry.sh` exists but appears **zero times** in `settings.json` (only `acceptance-gate.sh` and the private-repo `session_telemetry.py` are registered). Even if wired, it only logs `Skill`-tool invocations — but council skills are consumed by **inlining `skillContent` via file reads** in `_council-engine.md` Phase 2.5, which never triggers the Skill tool. And `registry.json` "uses" are hand-incremented (this very session bumped a handful to `1`). So "60+ skills, zero uses" is a **measurement artifact, not dormancy**. Pruning council skills on this data would be deleting code because the odometer was unplugged. Fix the instrument first, or prune explicitly on workload-fit judgment and label it as such.

On the pattern-analysis findings (appendix), the corpus is genuinely healthy on token budgets: no specialist/standalone `SKILL.md` exceeds ~1,500 words (largest is `alchemist/ml-workflow` at 1,407 words / ~1,870 tok, under the 2,000-tok cap). That discipline is a strength to preserve through any pruning: extraction should keep the surviving corpus equally clean.

**Routing as one system.** The council engine already has a mature spawn-site routing matrix (`lean/balanced/max` keyed by spawn site, tier aliases only). `model-routing.json` is a *second, thinner* config using vendor IDs (`openai/gpt-4o-mini`, `google/gemini-flash-1.5` — both stale by 2026-07). Two routing configs is pattern drift. The maintainable design is one documented schema covering every spawn site (session default, brainstorm/council/round-2/audit agents, /ship + /looper pipelines, OpenRouter Pattern A lens relay + Pattern B task classes) with a validation test that rejects pinned `claude-*` IDs in Claude-tier slots, flags stale OpenRouter IDs, and asserts every spawn site has an entry for every profile. Types-as-documentation: a JSON Schema for the routing file makes the correct thing the only thing that validates.

**Extraction disposition (maintainability lens).** ECE is a fully populated, cleanly isolated suite (15 `ece-*` agents / ~120 KB, 15 skill departments + its own `registry.json`, plus the 266-line `/ece` command) that mirrors the council structure. It is a low-risk extraction to a private "attic" repo — the one coupling to verify is whether `/ece` reuses `_council-engine.md` (shared deliberation engine) or duplicates it; that boundary must be settled before the cut. `resume-tailor`, `docx-to-pdf`, `soc-security` are standalone with no council coupling and are trivial to extract; `docx-to-pdf` is cheap and generically useful, so keeping it local is defensible. Because skills only load on trigger, at-rest cost is near zero — so extraction-with-a-pointer beats aggressive deletion, and preserves the record the user wants.

## Risks if ignored

- **Regression / silent-wrong-behavior:** the pinned-ID + 1M-suffix vs `DISABLE_1M_CONTEXT=1` contradiction means the effective context window and model are ambiguous; a future model rename leaves the session pinned to a stale ID with no validator catching a *settings* file (the validator only guards agent frontmatter).
- **Velocity / DX drag:** an allow-list that doesn't match the workload plus an every-tool-use hook bound to an optional private repo (`session_telemetry.py` on SessionStart/PostToolUse/PostToolUseFailure/Stop/SessionEnd) means a fresh clone or second machine spawns a failing `python3` on the critical path of *every* tool call — latency and noise, and a fast-feedback-loop killer if it isn't fail-soft.
- **Irreversible pruning on bad data:** deleting skills/agents because the (unwired, wrong-layer) telemetry shows zero uses destroys work that was never actually measured; consistency and recoverability both suffer.

## Dependencies on other domains

- **Architect:** the unified routing schema / source-of-truth structure, and the ECE extraction module boundary (is `_council-engine` shared or duplicated by `/ece`?).
- **Accountant / Tuner (cost + latency):** concrete 2026 OpenRouter model IDs and $/token so I can write validation thresholds and the Max-plan vs API-billed default profiles; without real IDs the routing config stays stale.
- **Cipher / Guardian (security):** `OPENROUTER_API_KEY` handling and making the private-repo telemetry hook dependency safe (guarded/fail-soft) before it fires on every tool.
- **Strategist:** workload-fit ranking (TS/React web, data/ML, meta-repo) to ground pruning judgment, since usage data is void and I refuse to prune on it.

---

## Appendix A — Pattern & Convention Audit (pattern-analysis skill output)

### Pattern Inventory

| Category | Pattern | Example File | Frequency | Status |
|----------|---------|--------------|-----------|--------|
| File naming | kebab-case for agents/commands/skills | `agents/council-craftsman.md`, `commands/_council-engine.md` | High | Standard |
| Agent frontmatter | `name` + `description` YAML, then persona prose | `agents/council-craftsman.md`, `agents/ece-analog.md` | High | Standard |
| Skill frontmatter | `name/department/description/version/triggers` | `skills/council/craftsman/pattern-analysis/SKILL.md` | High | Standard |
| Skill structure | Purpose → Scope → Procedure → Output → Quality Checks | council specialist skills | High | Standard |
| Token budget | Specialist/standalone SKILL.md ≤~1,500 words | all audited (max 1,407) | High | Compliant |
| Model routing (Claude) | Tier aliases keyed by spawn site | `_council-engine.md:97-105` | High | Standard |
| Model routing (OpenRouter) | Vendor IDs in separate `model-routing.json` | `skills/council/model-routing.json` | Low (1 file) | **Divergent** |
| Suite composition | department = agent + skill dir + registry entry | council/*, ece/* | High | Standard |
| Governance enforcement | pre-commit: frontmatter/refs/isolation/context-load (hard), token-budget/prose (warn) | `.pre-commit-config.yaml` | Repo-wide | Standard |
| Usage telemetry | `Skill`-tool JSONL logger, unwired + wrong layer for council | `hooks/skill-telemetry.sh` | 0 (not registered) | **Broken** |

### Consistency Report (proposed / observed changes)

| Change | Existing Pattern | Match? | Recommendation |
|--------|-----------------|--------|----------------|
| `model: "claude-fable-5[1m]"` | tier aliases only (`_council-engine.md:105`) | **No** | Use `"fable"`/`"default"` alias; reconcile with `DISABLE_1M_CONTEXT`. |
| `[1m]` suffix + `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` | single coherent context signal | **No** | Pick one; remove the contradiction. |
| Two routing configs (engine table + `model-routing.json`) | one routing source | **No** | Unify under one schema-validated file. |
| Prune on `registry.json` zero-uses | evidence-based change | **No** | Instrument correctly OR prune on labeled workload judgment. |
| npm/tsc/git allow-list | permissions describe real workload | **No** | Add python3/pre-commit/pytest/gh/jq + repo Write globs. |

### Recommendations

1. **Follow:** tier-alias routing (`_council-engine.md:97-105`) and the skill-structure template — extend, don't fork them.
2. **Avoid:** a second parallel routing config with stale vendor IDs; fold OpenRouter routing into the unified schema with validation.
3. **Avoid:** treating `registry.json` uses as evidence until `skill-telemetry.sh` is wired AND made aware of inlined `skillContent` (or the engine records uses directly).
4. **Refactor:** extract ECE + resume-tailor + soc-security to a private repo with a pointer/manifest; verify `/ece` vs `_council-engine` coupling first (scope: 15 agents, ~15 skill dirs, 1 command, ~120 KB).
5. **Fix:** guard the private-repo telemetry hook (existence check / fail-soft) so it never blocks the tool path on a fresh clone.

### Quality Checks

- [x] ≥3 categories audited (naming, structure, routing, governance, telemetry)
- [x] Naming conventions documented with examples
- [x] Routing pattern identified and its divergence documented
- [x] Governance/enforcement pattern identified
- [x] Proposed/observed changes evaluated against each pattern
- [x] Example files referenced for each pattern
- [x] Anti-patterns identified with rationale
- [x] Recommendations actionable
