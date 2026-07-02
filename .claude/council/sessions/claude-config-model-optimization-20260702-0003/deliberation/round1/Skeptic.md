# Skeptic Position — Claude Config & Model-Routing Optimization

**Core recommendation:** Do not prune skills on zero-use data (the tracking only started this session, so zero-use is a measurement artifact, not evidence of uselessness) and do not treat the OpenRouter routing layer as free: `consult()` egresses council/code context to third-party vendors and, on the Max plan, converts rate-limited "free" Claude calls into billed OpenRouter calls. Ship config hygiene and routing as reversible, validated changes, gated behind a settings.json validator because that file is the live symlinked harness config.

**Key argument:**
The plan's four workstreams each rest on an unvalidated assumption. (1) *Routing:* `model-routing.json` already exists (contradicting the handover) and pins 2024-era cheap IDs (`openai/gpt-4o-mini`, `google/gemini-flash-1.5`) that are stale in 2026-07; more importantly `consult()` forwards `system + prompt` verbatim to OpenRouter and onward to OpenAI/Google, crossing the Claude trust boundary with zero redaction or send-allowlist. (2) *Pruning:* 57 of 67 council skills show zero uses, but the two skills that show `uses:1` are exactly the ones this very session touched (`codebase-context`, `threat-model`) which proves the counter is newborn. Deleting on that signal is Chesterton's-fence deletion. (3) *Config hygiene:* the new model is a pinned ID `claude-fable-5[1m]` that violates the repo's own "tier aliases, never pinned IDs" rule AND requests a 1M context that `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` explicitly disables (silent conflict). settings.json is symlinked to `~/.claude/settings.json`, so a malformed edit live-breaks the running harness with no validation gate. (4) *Harness leverage:* the telemetry hook fires on *every* PostToolUse from a hard-coded private-repo path (`$HOME/Development/my-claude-setup-private/hooks/session_telemetry.py`); if that repo is absent/moved/renamed, every tool call in every session raises a hook error, and any public clone of this repo is broken out of the box.

**Risks if ignored:**
- **[Critical — data/trust boundary]** OpenRouter `consult()` sends full council persona prompts and any embedded code/context to third-party vendors with no redaction and no allowlist of what may leave. A council lens relay (Phase 2) reasoning over sensitive repo content = uncontrolled data egress to OpenAI/Google. Mitigation: define a send-allowlist / redaction pass, forbid routing any task that carries file contents or secrets, and document the egress explicitly in the PRD.
- **[High — cost/economics]** On the **Max plan**, Pattern B routing cheap tasks to OpenRouter *replaces rate-limited-but-dollar-free Claude Haiku calls with billed OpenRouter calls* — economically backwards unless the explicit goal is rate-limit relief. On the **API account**, a routing-config typo or fallback misfire that sends high-volume subtasks to a frontier model instead of a mini model = runaway spend with no budget cap. Mitigation: on Max, prefer `claude-haiku-4-5` for cheap tasks (free under rate limits); add a per-model cost ceiling / max_tokens clamp; alert on routed-call volume.
- **[High — reliability/portability]** Telemetry hook is a hard cross-repo dependency firing on every tool use; a missing private repo turns every session into an error stream, and the public repo is non-portable. `[1m]` suffix vs `DISABLE_1M_CONTEXT=1` is a live config contradiction. Mitigation: guard the hook command (`[ -f <path> ] && python3 …`), or vendor a no-op stub; resolve the 1M conflict (drop the suffix or flip the env var); add a pre-commit JSON-schema validator for settings.json before the symlink serves it.
- **[Medium — scope/pruning]** ECE extraction (15 agents + `/ece` command + `ece` skill) and dormant-suite removal risk dangling references: `/ece` command body, registry.json entries, and any council/registry cross-links break if migration is non-atomic. Mitigation: grep every reference before moving, migrate in one commit, keep a manifest record, and gate deletion on real telemetry (>=30 days) not the newborn counter.

**Dependencies on other agents' domains:**
- **Architect:** owns the single-routing-system abstraction (Claude tiers + OpenRouter under one config) and the ECE-extraction migration boundary. I need the routing schema to carry an explicit `fallback` + cost-ceiling field and a documented trust-boundary annotation per task class.
- **Craftsman/Operator:** owns the settings.json validator (pre-commit JSON-schema + symlink safety) and the telemetry-hook guard. I need these as non-negotiable safeguards before any hygiene change merges.
- **Pragmatist:** owns the prune-vs-keep economics. I concede low token-cost-at-rest makes keeping tolerable; I need agreement that deletion waits for real usage data, extraction is atomic, and a record survives.
- **Conductor/Ship:** the PRD must carry each mitigation as an acceptance criterion so the acceptance-gate hook actually enforces them.

---

## Appendix A — Failure Mode Analysis

### Failure Mode Table
| Component | Failure Mode | Severity | Cascade Risk | Mitigation | Monitoring Signal |
|---|---|---|---|---|---|
| settings.json (symlinked to ~/.claude) | Malformed JSON / bad key written live | Critical | Running harness reads broken config mid-session; new sessions may fail to start | Pre-commit JSON-schema validate before commit; never hand-edit the symlink target without validation | Harness startup error; `jq . settings.json` in CI |
| `model: claude-fable-5[1m]` vs `DISABLE_1M_CONTEXT=1` | Silent conflict; 1M request ignored or errors | High | User believes 1M context active; long-context tasks silently truncate | Resolve to one source of truth; drop `[1m]` or set env to 0; use tier alias `opus`/`fable` per governance | Context-window assertion in a smoke session |
| session_telemetry.py (private-repo path) | Private repo absent/moved/renamed | High | Every PostToolUse/Stop/SessionStart fires a failing hook -> error noise every tool call; public clone unusable | Guard: `[ -f PATH ] && python3 PATH`; or vendor no-op stub; make path relative/optional | Hook stderr rate; count of PostToolUseFailure |
| OpenRouter `consult()` | API down / 4xx / 5xx / timeout / missing key | Low (by design) | None — fails soft to Claude fallback (verified in client) | Already handled: structured `fallback:"claude"` | Log `error_kind` frequency; fallback-rate metric |
| model-routing.json | Stale/invalid model ID (gpt-4o-mini, gemini-flash-1.5 in 2026) | Medium | OpenRouter 404s the model -> every routed call falls back to Claude -> Pattern B savings silently = 0 | Validate model IDs against `GET /api/v1/models` at load; pin current-gen cheap IDs; CI check | Fallback-rate spike; routed-call success ratio |
| Pattern A Claude relay agent | Relay spawns but MCP unreachable in sandbox | Medium | Lens returns fallback Claude output -> cross-vendor diversity silently lost, deliberation looks fine | Assert relay received non-fallback text; log per-lens actual model used | Per-lens `model` field in output vs configured |
| Routing config (API account) | Typo routes high-volume task to frontier model | High | Runaway token spend, no cap | Per-task max_tokens clamp + cost ceiling; deny frontier IDs in `tasks` block | Daily spend alert; token-per-task histogram |
| ECE / dormant-suite extraction | Non-atomic move leaves dangling refs | Medium | `/ece`, registry entries, cross-links 404; council engine may fail to resolve a skill | grep all refs; single-commit migration; manifest | Pre-commit reference-integrity hook (already exists per governance) |
| Pruning on zero-use counter | Delete skill that is actually used but untracked | Medium | Lost capability; rebuild cost | Gate on >=30d real telemetry, not newborn counter; keep archive | Registry age vs first-tracked date |

### Cascade Diagram
```
[private-repo telemetry path missing]
  ├── PostToolUse hook — fails on EVERY tool call (error noise)
  ├── SessionStart/Stop/SessionEnd — fail (session boundary errors)
  └── public clone of repo — unusable out of the box (hard dependency)

[settings.json malformed (live symlink)]
  ├── running session — reads broken config mid-work
  └── next SessionStart — may fail to launch harness

[stale OpenRouter model IDs]
  ├── every routed cheap task — 404 -> Claude fallback
  └── Pattern B cost savings — silently 0 (looks like it "works")
```

### Rollback Checklist
- [ ] Feature flag to disable OpenRouter routing: set `defaults.fallback=claude` + empty `tasks` map (all routing off)
- [ ] settings.json rollback: `git checkout settings.json` (reversible; symlink picks up immediately)
- [ ] Telemetry hook disable: comment out hook blocks or point to no-op stub
- [ ] ECE extraction rollback: revert the single migration commit; refs restore atomically
- [ ] Data cleanup: none (no destructive data ops if pruning is deferred)
- [ ] Communication: single-user repo — note in memory/HANDOVER

## Appendix B — Threat Model (STRIDE)

### Trust Boundary Diagram
```
┌─────────────────────────────────────────────┐
│ Trust Boundary: Local Claude Code harness     │
│  agents/ commands/ skills/ hooks/             │
│  council deliberation content, repo code       │
└───────┬───────────────────────┬───────────────┘
        │ MCP consult()          │ hook exec (env-passed key)
        ▼                        ▼
   [OpenRouter API] ──▶ [OpenAI / Google vendor models]   [private-repo python hook]
   (3rd-party egress: system+prompt leave boundary)
```

### Threat Table
| STRIDE | Threat | Risk | Mitigation | Status |
|---|---|---|---|---|
| Information Disclosure | `consult()` forwards `system`+`prompt` (may embed code, council context, repo internals) to OpenRouter -> onward to vendor models; no redaction, no send-allowlist | **Critical** | Define allowlist of task classes permitted to egress; forbid routing tasks carrying file contents/secrets; redaction pass; document egress in PRD | Open |
| Information Disclosure | `OPENROUTER_API_KEY` in shell env is passed into MCP subprocess env; any code the MCP process loads can read it | High | Deny-list already blocks reading `.env`/keys, but env-var exposure is separate; scope key to minimum; rotate; consider a secrets file with restricted perms over broad env | Open |
| Elevation of Privilege | `skipDangerousModePermissionPrompt` + `skipAutoPermissionPrompt` + `defaultMode:acceptEdits` = broad auto-accept; a malicious/errant skill or MCP tool acts with little friction | High | Keep deny-list tight (rm -rf, sudo, chmod, curl\|sh, wget, publish already denied — good); reconsider auto-accept breadth for MCP-originated actions | Open (partially mitigated) |
| Tampering | settings.json is symlinked and live; anything that writes it changes the running harness config with no validation | High | Pre-commit JSON-schema validation; treat symlink target as protected | Open |
| Denial of Service (self-inflicted / cost) | Misrouted high-volume task on API account -> unbounded spend; on Max -> rate-limit exhaustion by frontier Fable + fullscreen + effortLevel:high defaults | High | Per-model cost ceiling + max_tokens clamp; prefer Haiku for cheap tasks; reserve frontier for synthesis | Open |
| Spoofing / Repudiation | Pattern A relay may silently return Claude fallback while claiming a vendor lens; no audit of which model actually answered | Medium | Log actual `model` field per lens; assert non-fallback; surface in deliberation record | Open |
| Tampering | Permission `allow` list is npm/tsc/git-centric but repo is bash/python/markdown; `chmod` is denied yet new hooks need +x -> friction may push user to loosen deny-list dangerously | Medium | Right-size allow-list to actual workload (python3, pre-commit, gh, bun); handle hook +x via git mode bits, not runtime chmod | Open |

### Residual Risk Summary
- OpenRouter egress: even with an allowlist, any routed task inherently leaks *some* prompt text to a third party. Accepted only for non-sensitive task classes (classification, scoring on non-proprietary text); monitor fallback/egress volume.
- Auto-accept posture: accepted for a trusted single-user local repo; revisit if untrusted skills/MCP servers are added.
- Fail-soft OpenRouter client is genuinely well-built (structured fallback, transport-injectable, no unhandled raises) — low residual reliability risk on the client itself.
