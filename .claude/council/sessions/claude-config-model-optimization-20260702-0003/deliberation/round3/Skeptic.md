# Skeptic Final Position — Claude Config & Model-Routing Optimization

**Revised recommendation:** Ship the config-hygiene + routing-doc MVP ungated (it changes no live model behavior), but gate every *activation boundary* — first `routed_consult` caller, any OpenRouter egress, any live model flip — behind hard safeguards: a send-allowlist + ZDR/no-training flags + actual-model audit + kill switch for OpenRouter, a settings.json schema validator, and F3a (fail-soft hook guard removing the private-repo path from public settings.json) inside v1. Council-skill pruning waits for real post-fix telemetry; dormant-suite extraction proceeds now on workload judgment, atomically.

**Concessions made and why:**

1. **Egress: block → gated Trial.** I conceded that OpenRouter's platform controls (per-request ZDR enforcement, no-training flags, provider allowlists) address the *controllable* half of the trust-boundary problem that Scout surfaced. My verbatim-forwarding finding still holds (`openrouter_client.py` sends `system+prompt` with no redaction), so I move to conditional acceptance, not clearance: Pattern A may Trial on **one** lens only, behind a send-allowlist, ZDR/no-training flags, and an actual-model assertion. The trial doubles as Oracle's persona-transfer test.

2. **Eval-before-everything → eval-before-activation.** I accept Strategist/Oracle's calibration: F1 alias fix, F2 permissions, F4 stale-ID refresh, F5 routing doc alter no live model dispatch and have zero live callers, so an eval gate there is theoretical-risk blocking. The 12-case smoke set (F11) becomes the real gate at the first `routed_consult` caller; the full 38-case harness gates Phase 2 relay and any prune decision. This is the correct place for the safeguard, and I retract the demand to gate the MVP.

3. **Pruning signal is inconclusive, not damning.** Craftsman/Scout verified my Chesterton's-fence concern: committed `registry.json` shows 0/67 uses and all 10 nonzero entries were written by *this* session today. Zero-use is a measurement artifact. I concede the pruning *timeline* (Operator's 2-4 week window) is acceptable **only after** the increment is made durable and the window is scoped to the council long tail.

**Non-negotiables (must be acceptance criteria in the PRD):**

- **OpenRouter Trial gate (Critical).** No routed egress ships without: (a) a send-allowlist in `routing.py` that forbids file contents/secrets leaving the boundary; (b) ZDR + no-training flags set per request; (c) the relay logging and *asserting* the actual vendor model returned (fail if fallback silently substituted); (d) a kill switch (`defaults.fallback=claude`, empty `tasks` map). If the Trial cannot prove measurable diversity value, OpenRouter collapses to Pattern B on the API account only. Work-account code that egresses ungated is Critical and must not merge.
- **F3a in v1 (High).** The public `settings.json` must not name `$HOME/Development/my-claude-setup-private/...`; the five hook events get a fail-soft existence guard so a missing/moved private repo cannot turn every tool call into an error stream, and a public clone is not broken out of the box.
- **settings.json schema validator (High).** A pre-commit JSON-schema check runs before the symlink serves the file. The live symlink to `~/.claude/settings.json` means a malformed edit breaks the running harness with no gate today.
- **1M-context conflict resolved (High).** `claude-fable-5[1m]` vs `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` is a silent contradiction and violates the "tier aliases, never pinned IDs" governance rule. Resolve to one source of truth before F1 lands.
- **API-account cost ceiling (High).** Per-model `max_tokens` clamp + frontier-ID denylist in the `tasks` block + routed-call-volume alert. A routing typo on the dollar-billed account is runaway spend with no cap.
- **Extraction is atomic (Medium).** Dormant-suite/ECE move greps all references (`/ece` body, registry entries, cross-links), lands in one commit, keeps a manifest, and passes the reference-integrity pre-commit hook.

**Implementation notes:**

- **Max plan:** cheap tasks route to `claude-haiku-4-5` (dollar-free under rate limits), not OpenRouter — routing cheap work off-platform is economically backwards here. OpenRouter stays Hold on Max, Trial on API only after the F4 ID refresh (2024-era `gpt-4o-mini`/`gemini-flash-1.5` are stale in 2026-07).
- **Durable telemetry (precondition for prune window):** the engine-level increment (`_council-engine.md:672-673`) is the right layer and ran today, but writes are lost if uncommitted — make increments durable (untracked sidecar or auto-commit) and register a telemetry path for standalone suites before starting the 2-4 week clock. Prune rule: zero-uses = inconclusive (keep); any-use = keep; only the council long tail is in scope.
- **Rollback:** `git checkout settings.json` (symlink picks up immediately); OpenRouter off via empty `tasks` map; extraction reverts as a single commit. No destructive data ops if pruning stays deferred.
