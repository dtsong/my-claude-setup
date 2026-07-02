# Architect Final Position — Claude Config & Model-Routing Optimization

**Revised recommendation:** Keep the core structural call unchanged: model routing is ONE data model with a single source of truth (`skills/council/model-routing.json`, extended) keyed by spawn site and parameterized by an account-profile dimension (`max-plan` vs `api-billed`), with a per-destination egress-policy field so external routing is a schema constraint, not a bolt-on. But phase the delivery per Strategist/Oracle: the v1 MVP (F1 alias fix, F2 permissions, F4 stale-ID refresh, F5 routing-design doc, and the now-split F3a fail-soft telemetry wrapper) changes NO live model behavior and ships ungated. Activation of any live model flip (first `routed_consult` caller, /ship or council-profile model changes) is gated by an eval; the machine-readable loader and OpenRouter relay follow behind that gate.

**Concessions made and why:**

1. **Consolidation splits into design-then-activate.** My R1 framed the unified routing table as one consolidation landing. I concede Strategist's phasing: F5 ships as a routing *design doc* in v1 (no behavior change, ungated), and the machine-readable loader + first live caller are gated behind F11's 12-case smoke eval, with the full 38-case harness gating Phase 2 relay (F6) and evidence-based pruning (F7). This is correct sequencing: a config that reroutes models is only safe once there is a smoke set proving the reroute holds.

2. **Telemetry loop must close before council pruning, not either/or.** My R1 offered "close the loop OR prune on heuristics." Craftsman and Scout verified the loop is measurably broken: committed HEAD shows 0/67 uses; all 10 nonzero entries are uncommitted this-session writes. The increment mechanism exists (engine line 672-673) but is not durable. I concede the refined rule: make increments durable (F3a telemetry pipeline is the prerequisite), run a 2-4 week window for the council long tail, treat zero-uses as inconclusive and any-use as keep. Dormant *suites* (ECE, resume-tailor, docx-to-pdf, soc-security) extract now on workload judgment, independent of the registry, since usage data will never accrue for suites the user is not exercising.

3. **OpenRouter Pattern A is not a clean fourth-surface extension I can just draw.** I conceded to Skeptic's re-verified egress finding: `openrouter_client.py` sends system+prompt verbatim with no redaction. Pattern A downgrades from "designed-in" to gated Trial behind a send-allowlist, ZDR/no-training flags, and actual-model audit. This changes my schema: the routing table must carry an `egress_policy` per external destination, so the allowlist is structural.

4. **F3 splits; F3a joins the MVP.** I accept Operator/Strategist splitting F3. The XS piece (fail-soft existence guard + vendored wrapper that removes the private-repo path from public settings.json) joins v1; the M-sized hardening (per-call interpreter perf, batching, alert tuning) slides to v1.1. My R1 flagged the 5-event cross-repo hook as fragile; F3a is the minimal fix and my routing metrics depend on its telemetry pipeline.

**Non-negotiables:**

1. **Single source of truth for routing.** Phase 2 lens relay (F6) MUST extend `model-routing.json`, not add a fourth routing surface. Three vocabularies across settings/engine-prose/OpenRouter-IDs already cannot stay consistent; a fourth guarantees permanent drift and a model-rename becomes an N-file edit that the validator rejects. Non-negotiable regardless of eval outcome.

2. **`settings.json.model` reverts to a tier alias, and the `[1m]`/`DISABLE_1M_CONTEXT=1` conflict resolves to one state.** Pinned `claude-fable-5[1m]` violates repo governance and is self-canceling against the env flag. The concrete ID lives in the routing config, not the session default. This is F1, ungated, ships v1.

3. **The private-repo path leaves public `settings.json` (F3a).** A hard cross-repo dependency invoked on every tool call across five lifecycle events is a broken seam: break-on-clone, degrades the API work account, and leaks a private filesystem path into public config. Non-negotiable for v1.

4. **The routing schema carries a per-destination `egress_policy` field.** This makes Skeptic's send-allowlist a structural invariant of the data model rather than client-side code that can be bypassed. Any external (OpenRouter) destination without an egress policy is a schema violation.

**Implementation notes:**

- **Schema shape (F5 doc, v1):**
  ```
  {
    "tiers":   { "<alias>": { "max-plan": "<id>", "api-billed": "<id>" } },
    "profiles":{ "max-plan": {...}, "api-billed": {...} },
    "spawn_sites": { "session_default|council.<profile>|ship|looper|subagent|routed_consult": "<alias>" },
    "egress_policy": { "<external_dest>": { "send_allowlist": [...], "zdr": true, "no_train": true, "audit_actual_model": true, "kill_switch": true } }
  }
  ```
  Tier aliases resolve to concrete IDs per active profile; council cost-profiles (lean/balanced/max) become spawn-site→alias entries; the engine's prose cost table is generated from or validated against this file.

- **Max-plan routing:** adopt Oracle's Haiku-in-family default for cheap council spawns (rate-limit efficiency, quality ceiling preserved for lead lenses). Pattern B (OpenRouter cheap tasks) is Hold on Max (no dollar upside against rate limits); Trial on API-billed only, after the F4 ID refresh and behind Skeptic's cost ceiling.

- **F3a:** `hooks/telemetry-dispatch.sh` (5-line existence guard, fail-soft no-op if private repo absent) replaces the five bare `python3 $HOME/.../session_telemetry.py` invocations; five string edits in settings.json lines 71-115 point at the wrapper.

- **Evals:** land in `pipeline/evals/`. The 12-case smoke set (F11) ships as an acceptance criterion inside F5 and gates the first `routed_consult` live caller. The 38-case harness is the entry gate for F6 (relay) and F7 (prune evidence). Neither gate blocks the F1/F2/F4/F5-doc/F3a v1 PR, since none change live model behavior.

- **/ship handoff:** each finding maps to a GitHub issue; v1 MVP = F1, F2, F4, F5 (doc), F3a as one quick-win PR; v1.1 = F3b, F6, F7, F11-driven activation. Dormant-suite extraction is its own issue, workload-gated, not registry-gated.
