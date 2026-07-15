# Research frontier candidates, full detail (ranks 1-3)

Ranked order and one-line rationale live in `SKILL.md`. Ranks 4-5 are in `references/candidates-rank4-5.md`. Every "why SOTA falls short" claim is training-knowledge, early-2026, author's characterization, unverified against a live literature search: treat as `open, owner-unconfirmed`.

## 1. Contract-gated autonomous execution (candidate)

**Why current SOTA falls short:** as of early 2026, most autonomous-agent harnesses treat task completion as self-reported: the agent calls a "mark done" tool and the harness trusts it, with verification enforced by a system-prompt request ("please verify before completing") rather than a structural gate the agent cannot talk its way around. Public write-ups of agent safety in this area are mostly theoretical; few ship a hardened, reproducible implementation with an incident history proving which failure modes were real.

**This repo's asset:** `hooks/acceptance-gate.sh` (PreToolUse on `TaskUpdate`→`completed`, exit 2 blocks, mtime-based contract selection, `ACCEPTANCE_GATE_STALE_HOURS` staleness guard) plus a 3-generation, SHA-documented hardening chain (299a264 → 6bc7c1a → 4bb8bf2 → 605112d) that closed three distinct fail-open holes (relative hook path + unguarded `jq`; `grep -c` zero-match arithmetic bug; `PostToolUse`+exit-1 being non-blocking by the platform's own contract). The mcs-diagnostics-and-tooling skill's `hook-contract-check.sh` tool already probes exit-code/stream behavior for any hook.

**First three steps, in this repo:**
1. Read `hooks/acceptance-gate.sh` in full, then hand off to mcs-validation-and-qa for its "Acceptance-contract discipline" section, which documents the exact `| id | criterion | method | status |` row format the hook parses.
2. Design >=10 adversarial cases covering the 3 historical fail-open modes plus >=2 novel vectors (e.g.: malformed pipe rows; a dead session's contract `touch`ed after the live one to beat mtime selection; a contract exactly at the `STALE_HOURS` boundary; concurrent contracts from two workspaces).
3. Hand off to the mcs-diagnostics-and-tooling skill and run each case through its `hook-contract-check.sh` tool against `hooks/acceptance-gate.sh` (event `PreToolUse`, tool `TaskUpdate`, one JSON payload per case), capturing exit code and stderr for every case; do not hand-roll a new harness for something that tool already does.

**You have a result when:** an adversarial suite of >=10 bypass-attempt cases against `hooks/acceptance-gate.sh` shows 0 successful bypasses (exit 0 while unverified criteria exist), with a committed report of per-case exit codes.

## 2. Closed-loop eval-driven skill evolution (candidate)

**Why current SOTA falls short:** public skill/tool registries and marketplaces (Claude skills, MCP tool directories, LangChain/CrewAI-style tool libraries) as of early 2026 ship static prompt files; adoption and retirement decisions are manual. Telemetry, where it exists, is rarely wired into an automated mutate-and-reprove loop inside a single working session: most "self-improving prompt" demos show one iteration on a toy task, not a repo-scale registry with real usage counts and a tiered eval runner.

**This repo's asset:** `skills/council/registry.json` (now durably committed telemetry, 18 real committed uses as of `dc44611`, though the increment itself is still a prose instruction at `commands/_council-engine.md:672-677`, not a forced write); 135 eval cases across 9 council departments (`skills/council/*/eval-cases/trigger-evals.json`, positive/negative typed); `pipeline/scripts/run-evals.sh` (3 tiers: static/pre-commit, e2e via `claude -p`, LLM-as-judge); `pipeline/scripts/judge-skill-quality.sh` (Clarity/Completeness/Actionability 1-5 rubric); `pipeline/scripts/check-regressions.py` (baseline comparison against `eval-cases/baselines/`, already reads that directory convention). All exist; none call each other.

**First three steps, in this repo:**
1. `python3 pipeline/scripts/skill-audit.py --json > /tmp/baseline-audit.json` for a duplicate/cost baseline.
2. Pick a weak-signal target with a documented gap, e.g. `skills/council/accountant/` (`"skills": {}` in registry.json, all `DEPARTMENT.md` links broken per `mcs-failure-archaeology`), and run `pipeline/scripts/judge-skill-quality.sh --targets accountant` for a Tier-3 baseline score.
3. Revise the target, then run `pipeline/scripts/run-evals.sh --tier all --targets accountant --diff` and `pipeline/scripts/check-regressions.py`, recording before/after numbers to `eval-cases/baselines/`.

**You have a result when:** one skill is flagged by a script reading `registry.json` + `judge-skill-quality.sh` output (not by eyeballing), revised, and re-scored with a documented Tier-3 delta of >=+1.0 point (1-5 scale) or a measurable Tier-2 pass-rate gain, entirely inside one working session, with both numbers committed.

## 3. Heterogeneous multi-model deliberation with provable egress policy (open)

**Why current SOTA falls short:** most multi-agent "debate"/"council" frameworks as of early 2026 are either single-vendor (cheap, but blind to that vendor's blind spots) or bolt on a second vendor with no egress control, so any quality-diversity gain is unmeasured and third-party data exposure is simply accepted. No public system couples heterogeneous-model deliberation with a schema-enforced, auditable send-allowlist gating every external call.

**This repo's asset:** `mcp/openrouter/` (merged, fail-soft `consult()`, never raises, hardened via PR #55/#56); `routing.py`'s `routed_consult` Pattern B primitive (zero callers today, by design); the Workflow-tool sandbox already running real deliberations (`skills/council/references/workflows/council-deliberation.template.js`, `agent()` calls) idle and structurally ready to accept non-Claude lens calls; a design-stage `egress_policy` schema field already specified (`design.md:24,30`: `send_allowlist`/`zdr`/`no_train`/`audit_actual_model`/`kill_switch`) but not implemented; a fully worked composite scoring formula for the harness (`design.md:117`).

**First three steps, in this repo (execution owned by `mcs-model-routing-campaign`; this entry frames the research question):**
1. Read `docs/superpowers/specs/2026-06-22-openrouter-integration-design.md` and this session's `design.md:24,30,97,117,140`: the egress schema and harness formula are already specified, do not re-derive them.
2. Confirm `OPENROUTER_API_KEY` provisioning (unset as of 2026-07-02) and run `python3 mcp/openrouter/check_models.py` for model-ID freshness before any live call.
3. Build the 38-case golden harness under `pipeline/evals/` (path does not exist yet) using the composite formula (correctness LLM-judge>=4.0 x 0.45 + format 100% x 0.25 + persona fidelity>=4.0 x 0.20 + cost/latency x 0.10) before writing the first `routed_consult` caller: F6 (lens relay) is explicitly gated on this in the PRD.

**You have a result when:** a committed 38-case harness run shows a mixed-model council (>=1 non-Claude lens via `routed_consult`) scoring >= the all-Claude baseline on the composite formula at lower total dollar cost, with an egress audit log showing 0 send-allowlist violations across all 38 cases.
