# Model Routing

Which model runs at each spawn site, per billing profile. The machine-readable
source of truth is `skills/council/model-routing.json` (spec 2.0), validated by
the `model-routing` pre-commit hook (`pipeline/hooks/check_model_routing.py`);
this doc renders it for humans. When they disagree, the JSON wins and this doc
has a bug.

## The Full Table (AC-015)

Values are tier aliases; concrete `claude-*` IDs live only in the JSON's `tiers`
map, the one sanctioned home for pinned IDs. `inherit` means follow the session
model. `openrouter` resolves through the `tasks` map and is governed by
`egress_policy`.

| Spawn site | max-plan (rate limits, quality ceiling) | api-billed (dollars) | Effort |
|---|---|---|---|
| session_default | opus | sonnet | high |
| council.lean | sonnet | sonnet | high |
| council.balanced | opus | opus | high |
| council.max | opus | opus | high |
| brainstorm | sonnet | sonnet | low |
| challenge (Round 2 adversarial) | fable (opus fallback) | opus | max |
| audit | sonnet | sonnet | medium |
| ship_implement | opus | sonnet | high |
| ship_review | sonnet (user direction 2026-07-02; opus on repeat failure) | sonnet | high |
| looper | opus | sonnet | high |
| subagent | inherit | inherit | inherit |
| routed_consult | haiku | openrouter (eval-gated) | low |
| cheap_tasks (classify/score/scout) | haiku, temp 0, NOT OpenRouter | openrouter, cost ceiling | low |

Profile rules:

- **max-plan:** cheap work stays in-family (Haiku 4.5 is free under plan rate
  limits, zero egress). OpenRouter on Max is Hold: it bills dollars plus a 5.5%
  fee to avoid a free call.
- **api-billed:** sonnet default, manual escalation. OpenRouter Pattern B is a
  Trial behind a cost ceiling, and no `routed_consult` caller ships until the
  F11 12-case smoke eval passes. Proprietary work-account code never crosses
  the OpenRouter boundary (see `egress_policy.forbid`).

## Selection Principles

From Anthropic's model-selection guidance, adopted 2026-07-02:

- **Cost per successful outcome, not per token.** A stronger model that finishes
  agentic work in fewer turns is often cheaper end-to-end. The api-billed sonnet
  default is a starting point; correct it with data when the F11 eval records
  tokens-to-success per tier.
- **Effort is a routing dimension.** Every spawn site carries an `effort` column
  (low for mechanical stages, max only for adversarial challenge). Do not leave
  effort at a single global value when spawn sites differ.
- **Prompt caching changes the math.** Cached input is roughly 1/10 price, so
  keep agent prompts append-only (council rounds reuse an identical context
  block by design; preserve that property) before downshifting model tiers.
- **Context hygiene beats model upgrades.** Lean Markdown payloads over bloated
  JSON in tool and relay traffic; less noise raises accuracy at every tier.
- **Custom evals over public benchmarks.** Gate model flips on the repo's own
  eval cases (atomic tasks, success criteria that check the working, multiple
  trials to separate variance from signal, infra failures scored apart from
  model failures, cases sourced from real session transcripts).
- **Read the transcripts.** Before blaming or swapping a model, read the raw
  run records (workflow `journal.jsonl`, per-agent transcripts). Routing changes
  follow evidence, not vibes.

## Other Routing Surfaces

- `commands/_council-engine.md` cost-profile table: prose rendering for council
  sessions; validated against the JSON (AC-016).
- `pipeline/config/model-routing.yaml`: skill-pipeline tier preferences; its
  `tiers` map must mirror the JSON's `tiers` (same concrete IDs).
- OpenRouter task/lens routing: the same JSON's `tasks`/`lenses`/`defaults` keys,
  consumed by `mcp/openrouter/routing.py`. `defaults.fallback` stays `claude`
  (fail-soft invariant, validator rule R5).

## Session Default and Escalation (AC-006)

| Profile | Default | Escalation |
|---------|---------|------------|
| max-plan (personal account) | `opus` | `/model fable` for ceiling-quality sessions (deep design, adversarial review); drop back to `opus` for daily work |
| api-billed (work account) | `sonnet` | escalate manually to `opus` for hard reasoning; never default to frontier tiers on dollar billing |

Rules:

- `settings.json.model` holds a tier alias only (`opus`, `sonnet`, `haiku`, `fable`). Pinned `claude-*` IDs are forbidden: they go stale and bypass profile routing.
- No `[1m]` context suffix: `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` is the deliberate stance for this meta-config repo (no workload here needs 1M context). One state, no self-cancelling pairs.
- 1M context, if ever needed, is a per-session decision made by removing the env flag AND selecting a 1M-capable model explicitly, not a standing default.

## Experiment Lane: settings.local.json

`settings.json` is live production config (symlinked to `~/.claude/settings.json`)
and stays clean, minimal, and schema-verified. Experiments go in a local overlay:

- Project-scoped: `.claude/settings.local.json` (per-repo overrides while testing)
- Both filenames are gitignored (`settings.local.json`, `**/settings.local.json`)
- Rule: an experiment graduates into `settings.json` only via a reviewed PR; anything
  living in the local file longer than two weeks is either promoted or deleted
