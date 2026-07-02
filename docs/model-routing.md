# Model Routing

Source of truth for which model runs at each spawn site, per billing profile.
Seeded by issue #60 (session default + escalation rule); issue #63 extends this
into the full spawn-site x profile table backed by `skills/council/model-routing.json`.

## Session Default and Escalation (AC-006)

| Profile | Default | Escalation |
|---------|---------|------------|
| max-plan (personal account) | `opus` | `/model fable` for ceiling-quality sessions (deep design, adversarial review); drop back to `opus` for daily work |
| api-billed (work account) | `sonnet` | escalate manually to `opus` for hard reasoning; never default to frontier tiers on dollar billing |

Rules:

- `settings.json.model` holds a tier alias only (`opus`, `sonnet`, `haiku`, `fable`). Pinned `claude-*` IDs are forbidden: they go stale and bypass profile routing.
- No `[1m]` context suffix: `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` is the deliberate stance for this meta-config repo (no workload here needs 1M context). One state, no self-cancelling pairs.
- 1M context, if ever needed, is a per-session decision made by removing the env flag AND selecting a 1M-capable model explicitly, not a standing default.
