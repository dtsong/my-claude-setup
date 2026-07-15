# Checklist: adding a new configuration axis

Use this when introducing a brand-new knob (env var, permission rule, cost-profile row, routing key, budget override) rather than changing the value of an existing one. Route the actual PR/review mechanics to `mcs-change-control`; this checklist only covers placement and documentation.

1. **Classify the axis's scope** before picking a file:
   - Applies to every project on this machine, permanent → `settings.json`.
   - Applies to this repo only, temporary/experimental → `.claude/settings.local.json`.
   - Controls council agent spawning or cost → `commands/council.md` (theme-level) or `commands/_council-engine.md` (engine-level, shared across all council-family commands).
   - Controls which OpenRouter/Claude model answers a given task or spawn site → `skills/council/model-routing.json`.
   - Controls skill-governance word/token limits → `pipeline/config/budgets.json`.
   - Controls per-skill security exemptions → `pipeline/config/security-suppressions.json` (note: currently unconsumed, no hook reads it yet; confirm a consuming hook exists or is planned before adding entries here).
2. **Check whether the axis needs a guard, and whether one exists.** As of 2026-07-02:
   - `settings.json` has **no schema validation at all** in pre-commit (`.pre-commit-config.yaml`'s hard hooks only match `files: ^skills/.*\.md$`). Issue #64/US-006 plans to add one (JSON-schema + pre-commit hook, rejecting pinned `claude-*` IDs, `[1m]` suffixes, and absolute private-repo paths in hook commands). Until #64 ships, a malformed edit here reaches the live symlinked harness immediately with zero automated protection.
   - `pipeline/config/budgets.json` overrides are checked by `check_token_budget.py`, but that hook is WARN-tier and always exits 0. Adding a wrong path here (see the soc-security precedent in `references/council-and-routing.md`) will not fail CI, it will just silently do nothing. Verify your override key with `python3 -c "import os; print(os.path.exists('<your-key>'))"` before committing it.
   - `skills/council/model-routing.json` has no validator today either; #63/US-005's AC-014 plans one (rejects pinned IDs, asserts every spawn site has an entry per profile, fails on external destinations lacking `egress_policy`).
3. **If the axis is an env var**, decide its default explicitly and put the default in the *consuming script*, not in `settings.json`'s `env` block, unless it must always be set for every session (like `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS`). Optional overrides (`CLAUDE_TELEMETRY_HOOK`, `ACCEPTANCE_GATE_STALE_HOURS`, `CLAUDE_CODE_DISABLE_WORKFLOWS`) are precedent: `"${VAR:-default}"` inside the shell script that reads it.
4. **If the axis is a permission rule**, add it to `.claude/settings.local.json` first, exercise it for real work, then promote to `settings.json.permissions` via a reviewed PR once it has proven necessary. Do not add directly to `settings.json` to "save a step": that is exactly the drift that produced the imagined-TypeScript allowlist F2 fixed.
5. **Write the rationale down**, not just the value:
   - Model/permission/env axes → append a row or section to `docs/model-routing.md` (existing precedent: the profile-escalation table, the `[1m]` rule, the experiment-lane rule).
   - Council-specific knobs → the relevant `commands/*.md` theme file, next to `DEFAULT_PROFILE` and the cost-profile table.
   - Governance budgets → the `rationale` field required alongside every `pipeline/config/budgets.json` override entry.
6. **Check for a naming collision** before creating a new file. This repo already has two unrelated files both fragmented as "model-routing" (`skills/council/model-routing.json` for OpenRouter task routing vs `pipeline/config/model-routing.yaml` for governance tier defaults). Grep existing config file names before reusing a term: `find . -iname "*<your-term>*" -not -path "*/node_modules/*"`.
7. **Confirm the axis is actually read.** This repo has two config files that are fully documented in a spec but read by zero code (`pipeline/config/model-routing.yaml`, `pipeline/config/security-suppressions.json`). Before shipping a new axis, grep for its consumer: `grep -rn "<field-or-file-name>" pipeline/hooks/*.py hooks/*.sh mcp/openrouter/*.py commands/*.md`. If nothing reads it, either wire the consumer in the same change or label the axis explicitly "design-only, not enforced" in its documentation.
8. **Add a row to `mcs-config-and-flags/SKILL.md`'s axis table**: Axis | Current value | Default | Status (production/experimental/known-wrong-parked/design-only) | Guard | Re-verify command. This is the step most PRs skip; the skill drifts the moment a new axis lands without it.
9. **Pick a re-verification command that will still work after the value changes.** Prefer `jq`/`grep`/`test -x` one-liners over prose claims: the whole point of this catalog is that its numbers go stale within hours in this repo, and only a runnable command survives that.
10. **If the axis touches `settings.json` or `hooks.json`**, remember both are symlinked into `~/.claude/` on this machine (verified: `ls -la ~/.claude/settings.json ~/.claude/hooks.json`). There is no staging environment; the change is live the moment it's on disk, commit or not.
11. **Re-run governance checks before opening a PR**: `pre-commit run --all-files` (hard hooks: frontmatter, references, isolation, context-load; warn hooks: token-budget, prose). If you touched a skill's `SKILL.md`, also confirm the file's own budget: `python3 -c "import sys; sys.path.insert(0,'pipeline/hooks'); from _utils import count_body_words, classify_file, find_repo_root; r=find_repo_root(); print(classify_file('<path>', r), count_body_words('<path>'))"`.

## Re-verification for this checklist

- `cat .pre-commit-config.yaml` (confirm which hooks are hard vs warn tier before assuming a new axis is protected).
- `gh issue view 64 --json state` (confirm whether the `settings.json` schema guard, US-006, has shipped; if it has, step 2's "no schema validation" caveat is stale and this file needs an update).
- `gh issue view 63 --json state` (same check for the `model-routing.json` validator, US-005/AC-014).
