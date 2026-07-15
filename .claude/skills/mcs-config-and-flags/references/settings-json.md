# settings.json and settings.local.json, field by field

Both files use the standard Claude Code settings schema. `settings.json` is production (symlinked to `~/.claude/settings.json` on this machine, created 2026-02-09). `.claude/settings.local.json` is the project-local experiment overlay: it is gitignored (`.gitignore`: `settings.local.json`, `**/settings.local.json`) and never deploys anywhere but this repo.

## settings.json top-level fields (verified against HEAD `d84b549`, `feat/61-permissions-rewrite`)

| Field | Value | Notes |
|---|---|---|
| `env.CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS` | `"1"` | Required for the council teams backend's live `--meet` steering. Without it, sub-rounds degrade to fixed one-shot Task phases with one follow-up max (`commands/_council-engine.md:897`). |
| `env.CLAUDE_CODE_DISABLE_1M_CONTEXT` | `"1"` | Deliberate: this meta-config repo has no workload needing 1M context (`docs/model-routing.md`). Previously contradicted a `[1m]`-suffixed model pin (fixed by #60/US-002; see `model` below). |
| `env.CLAUDE_CODE_DISABLE_AUTO_MEMORY` | `"1"` | Deliberate: the repo's `/handover` protocol is the memory mechanism of record, not Claude Code's auto-memory. |
| `model` | `"opus"` | Tier alias only. `docs/model-routing.md` states the rule explicitly: pinned `claude-*` IDs are forbidden in this field because they go stale and bypass profile routing. History: was hand/app-written to `"claude-fable-5[1m]"` and committed as `0954f52` (parked, pending #60); reverted to a tier alias by PR #68 (`a1a8a72`, US-002/F1). |
| `permissions.allow` | 27 entries as of `d84b549` | Rewritten by #61/US-003 (PR #69) to match the repo's actual bash/python/markdown workload: `Write(agents\|commands\|skills\|hooks\|pipeline\|docs\|mcp/**)`, `Bash(pre-commit run *)`, `Bash(pytest *)`, `Bash(python3 *)`, scoped `gh` subcommands (`pr`, `issue`, `label`, `repo view`, `auth status`), `jq *`, `git status/diff/log/add/commit`. Superseded the old TypeScript-shaped list (`Write(src\|tests/**)`, `npm run/test`, `npx tsc`) that never matched this repo (no `src/`, no root `package.json`). |
| `permissions.deny` | 26 entries | Secret-file reads (`.env*`, `*.pem`, `*.key`, `secrets/**`, `credentials/**`, `.aws/**`, `.ssh/**`, `.npmrc`, `.pypirc`, etc.), `Write(.github/workflows/*)`, `Bash(rm -rf *)`, `sudo *`, `npm publish *`, `curl * \| sh`, `wget *`, `chmod *`, plus 4 destructive `gh` subcommands added alongside the allow rewrite (`gh repo delete`, `gh secret set`, `gh gist create`, `gh repo create`). |
| `permissions.defaultMode` | `"acceptEdits"` | Platform semantics (what this mode actually skips) belong to `mcs-claude-code-platform`. |
| `effortLevel` | `"high"` | |
| `tui` | `"fullscreen"` | App-written preference, landed in the same commit (`0954f52`) as the fable pin. |
| `statusLine.command` | shells out to `bun` running claude-hud, resolved via `ls -td ~/.claude/plugins/cache/claude-hud/claude-hud/*/` | This machine only: depends on `~/.bun/bin/bun` and the claude-hud plugin cache existing. |
| `enabledPlugins` | 9 entries: `claude-hud`, `code-simplifier`, `superpowers`, `terraform-skill`, `swift-lsp`, `pr-review-toolkit`, `frontend-design`, `context7`, `skill-codex` | |
| `extraKnownMarketplaces` | `skill-codex` (github source: `skills-directory/skill-codex`) and `research-toolkit-local` (directory source: `/Users/danielsong/Development/llm/skills/paperbanana-skills`) | The `research-toolkit-local` entry is this machine only; a fresh clone would need this path to exist or the marketplace silently fails to resolve. |
| `mcpServers.openrouter.command` | `/Users/danielsong/Development/my-claude-setup/mcp/openrouter/.venv/bin/python` | This machine only, hardcoded absolute path. The `.venv` is a required one-time manual bootstrap (`python3 -m venv mcp/openrouter/.venv && mcp/openrouter/.venv/bin/pip install -r mcp/openrouter/requirements.txt`); the server raises `FileNotFoundError` and never starts without it (`mcp/openrouter/README.md`). |
| `mcpServers.openrouter.env.OPENROUTER_API_KEY` | `"${OPENROUTER_API_KEY}"` | Shell-env passthrough only, never written to a file. Verified unset in the current shell as of 2026-07-02: `mcp__openrouter__consult` returns `{"error_kind": "missing_key", "fallback": "claude"}` until exported. |
| `skipDangerousModePermissionPrompt`, `skipAutoPermissionPrompt`, `skipWorkflowUsageWarning` | `true` | |
| `theme` | `"dark-ansi"` | |
| `agentPushNotifEnabled` | `true` | |

Re-verify any field: `jq -r '.<field>' settings.json` (dotted path) or `jq '.<field>' settings.json` for objects/arrays.

## .claude/settings.local.json

Project-scoped permission overlay, per the "experiment lane" convention documented in `docs/model-routing.md`:

- **Rule**: an experiment graduates into `settings.json` only via a reviewed PR. Anything living in the local file longer than two weeks should be promoted or deleted. This rule is a stated convention, not mechanically enforced: nothing currently checks the file's age.
- **Current state** (2026-07-02): 38 `permissions.allow` entries. Legitimate entries include `Bash(git push:*)`, `Bash(git reset:*)`, `Bash(python3:*)`, `Bash(chmod +x:*)`, `WebSearch`, `Skill(ship)`, `Skill(update-config)`. Junk, one-off debugging entries persist alongside them, e.g. `Bash(echo "exit=$?")` and `Bash(WORKSPACE=/tmp /Users/danielsong/Development/my-claude-setup/hooks/acceptance-gate.sh)`, leftovers from manually testing the acceptance-gate hook.
- **Precedent to internalize**: this file only ever accretes. Nothing purges stale entries automatically; a mid-level engineer adding a one-off allow rule here should expect it to sit indefinitely unless someone manually cleans it up.
- Re-verify entry count: `jq '.permissions.allow | length' .claude/settings.local.json`. Re-verify gitignore status: `git check-ignore -v .claude/settings.local.json` (expect a match).

## Re-verification for this whole file

- `diff <(git show main:settings.json) settings.json` (see exactly what the active branch changed vs `main`).
- `gh pr view 69 --json state,mergedAt` (has the permissions rewrite, US-003, landed yet).
- `ls -la ~/.claude/settings.json ~/.claude/hooks.json` (confirm the symlinks still point into this repo on this machine).
