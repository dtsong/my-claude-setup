# Settings Layering and MCP Registration (Deep Reference)

Verified against `settings.json`, `.claude/settings.local.json`, `install.sh`, `mcp/openrouter/` on 2026-07-02, HEAD `105427a`, branch `feat/61-permissions-rewrite`.

## File roles

| File | Role in this repo | Symlinked on this machine? |
|---|---|---|
| `settings.json` (repo root) | Global baseline: `env`, `permissions.{allow,deny,defaultMode}`, `hooks`, `model`, `mcpServers`, `enabledPlugins`, `extraKnownMarketplaces`, `effortLevel`, `tui`, `statusLine` | Yes → `~/.claude/settings.json` |
| `hooks.json` (repo root) | Hook-only file, `PreCompact` only (see hook reference) | Yes → `~/.claude/hooks.json` |
| `.claude/settings.local.json` (this repo, project-scoped) | Project-local `permissions.allow` accretion only: no `deny`, no `hooks`, no `defaultMode` seen here | N/A: this file lives inside the repo itself and is read because Claude Code is running with this repo as cwd, not because of a symlink |
| `skills/council/.claude/settings.local.json`, `skills/paperbanana/.claude/settings.local.json` | Nested project-local files scoped to those subtrees if Claude Code is ever launched with that subdirectory as cwd | N/A |

Exact cross-layer precedence (enterprise policy vs. CLI flags vs. project-local vs. project-shared vs. user-global) is platform behavior this repo does not implement, override, or test. Confirm against current Claude Code docs rather than treating any specific order as repo-verified. Directly observable instead: `.claude/settings.local.json` currently holds 39 `permissions.allow` entries and nothing else (verified 2026-07-02), several granting things `settings.json` doesn't (`Bash(git push:*)`, `Bash(chmod +x:*)`), noting `settings.json:55` denies `Bash(chmod *)` globally, so the local file is additive on a narrower pattern, not a blanket override. Some entries are leftover single-use debugging allows; this file accretes and isn't pruned automatically.

## `settings.json` axis inventory (as of 2026-07-02, HEAD `105427a`)

| Axis | Current value | Line |
|---|---|---|
| `env` | `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`, `CLAUDE_CODE_DISABLE_1M_CONTEXT=1`, `CLAUDE_CODE_DISABLE_AUTO_MEMORY=1` | 2-6 |
| `model` | `"opus"` (tier alias: the `claude-fable-5[1m]` pinned-ID + 1M-context contradiction that existed earlier on 2026-07-02 was resolved by PR #68 / US-002, merged) | 59 |
| `permissions.defaultMode` | `"acceptEdits"` | 57 |
| `permissions.allow` | Read/Glob/Grep/LS/Edit/MultiEdit, scoped `Write(<dir>/**)` for agents/commands/skills/hooks/pipeline/docs/mcp, a handful of `Bash(...)` prefixes (pre-commit, pytest, python3, gh, jq, git status/diff/log/add/commit) | 8-32 |
| `permissions.deny` | Secret-file reads (`.env*`, `.pem`, `.key`, `secrets/`, `credentials/`, `.aws/`, `.ssh/`, `.npmrc`, `.pypirc`), secret-file writes, `Write(.github/workflows/*)`, `Bash(rm -rf *)`, `Bash(sudo *)`, `Bash(npm publish *)`, `Bash(curl * \| sh)`, `Bash(wget *)`, `Bash(chmod *)` | 33-56 |
| `enabledPlugins` | 9 entries: `claude-hud`, `code-simplifier`, `superpowers`, `terraform-skill`, `swift-lsp`, `pr-review-toolkit`, `frontend-design`, `context7`, `skill-codex` | 137-147 |
| `extraKnownMarketplaces` | `skill-codex` (GitHub `skills-directory/skill-codex`), `research-toolkit-local` (local directory `/Users/danielsong/Development/llm/skills/paperbanana-skills`: this-machine-only path) | 148-161 |
| `mcpServers` | `openrouter` only: see below | 169-178 |
| Other flags | `effortLevel: "high"`, `tui: "fullscreen"`, `skipDangerousModePermissionPrompt: true`, `skipWorkflowUsageWarning: true`, `skipAutoPermissionPrompt: true`, `theme: "dark-ansi"`, `agentPushNotifEnabled: true` | 162-168 |

This table is a snapshot and **will drift**: it's under active edit by the same ship run that's touching this repo today. For the current authoritative catalog and the full rationale behind each value, use `mcs-config-and-flags`; this file exists only to document the *mechanism* (which file, which key) not the current truth of every value.

## The `settings.json` vs. `~/.claude/settings.json` symlink pattern

`install.sh` does **not** symlink `settings.json`, `hooks.json`, or `CLAUDE.md` by default: README states this explicitly ("avoids replacing `~/.claude/settings.json`, `~/.claude/hooks.json`, and `~/.claude/CLAUDE.md` unless you explicitly opt in", `README.md:29`). The installer has two dedicated opt-in flags:

```bash
./install.sh --with-settings       # links repo settings.json -> ~/.claude/settings.json
./install.sh --with-hooks-json     # links repo hooks.json    -> ~/.claude/hooks.json
```

(`install.sh:45-46`, wiring at `install.sh:189-195`.) For `skills/`, the default installer behavior is **per-skill-pack** symlinks (`skills/<pack> -> ~/.claude/skills/<pack>`, `install.sh:150-156`), and for `commands/`/`agents/` it's **per-file** symlinks under the `core`/`full` presets (`install.sh:158-167`). On this development machine, the actual state is coarser: `~/.claude/skills`, `~/.claude/agents`, and `~/.claude/hooks` are each single directory-level symlinks straight to the repo's top-level directory (verified `ls -la ~/.claude/`, 2026-07-02): this is a manual convenience setup on this one machine, not what a fresh `install.sh` run produces. Don't assume a fresh clone/install has this coarse-grained symlink; assume the finer-grained installer behavior instead when reasoning about a portable install.

## MCP server registration for `openrouter` (the one example)

```json
"mcpServers": {
  "openrouter": {
    "command": "/Users/danielsong/Development/my-claude-setup/mcp/openrouter/.venv/bin/python",
    "args": ["/Users/danielsong/Development/my-claude-setup/mcp/openrouter/server.py"],
    "env": { "OPENROUTER_API_KEY": "${OPENROUTER_API_KEY}" }
  }
}
```

(`settings.json:169-178`, absolute paths are this-machine facts: a portable install would need this section regenerated, e.g. by an install-time template step; nothing in this repo currently does that regeneration automatically.)

- **Transport:** stdio. The platform spawns `command` with `args`, and speaks MCP over the process's stdin/stdout. No HTTP/SSE server here.
- **Interpreter pattern:** `command` points at a project-local venv's `python` binary, not a bare `python3` or `uv run python`. This is deliberate: the server's only dependency is `mcp>=1.2.0` (`requirements.txt`), and pinning the interpreter avoids depending on whatever `python3` happens to resolve to in the invoking shell's `PATH`. The venv must be created manually once (`mcp/openrouter/README.md:8-17`); there is no bootstrap hook that creates it automatically. If the venv is deleted, the server fails with `FileNotFoundError` before any MCP handshake happens: this manifests to a user as "the openrouter tools just aren't there," not a clear error.
- **Env passthrough:** `${OPENROUTER_API_KEY}` in the `env` block is substituted from the *launching shell's* environment at server-spawn time by the platform: it is never read from a repo file, and the repo's own `CLAUDE.md` for the MCP directory states it must never be written to one either. If the variable is unset in the shell that starts Claude Code, the server itself still starts (no crash): it just returns `{"error_kind": "missing_key", "fallback": "claude"}` on every `consult()` call.
- **Tool naming:** FastMCP's `@mcp.tool()` decorator on `consult(...)` in `server.py:21-38` becomes the single callable tool. Claude Code surfaces MCP tools as `mcp__<server-key-in-settings.json>__<tool-function-name>`: here, `mcp__openrouter__consult`. This is the naming convention to expect for any future MCP server this repo adds: the server key you choose in `mcpServers` becomes part of every tool name callers will see.
- **Fail-soft contract (server-authored, not platform-enforced):** `openrouter_client.py:93-117` guarantees the tool function itself never raises: every failure path (missing key, transport error, HTTP error, parse error) returns a structured dict with `"fallback": "claude"`. This is a design choice of this specific server, not a platform guarantee; a differently-written MCP server can absolutely raise and surface as a tool error to the caller.

## Adding a second MCP server (mechanism, not this repo's roadmap)

1. Add a new key under `mcpServers` in `settings.json` with `command`/`args`/optional `env`.
2. If it's Python and you want the interpreter-pinning pattern, create a project-local venv and point `command` at its `bin/python`, following `mcp/openrouter/`'s layout.
3. Tools show up as `mcp__<key>__<tool-name>`: pick the key with that in mind, since it's permanently part of every tool name.
4. There is no repo-enforced fail-soft requirement for new servers; the `{"error", "error_kind", "fallback": "claude"}` shape is this repo's own convention for `openrouter`, not a platform contract. Adopt it deliberately if you want callers to degrade the same way.
