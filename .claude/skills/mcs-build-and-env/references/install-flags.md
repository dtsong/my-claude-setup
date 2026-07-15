# install.sh: full flag reference and manifest schema

Verified against `install.sh` (496 lines, `#!/bin/bash`, `set -euo pipefail`)
on 2026-07-02. Re-verify: `./install.sh --help`.

## All flags

| Flag | Effect | Notes |
|---|---|---|
| `--preset skills\|core\|full` | selects link set (see SKILL.md Step 2 table) | default `skills` |
| `--skills <csv>` | install only the named skill packs instead of all of `skills/*` | each name must be a real directory under `skills/`, else `die "Unknown skill pack: ..."` |
| `--list-skills` | prints every installable pack name and exits 0 | does not install anything |
| `--conflict-policy fail\|skip` | `fail` (default): abort before any writes if any target exists and is not a symlink. `skip`: print every conflict, then link only the non-conflicting entries | `skip` with every target conflicting can hit the bash-3.2 empty-array trap (see SKILL.md Gotchas) |
| `--dry-run` | prints the full plan (`mkdir -p ...`, `ln -sfn ...`) and returns 0 before any writes, even before conflict resolution runs the `skip` continuation path | safe to run repeatedly, never touches `~/.claude` |
| `--with-settings` | additionally links `settings.json` → `~/.claude/settings.json` | opt-in regardless of preset; overwrites your existing global settings if you don't first back them up |
| `--with-hooks-json` | additionally links `hooks.json` → `~/.claude/hooks.json` | opt-in regardless of preset |
| `--with-hooks-scripts` | additionally links every `hooks/*.sh` into `~/.claude/hooks/` | works even without `--preset full` (guarded by `"$preset" != "full"` to avoid double-planning the same links) |
| `--with-claude-md` | additionally links `CLAUDE.md` → `~/.claude/CLAUDE.md` | opt-in regardless of preset; overwrites your existing global CLAUDE.md |
| `--uninstall` | removes symlinks recorded in the manifest, then does legacy top-level cleanup | **must be the literal first argument** (`main()` only checks `"${1:-}"`); anywhere else the option parser hits `*) die "Unknown option: $1"` |
| `-h`, `--help` | prints usage and exits 0 | |

`CLAUDE_DIR` env var overrides the install target (default `$HOME/.claude`):
use this for any dry-run testing so you never touch a real `~/.claude`.

## Manifest schema (`~/.claude/.managed/my-claude-setup.json`)

Written by `write_manifest()` on every non-dry-run install (any preset).
Shape:

```json
{
  "version": 1,
  "repo_dir": "/abs/path/to/my-claude-setup",
  "preset": "core",
  "installed_at": "2026-07-02T00:00:00Z",
  "items": [
    {"source": "/abs/path/.../skills/dbt-skill", "path": "/abs/.claude/skills/dbt-skill"}
  ]
}
```

`--uninstall` reads this file first and removes only the `path` entries that
are still symlinks (skips anything a later process replaced with a real
file), then best-effort `rmdir`s now-empty parent directories, then deletes
the manifest itself and `.managed/` if empty.

## Legacy cleanup (pre-manifest installs)

After manifest-driven removal, `uninstall()` unconditionally checks 9
top-level names for a symlink that resolves to the exact matching repo path,
and removes any match even if no manifest exists:
`CLAUDE.md, settings.json, hooks.json, commands, skills, agents, scripts,
hooks, workspaces`. This is why an install performed by directly running
`ln -s` (as this development machine's own `~/.claude` was set up, predating
the manifest system: no `.managed/my-claude-setup.json` exists here) is
still safely removable by `--uninstall`.

## CI coverage (what is and isn't tested)

`.github/workflows/validate.yml`, matrix `ubuntu-latest` + `macos-latest`:
`bash -n` over `install.sh`/`hooks/*.sh`/`scripts/*.sh`, JSON-parses
`settings.json`/`hooks.json`, then an isolated smoke test (`CLAUDE_DIR:
${{ runner.temp }}/claude`) that runs `--help`, `--list-skills`, `--dry-run`,
then a real `--preset skills` install + `--uninstall`, then a real
`--preset core` install + `--uninstall`. **`--preset full` is never smoke
tested**, nor is `--conflict-policy skip`, nor any `--with-*` flag. A
regression confined to those paths will not fail CI.
