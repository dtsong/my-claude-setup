# Adoption Guide

This repo is designed to be adopted incrementally.

## Install Presets

The installer supports three presets:

- `skills` (default): installs skills only
- `core`: skills + commands + agents
- `full`: core + scripts + hook scripts + workspaces

All presets avoid replacing `~/.claude/settings.json`, `~/.claude/hooks.json`, and `~/.claude/CLAUDE.md` unless you explicitly opt in.

## Quick Start

Install skills only (safe default):

```bash
./install.sh
```

Install only a few skill packs:

```bash
./install.sh --list-skills
./install.sh --skills git-status,github-workflow,workflow
```

## Notes on Vercel React Best Practices

`vercel-react-best-practices` is implemented as a lightweight stub that fetches Vercel's upstream guidance at runtime.

If you want an offline snapshot instead, see `skills/vercel-react-best-practices/README.md`.

Adopt the full setup:

```bash
./install.sh --preset full
```

## Opt-In Configuration

If you want this repo to manage your Claude Code config files:

```bash
./install.sh --preset full --with-settings --with-hooks-json --with-claude-md
```

If you only want hook scripts (without replacing your `hooks.json`):

```bash
./install.sh --with-hooks-scripts
```

## Safety Tips

- Use `--dry-run` to see what would change.
- Use `--conflict-policy skip` if you want a partial install without moving existing files.
- Use `CLAUDE_DIR=/tmp/claude ./install.sh --preset core` to test installs in an isolated directory.

## Uninstall

```bash
./install.sh --uninstall
```
