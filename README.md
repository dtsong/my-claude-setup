# my-claude-setup

Personal Claude Code configuration — agents, skills, commands, hooks, and workspaces that customize how Claude Code works across all projects.

## What This Is

A version-controlled repo that symlinks into `~/.claude/` via `install.sh`. Everything here — slash commands, agent personas, convention references, hook scripts — becomes available in every Claude Code session.

## Directory Layout

```
my-claude-setup/
├── agents/          # Agent persona files (council + academy themes)
│   ├── council-*.md # 16 council agents + steward
│   └── academy-*.md # 16 academy agents + professor
├── commands/        # Slash command files (/council, /new-python, /brainstorm, etc.)
├── hooks/           # Hook scripts (sounds, permission classification)
│   └── sounds/      # Pokemon-themed WAV files for hook events
├── skills/          # Structured skill templates
│   ├── council/     # 48 SKILL.md files shared by council + academy agents
│   └── language-conventions/  # Python, TypeScript, Terraform references
├── workspaces/      # Project-specific context configs
│   └── _full-stack/ # Example multi-stack workspace template
├── scripts/         # Utility scripts
├── CLAUDE.md        # Global Claude Code instructions
├── settings.json    # Claude Code settings
├── hooks.json       # Hook event configuration
└── install.sh       # Symlinks repo into ~/.claude/
```

## Installation

```bash
git clone <this-repo> ~/Development/my-claude-setup
cd ~/Development/my-claude-setup
./install.sh
```

This creates symlinks from `~/.claude/` to the repo, so changes here are immediately available in Claude Code.

## How It Fits Together

```
User runs /new-python          User runs /council
       │                              │
       ▼                              ▼
commands/new-python.md         commands/_council-engine.md
       │                              │
       ▼                              ▼
Scaffolds project with         Spawns agents from agents/
conventions from               who use skills from skills/
skills/language-conventions/   with project context from
references/python.md           workspaces/<project>/
```

### Command → Convention → Workspace Pipeline

1. **Commands** (`/new-python`, `/new-typescript`, `/new-terraform`) scaffold new projects with opinionated tooling
2. **Convention references** (`skills/language-conventions/references/`) define the patterns, configs, and gotchas for each stack
3. **Workspaces** (`workspaces/<project>/`) provide pre-configured context for specific projects, auto-detected by git remote name

### Multi-Agent System

- **Council theme**: 16 domain-expert agents + Steward conductor for structured deliberation
- **Academy theme**: Same 16 agents with Fire Emblem class system, house tensions, and support conversations
- **Shared engine**: `commands/_council-engine.md` drives both themes with 8 modes (brainstorm, quick, standard, deep, auto, guided, meeting, audit)

## Quick Reference

| Command | Purpose |
|---------|---------|
| `/council` | Full multi-agent deliberation workflow |
| `/academy` | Academy-themed deliberation (with house mechanics) |
| `/brainstorm` | Quick 3-agent gut check (Architect, Advocate, Skeptic) |
| `/new-python` | Scaffold a new Python + FastAPI project |
| `/new-typescript` | Scaffold a new TypeScript + Next.js project |
| `/new-terraform` | Scaffold a new Terraform module |
| `/handover` | Save session context for the next session |
| `/looper` | Issue-driven resilient executor |

## License

Personal configuration — not intended for redistribution.
