# my-claude-setup

A portable Claude Code configuration system — 34 agents, 48 skills, 8 deliberation modes, session persistence, and lifecycle hooks. Clone it, install it, and every Claude Code session gets multi-agent deliberation, opinionated project scaffolding, and workspace-aware context injection.

## Quick Start

```bash
git clone https://github.com/your-username/my-claude-setup.git ~/Development/my-claude-setup
cd ~/Development/my-claude-setup
chmod +x install.sh
./install.sh
```

The install script symlinks this repo into `~/.claude/`. Nothing is copied — changes here are immediately available in Claude Code. Run `./install.sh --uninstall` to cleanly remove all symlinks.

Try it out:

```bash
claude
> /brainstorm "Should I use WebSockets or SSE for real-time updates?"
> /new-python                    # Scaffold a FastAPI project with full tooling
> /council "Build a notification system"   # Full multi-agent deliberation
```

## What You Get

### Multi-Agent Deliberation

`/council` and `/academy` assemble 3-7 specialized agents from a roster of 16 to deliberate on design decisions. Agents explore your codebase independently, write position statements, challenge each other's recommendations, and converge on a unified design document with explicit trade-off resolution.

Eight modes control depth and involvement:

| Mode | Flag | What It Does |
|------|------|-------------|
| **Brainstorm** | `--brainstorm` | 30-second gut check from Architect, Advocate, Skeptic |
| **Quick** | `--quick` | Fast sketch — skip interview, 1 deliberation round |
| **Standard** | *(default)* | Full workflow — interview, 3 rounds, design doc + PRD |
| **Deep** | `--deep` | Standard + mandatory deep audit pass |
| **Auto** | `--auto` | Hands-off — no approval touchpoints |
| **Guided** | `--guided` | Tight control — user approval at every phase |
| **Meeting** | `--meet` | Discussion only — no action plan produced |
| **Audit** | `--audit` | Direct codebase audit against best practices |

`/brainstorm "idea"` is a shortcut for `--brainstorm` mode.

### Project Scaffolding

| Command | Stack |
|---------|-------|
| `/new-python` | uv, ruff, FastAPI, pytest, pre-commit |
| `/new-typescript` | pnpm, Next.js 14+, Vitest, Prettier, shadcn/ui |
| `/new-terraform` | tflint, tfsec, terraform-docs, native test framework |
| `/new-mcp-server` | TypeScript MCP SDK, Zod, pnpm, Vitest |

Each command scaffolds the full project: directory structure, tooling config, CI hooks, a starter CLAUDE.md, and git initialization.

### Session Persistence

`/handover` saves session knowledge — decisions, pitfalls, and next steps — as a markdown document that the next session picks up automatically. A `PreCompact` hook auto-generates handovers before context window compaction so you never lose session state.

### Issue-Driven Execution

| Command | What It Does |
|---------|-------------|
| `/looper` | Implement GitHub issues into PRs with dependency ordering, quality gate retry loops, and checkpoint/resume |
| `/implement` | Implement one or more GitHub issues and create PRs |
| `/ralf` | Autonomous execution loop with PRD-based planning |
| `/roadmap-executor` | Full workflow from roadmap document to GitHub issues to PRs |

### Hooks

A `PreCompact` hook auto-generates session handovers before context window compaction (see Session Persistence above).

> **Observability:** Session tracing and token usage observability (Langfuse integration) is in the works. See the `hooks/` directory for the current hook infrastructure.

### Workspace Context

Workspaces are project-specific context configs that auto-load based on git remote name. Drop a config in `workspaces/<repo-name>/` and it's injected into every session working in that repo — infrastructure maps, team conventions, deployment notes.

## Command Reference

### Deliberation

| Command | Description |
|---------|-------------|
| `/council [--mode] "idea"` | Multi-agent deliberation (Council theme) |
| `/academy [--mode] "idea"` | Multi-agent deliberation (Fire Emblem Academy theme) |
| `/brainstorm "idea"` | Quick 3-agent gut check |

### Project Setup

| Command | Description |
|---------|-------------|
| `/new-python` | Python + FastAPI project |
| `/new-typescript` | TypeScript + Next.js project |
| `/new-terraform` | Terraform module |
| `/new-mcp-server` | MCP server (TypeScript) |

### Workflow

| Command | Description |
|---------|-------------|
| `/looper` | Issue-to-PR with retry loops |
| `/implement` | Implement GitHub issues |
| `/ralf` | Autonomous PRD executor |
| `/roadmap-executor` | Roadmap to issues to PRs |
| `/create-issues` | Generate GitHub issues from a roadmap |

### Session Management

| Command | Description |
|---------|-------------|
| `/handover` | Save session context for next session |
| `/council --resume` | Resume a deliberation session |
| `/council --list` | List sessions in workspace |
| `/council --archive <slug>` | Export session to GitHub issue |
| `/ops` | Operations control center |
| `/g` | Git porcelain |

## The 16 Agents

Each agent brings a distinct cognitive lens. Sessions use 3-7 agents selected for relevance.

| Agent | Lens Color | Focus Area |
|-------|-----------|------------|
| Architect | Blue | System design, data models, APIs, integration patterns |
| Advocate | Green | User experience, product thinking, accessibility |
| Skeptic | Red | Risk assessment, security, devil's advocate |
| Craftsman | Purple | Testing strategy, DX, code quality, patterns |
| Scout | Cyan | Research, precedent, external knowledge |
| Strategist | Gold | Business value, scope, MVP, prioritization |
| Operator | Orange | DevOps, deployment, infrastructure, monitoring |
| Chronicler | Ivory | Documentation, knowledge architecture, onboarding |
| Guardian | Silver | Compliance, governance, privacy |
| Tuner | Amber | Performance, scalability, optimization |
| Alchemist | Indigo | Data engineering, data science, ML workflows |
| Pathfinder | Coral | Mobile, cross-platform, native apps |
| Artisan | Rose | Visual design, design systems, motion |
| Herald | Bronze | Growth, monetization, onboarding, retention |
| Sentinel | Titanium | IoT, embedded, edge, device protocols |
| Oracle | Violet | AI/LLM integration, RAG, prompt engineering |

The **Steward** (Platinum) serves as the conductor persona — always active, never spawned as a separate agent.

The **Academy** theme mirrors the full roster with Fire Emblem class names (Sage, Troubadour, Thief, etc.), house tensions, support conversations, and class promotion mechanics.

## Directory Layout

```
my-claude-setup/
├── agents/              # 34 agent persona files (17 council + 17 academy)
├── commands/            # 16 slash commands + shared engine
│   ├── _council-engine.md  # Shared deliberation engine (~1200 lines)
│   ├── council.md       # Council theme layer
│   ├── academy.md       # Academy theme layer
│   └── *.md             # Individual commands
├── skills/              # 48 structured skill templates
│   ├── council/         # 16 departments × 3 skills each
│   └── language-conventions/  # Python, TypeScript, Terraform references
├── hooks/               # Lifecycle hook scripts
│   └── pre-compact-handover.sh  # Auto-save before compaction
├── workspaces/          # Project-specific context configs
├── scripts/             # Utility scripts (agent management, notifications)
├── CLAUDE.md            # Global Claude Code instructions
├── settings.json        # Claude Code settings (model, env, plugins)
├── hooks.json           # Hook event routing
└── install.sh           # Symlink installer (with --uninstall)
```

## Customization

### Level 1: Use As-Is

Just run `./install.sh`. You get everything — all agents, skills, commands, and hooks.

### Level 2: Personalize

- Edit `CLAUDE.md` to add your own global instructions (NVM setup, coding preferences, etc.)
- Edit `settings.json` to change default model, enable/disable plugins
- Add workspace configs in `workspaces/<your-repo-name>/` for project-specific context

### Level 3: Fork for Your Team

1. Fork this repo
2. Keep: `commands/_council-engine.md`, `agents/`, `skills/council/`, `hooks/`
3. Customize: `CLAUDE.md` (team conventions), `settings.json` (model preferences), workspace configs
4. Add team-specific commands in `commands/`
5. Each team member clones and runs `./install.sh`

### Level 4: Extend the System

See [ARCHITECTURE.md](ARCHITECTURE.md) for details on:
- Adding new agents (persona file + department + skills + roster entry)
- Creating commands (markdown prompt templates with frontmatter)
- Building skills (structured templates with process steps and quality checks)
- Adding themes (supply 14 extension points to the shared engine)

## How It Works

Everything is markdown files symlinked into `~/.claude/`:

```
~/Development/my-claude-setup/          ~/.claude/
├── CLAUDE.md              ──symlink──▶ ├── CLAUDE.md
├── settings.json          ──symlink──▶ ├── settings.json
├── hooks.json             ──symlink──▶ ├── hooks.json
├── commands/              ──symlink──▶ ├── commands/
├── agents/                ──symlink──▶ ├── agents/
├── skills/                ──symlink──▶ ├── skills/
├── hooks/                 ──symlink──▶ ├── hooks/
├── scripts/               ──symlink──▶ ├── scripts/
└── workspaces/            ──symlink──▶ └── workspaces/
```

Claude Code reads `~/.claude/` for configuration. Because these are symlinks, editing files in the repo immediately updates what Claude sees. No build step, no compilation — just markdown prompts.

## Prerequisites

- [Claude Code](https://claude.com/claude-code) CLI
- Agent teams feature enabled (set `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1` in settings.json — already configured)

- Git (for workspace auto-detection)

## License

MIT License — see [LICENSE](LICENSE) for details.
