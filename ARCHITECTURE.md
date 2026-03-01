# Architecture

Technical reference for contributors and deep customizers. For usage, see [README.md](README.md).

---

## Engine Architecture

The deliberation system uses a **shared engine + themed layer** pattern. All workflow logic lives in `commands/_council-engine.md` (~1200 lines). The themed command file (`council.md`) supplies configuration variables.

### Phase Flow

```
Phase 0: Intake        → User describes their idea
Phase 1: Interview     → 2-3 rounds of targeted questions (no agents spawned yet)
Phase 2: Assembly      → Score all 20 agents, select 3-7, user approves roster
Phase 3: Deliberation  → 3 rounds: Position → Challenge → Converge
Phase 4: Planning      → Synthesize design document + PRD
Phase 5: Action        → Execute via team, /ralf, or manual review
```

### Theme Extension Points

Each themed command file defines 14 variables:

| Variable | Purpose | Example |
|----------|---------|---------|
| `$THEME_ID` | Directory prefix for sessions | `council` |
| `$THEME_NAME` | Display name | `Council` |
| `$ROSTER_TABLE` | Agent roster with names, colors, files, subagent types | *(see council.md)* |
| `$INTAKE_PROMPT` | Phase 0 question text | "What's the big idea?" |
| `$AGENT_FILE_PREFIX` | Filename prefix for personas | `council-` |
| `$MODIFIER_RULES` | Scoring bonuses and anti-redundancy penalties | *(see council.md)* |
| `$CHALLENGE_RULES` | How tension pairs are identified | Organic (from positions) |
| `$CONDUCTOR_PERSONA` | Agent file the conductor embodies | `council-steward` |
| `$SESSION_DIR_ROOT` | Root path for sessions | `.claude/council/sessions/` |
| `$TEAM_PREFIX` | Prefix for team names | `council-` |
| `$GLOBAL_REGISTRY_PATH` | Cross-workspace registry path | `~/.claude/council/global-registry.json` |
| `$INDEX_PATH` | Workspace index path | `.claude/council/index.json` |
| `$PHASE_LABELS` | Themed labels for each phase | *(see council.md)* |
| `$EXTRA_MECHANICS` | Theme-specific mechanics | *(none for council)* |

### Mode System

Eight modes control workflow depth. Modes are theme-agnostic (defined in the engine):

| Mode | Interview | Rounds | User Touchpoints | Action Phase |
|------|-----------|--------|------------------|-------------|
| brainstorm | None | 1 (3 fixed agents) | None | None |
| quick | None | 1 | Assembly only | Optional |
| standard | 2-3 rounds | 3 | Assembly + each round | Full |
| deep | 2-3 rounds | 3 + audit | All | Full |
| auto | 2-3 rounds | 3 | None | Auto-execute |
| guided | 2-3 rounds | 3 | Every phase | Full |
| meeting | 2-3 rounds | 3 | Assembly + each round | None (discussion only) |
| audit | None | 1 (codebase scan) | Assembly | Report only |

---

## Agent Schema

Agent personas live in `agents/`. Each is a markdown file with YAML frontmatter.

### Council Agent Format

```yaml
---
name: "Architect"
description: "Council Blue Lens — system design, data models, APIs, integration patterns"
model: "claude-opus-4-6"
---
```

### Persona Body Structure

Every agent file follows the same structure:
1. **Title + color identity** — One-line character intro
2. **Cognitive Framework** — 4 mental models the agent uses to reason
3. **Trained Skills** — 6 specific technical capabilities
4. **Communication Style** — How the agent presents reasoning
5. **Decision Heuristics** — 5 gut-instinct rules
6. **Known Blind Spots** — What the agent tends to get wrong (self-check)
7. **Deliberation Formats** — Templates for Position, Challenge, and Converge rounds

---

## Skill System

Skills live in `skills/council/`. Each agent manages a department of 2-3 skills.

### Directory Structure

```
skills/council/
├── README.md              # System overview
├── registry.json          # Usage tracking across all departments
├── architect/
│   ├── DEPARTMENT.md      # Department overview
│   ├── codebase-context/
│   │   └── SKILL.md       # Structured skill template
│   ├── schema-design/
│   │   └── SKILL.md
│   └── api-design/
│       └── SKILL.md
├── advocate/
│   └── ...
└── (20 departments total)
```

### SKILL.md Format

Each skill template contains:
1. **Purpose** — What the skill produces
2. **Inputs** — What information it needs
3. **Process** — Step-by-step methodology
4. **Output Format** — Markdown template for structured output
5. **Quality Checks** — Verification checklist
6. **Evolution Notes** — Post-session observations that drive skill improvement

### Skill Loading

1. **Assembly** — The conductor matches skill triggers against the idea and interview transcript
2. **Deliberation** — Skill content is inlined into agent prompts; agents follow process steps
3. **Execution** — Task assignments include relevant skills for structured methodology

### Skill Evolution

After each session, the conductor appends observations to the skill's Evolution Notes. The `registry.json` tracks usage counts. If a skill consistently needs the same adjustment, its process steps are updated.

Skills are not duplicated — all 57 SKILL.md files live in `skills/council/`.

---

## Workspace Detection

Workspaces provide project-specific context that auto-loads based on git remote name.

### How It Works

1. Claude Code starts in a project directory
2. The system reads the git remote URL and extracts the repo name
3. If `~/.claude/workspaces/<repo-name>/` exists, its contents are injected into context

### Workspace Contents

```
workspaces/<repo-name>/
├── INFRASTRUCTURE_MAP.md   # Services, databases, deployment topology
├── CONVENTIONS.md          # Team-specific coding conventions
└── CONTEXT.md              # Current focus, recent decisions
```

The `_full-stack/` directory is a template for multi-stack projects. The `FORMAT.md` documents the workspace config format.

---

## Hook System

Hooks are shell scripts triggered by Claude Code lifecycle events.

### Active Hooks

`hooks.json` maps events to scripts:

| Event | Script | What Happens |
|-------|--------|-------------|
| `PreCompact` | `pre-compact-handover.sh` | Auto-generate handover before context compaction |

### Observability (Planned)

Session tracing and token usage observability (Langfuse integration) is in the works. The hook infrastructure (`hooks.json` event routing + shell script dispatchers) is designed to support observability hooks once the tracing pipeline is solid.

---

## Session Persistence

Two mechanisms preserve context across sessions:

### Manual Handover (`/handover`)

The `/handover` command saves a structured markdown document with:
- Session summary
- What was done (changes list)
- Key decisions with rationale
- Pitfalls and gotchas
- Open questions
- Next steps

Saved to `memory/HANDOVER-<timestamp>.md` in the project root.

### Auto-Compaction Hook

The `pre-compact-handover.sh` hook fires on `PreCompact` events (auto-compaction only, not manual `/compact`). It:
1. Reads the last 500 lines of the session transcript
2. Pipes them to `claude -p --model sonnet` with a summarization prompt
3. Saves the result to `memory/HANDOVER-<timestamp>-auto.md`

At session start, `CLAUDE.md` instructs Claude to check for recent handover files and read the most recent one.

---

## Scripts

Utility scripts in `scripts/`:

| Script | Purpose |
|--------|---------|
| `launch-agent.sh` | Launch a council agent with context |
| `run-agent.sh` | Run an agent task to completion |
| `agent-broadcast.sh` | Broadcast a message to all active agents |
| `agent-status.sh` | Check status of running agents |
| `find-workspaces.sh` | Discover workspace configs by git remote |
| `launch-workspace.sh` | Initialize workspace context |
| `notify-complete.sh` | Send completion notification |
| `task-board.sh` | Display task board status |

---

## Extending the System

### Adding a New Agent

1. Create `agents/council-<name>.md` with YAML frontmatter (`name`, `description`, `model`) and the standard persona body structure
2. Create `skills/council/<name>/DEPARTMENT.md` describing the department
3. Create 2-3 skill directories under the department, each with a `SKILL.md`
4. Add the agent to the roster table in `commands/council.md`
5. Add the department to `skills/council/registry.json`
### Adding a New Command

Create `commands/<name>.md` with frontmatter:

```yaml
---
description: "Short description shown in the skills list"
argument-hint: "[optional args hint]"
---
```

The body is the prompt template. It's loaded as a skill and can reference other files, use `$ARGUMENTS` for user input, and call other commands.

### Adding a New Skill

Create `skills/council/<department>/<skill-name>/SKILL.md` with sections: Purpose, Inputs, Process, Output Format, Quality Checks.

### Adding a New Theme

Create a new command file (e.g., `commands/mytheme.md`) that defines all 14 extension point variables and references `_council-engine.md`. Create agent files with your theme's framing. The engine handles all workflow logic.
