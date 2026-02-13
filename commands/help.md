---
description: "Quick reference for all commands, modes, skills, and agents. Try: /help modes, /help skills, /help agents"
argument-hint: "[modes|skills|agents|<command>]"
---

# /help — Discovery & Quick Reference

Show what's available in this setup. Subcommands narrow the view.

## Usage

```
/help              → compact reference card
/help modes        → deliberation mode decision tree
/help skills       → installed skills grouped by category
/help agents       → the 16 agents with one-line differentiators
/help <command>    → detailed help for a specific command
```

## Routing

Parse the argument after `/help`:
- No argument → show **Reference Card**
- `modes` → show **Mode Decision Tree**
- `skills` → show **Skills Directory**
- `agents` → show **Agent Roster**
- Anything else → treat as a command name, show **Command Detail**

---

## Reference Card (no args)

Print this compact card:

```
my-claude-setup — Quick Reference

DELIBERATION
  /brainstorm "idea"           30-sec gut check from 3 agents
  /council "idea"              Full multi-agent deliberation (default: standard mode)
  /academy "idea"              Same deliberation, Fire Emblem theme

PROJECT SETUP
  /new-python                  Python + FastAPI + uv + ruff
  /new-typescript              TypeScript + Next.js + pnpm + Vitest
  /new-terraform               Terraform module + tflint + tfsec
  /new-mcp-server              MCP server + TypeScript SDK + Zod

WORKFLOW
  /implement #1 #2             Implement GitHub issues into PRs
  /looper #1 #2                Issues to PRs with retry loops
  /ralf                        Autonomous PRD-based execution
  /roadmap-executor            Roadmap → issues → PRs pipeline
  /create-issues               Generate issues from a roadmap doc

SESSION
  /handover                    Save session context for next session
  /ops                         Operations control center
  /g                           Git porcelain

MORE INFO
  /help modes                  Which deliberation mode to pick
  /help skills                 All installed skills
  /help agents                 The 16 council agents
  /help <command>              Detailed help for any command
```

---

## Mode Decision Tree (`/help modes`)

Print this decision tree:

```
Which deliberation mode?

  How much time do you have?

  30 seconds    → /brainstorm "idea"
                  3 agents, fast takes, no files

  5 minutes     → /council --quick "idea"
                  Skip interview, 1 round, lightweight output

  15-30 min     → /council "idea"
                  Full workflow: interview → 3 rounds → design doc + PRD
                  This is the default.

  30+ min       → /council --deep "idea"
                  Standard + mandatory deep audit pass

  What kind of session?

  Discussion    → /council --meet "idea"
                  Talk it through, no action plan produced

  Code audit    → /council --audit "API security"
                  Direct codebase audit against best practices

  Hands-off     → /council --auto "idea"
                  No approval touchpoints — agents run autonomously

  Max control   → /council --guided "idea"
                  User approval at every phase transition

All modes also work with /academy (Fire Emblem theme).
```

---

## Skills Directory (`/help skills`)

Dynamically discover installed skills by scanning the filesystem:

1. Read standalone skills from `~/.claude/skills/*/SKILL.md` — extract `name` and `description` from frontmatter
2. Read council skills from `~/.claude/skills/council/*/*/SKILL.md` — these have `[Council]` prefix in description
3. Group and display:

```
Installed Skills

STANDALONE
  <name>         <description (first sentence)>
  ...

COUNCIL (used during /council and /academy deliberation)
  <department>/<skill>    <description without [Council] prefix>
  ...

To use a skill: skills are matched automatically based on your request.
See the skill-matching protocol for details.
```

If `~/.claude/skills/` doesn't exist or is empty, say: "No skills installed. Run `./install.sh` to set up."

---

## Agent Roster (`/help agents`)

Print this roster:

```
The 16 Council Agents

Each agent brings a distinct cognitive lens. Sessions use 3-7 agents selected for relevance.

SYSTEM DESIGN
  Architect (Blue)       System design, data models, APIs, integration patterns
  Operator (Orange)      DevOps, deployment, infrastructure, monitoring
  Sentinel (Titanium)    IoT, embedded, edge, device protocols

USER & PRODUCT
  Advocate (Green)       User experience, product thinking, accessibility
  Artisan (Rose)         Visual design, design systems, motion
  Herald (Bronze)        Growth, monetization, onboarding, retention

QUALITY & SECURITY
  Skeptic (Red)          Risk assessment, security, devil's advocate
  Craftsman (Purple)     Testing strategy, DX, code quality, patterns
  Guardian (Silver)      Compliance, governance, privacy

DATA & AI
  Alchemist (Indigo)     Data engineering, data science, ML workflows
  Oracle (Violet)        AI/LLM integration, RAG, prompt engineering
  Tuner (Amber)          Performance, scalability, optimization

STRATEGY & RESEARCH
  Strategist (Gold)      Business value, scope, MVP, prioritization
  Scout (Cyan)           Research, precedent, external knowledge
  Chronicler (Ivory)     Documentation, knowledge architecture
  Pathfinder (Coral)     Mobile, cross-platform, native apps

CONDUCTOR
  Steward (Platinum)     Orchestrates deliberation — always active, never spawned separately

The Academy theme mirrors this roster with Fire Emblem class names.
```

---

## Command Detail (`/help <command>`)

When the argument doesn't match a known subcommand (modes, skills, agents):

1. Check if `~/.claude/commands/<argument>.md` exists
2. If found: read the file, extract the frontmatter (`description`, `argument-hint`), and display:
   ```
   /<command> <argument-hint>
   <description>

   <first 10 lines of content after frontmatter>

   Full docs: commands/<command>.md
   ```
3. If not found: suggest the closest match from available commands and show the reference card

---

## Implementation Notes

- Always output as preformatted text blocks for consistent formatting
- Keep output compact — users want a quick reference, not a manual
- For `/help skills`, scan the actual filesystem so new skills appear automatically
- Never show internal files (files starting with `_` like `_council-engine.md`)
