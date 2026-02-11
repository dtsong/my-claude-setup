---
type: project-convention
topic: CLAUDE.md configuration
last_updated: 2026-02-10
token_estimate: ~950
---

# Project CLAUDE.md Guide

## Purpose

- Project-level instructions for AI assistants (Claude Code, Copilot, etc.)
- Loaded automatically when working in the project directory
- Checked into the repository so all contributors share the same AI context
- Target: ~80 lines for the actual file (conciseness forces prioritization)

## Template

```markdown
# <Project Name>

## What This Is
<1-2 sentence description of the project and its purpose>

## Model Preferences
- Use **Opus** for complex architecture/refactoring
- Use **Sonnet** for general development tasks

## Key Docs
- `/docs/CODEMAP.md` -- Codebase structure and quick reference
- `/docs/SPEC.md` -- Full implementation specification

## Quick Context
- Frontend: <framework, version>
- Backend: <framework, language>
- Database: <engine>
- Hosting: <provider>

## Tooling

### <Language> (<directory>)
- **<package manager>** - Package management (`<install command>`)
- **<linter>** - Linting and formatting (`<lint command>`)
- **<type checker>** - Type checking (`<check command>`)
- **<test runner>** - Testing (`<test command>`)

### Pre-commit
Pre-commit hooks are configured for both languages. Run `pre-commit install` after cloning.

## Key Decisions
- <Decision 1 with rationale>
- <Decision 2 with rationale>
- <Decision 3 with rationale>

## Domain-Specific
- <Domain term 1: definition>
- <Domain term 2: definition>

## Testing
- All feature work must include unit tests
- <Backend>: <test framework> + <assertion library>
- <Frontend>: <test framework> + <testing library>

## Git Workflow
- <Branch strategy description>
- <PR/review requirements>

## Current Focus
- <Current phase, sprint, or milestone>
```

## Section Guide

| Section | Required? | Purpose |
|---------|-----------|---------|
| What This Is | Yes | Orients the AI immediately |
| Model Preferences | No | Guides model selection for different task types |
| Key Docs | Yes | Points to detailed documentation |
| Quick Context | Yes | Tech stack at a glance |
| Tooling | Yes | Exact commands -- AI can run them directly |
| Key Decisions | Yes | Prevents AI from re-litigating settled decisions |
| Domain-Specific | No | Domain terminology, business rules |
| Testing | Yes | Testing expectations and tools |
| Git Workflow | Yes | Branch strategy and PR process |
| Current Focus | No | What's being worked on now |

## Anti-Patterns

- **Don't duplicate docs.** If it's in CODEMAP or SPEC, don't repeat it here.
- **Don't include secrets.** No environment variables, API keys, or credentials.
- **Don't include transient info.** Current bugs and sprint deadlines change too fast.
- **Don't exceed ~100 lines.** Brevity forces you to include only what matters most.
- **Don't include setup instructions.** That belongs in README.md.
- **Don't list individual files.** That's what CODEMAP is for.

## Tips

- Write for an AI that has never seen your project before
- Include the "why" behind decisions, not just the "what"
- Update when architecture changes, not every commit
- Test by asking an AI to explain your project after reading only CLAUDE.md
