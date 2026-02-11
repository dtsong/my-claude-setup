---
type: project-convention
topic: persistent memory system
last_updated: 2026-02-10
token_estimate: ~1600
---

# Memory System Guide

## Purpose

- Persistent knowledge across AI coding sessions
- Prevents re-learning the same patterns, gotchas, and conventions
- Three layers: index (MEMORY.md), topic files, handovers
- Works with Claude Code's auto-memory directory

## Architecture

```
~/.claude/projects/<project-hash>/memory/
├── MEMORY.md              # Layer 1: Index (always loaded)
├── testing.md             # Layer 2: Topic file
├── debugging.md           # Layer 2: Topic file
├── architecture.md        # Layer 2: Topic file
├── HANDOVER-20260210.md   # Layer 3: Session handover
└── HANDOVER-20260209.md   # Layer 3: Session handover
```

## Layer 1: MEMORY.md (Index)

Always loaded into the system prompt. Keep under 60 lines to avoid truncation.

### Template

```markdown
# <Project> Memory

## Test Coverage (as of <date>)
- Backend: <count> tests passing
- Frontend: <count> tests passing
- See `testing.md` for patterns and lessons

## Key Patterns
- <Pattern 1 with brief explanation>
- <Pattern 2 with brief explanation>
- <Pattern 3 with brief explanation>

## Deployment
- CI/CD: <tool> `<workflow>`, triggers on <event>
- Deploy takes ~<time> (<steps summary>)
- Trigger pipelines: `<command>` (dry-run by default)

## Gotchas
- <Gotcha 1 -- specific, actionable>
- <Gotcha 2 -- specific, actionable>
- <Gotcha 3 -- specific, actionable>
- See `<topic>.md` for the full post-mortem
```

### Rules
- Each bullet should be self-contained and actionable
- Include tool/command names (not just descriptions)
- Link to topic files for detailed context
- Update test counts after significant test additions

## Layer 2: Topic Files

Deep-dive files for topics that outgrow MEMORY.md.

### When to Create
- A topic exceeds 3-4 lines in MEMORY.md
- A debugging session reveals deep insights worth preserving
- A pattern requires examples to be useful

### Naming
- Use kebab-case: `testing.md`, `api-patterns.md`, `deployment-lessons.md`
- Name by topic, not by date or session

### Format
Structure entries as Problem / Fix / Lesson, not chronologically:

```markdown
# Testing Patterns

## Async Database Mocking
**Problem:** Tests fail with "session already closed" errors.
**Fix:** Use `AsyncMock(spec=AsyncSession)` instead of plain `MagicMock`.
**Lesson:** Always spec async mocks to their async interface.

## Pre-commit Hook Failures
**Problem:** Commits fail due to formatting issues.
**Fix:** Run `<format command>` before committing.
**Lesson:** Configure editor to format on save.
```

### Linking
Always reference topic files from MEMORY.md:
```markdown
## Gotchas
- Never use `importlib.reload()` in tests -- corrupts module globals
- See `testing.md` for patterns and lessons
```

## Layer 3: Handovers

Transfer session context to the next session.

### When to Create
- Before ending a long coding session
- Before context window compression
- When switching between major focus areas
- Manual trigger: `/handover` command

### Location
`memory/HANDOVER-<YYYYMMDD>.md` (or with timestamp for multiple per day)

### Template

```markdown
# Session Handover - <Date>

## What Was Done
- <Completed task 1>
- <Completed task 2>

## Decisions Made
- <Decision with rationale>
- <Decision with rationale>

## In Progress
- <Task description> -- <current state>
- <Blocked on X> -- <what's needed>

## Pitfalls Discovered
- <Thing that didn't work and why>

## Next Steps
- [ ] <Next task 1>
- [ ] <Next task 2>
```

### Session Startup
Check for recent handovers at the start of each session:
```bash
ls -t memory/HANDOVER-*.md 2>/dev/null | head -3
```

## What to Save

- Stable patterns confirmed across multiple interactions
- Key architectural decisions and important file paths
- Solutions to recurring problems and debugging insights
- User preferences for workflow, tools, and communication style
- Explicit user requests ("always use X", "never do Y")

## What NOT to Save

- Session-specific context (current task details, in-progress work)
- Unverified conclusions from reading a single file
- Anything that duplicates CLAUDE.md instructions
- Speculative or unconfirmed information
- Temporary workarounds that should be fixed properly

## Update Cadence

| Layer | When to Update |
|-------|---------------|
| MEMORY.md | After significant discoveries or at session end |
| Topic files | When debugging reveals deep insights |
| Handovers | Before long sessions or switching focus areas |
