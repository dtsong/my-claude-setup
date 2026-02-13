# Claude Code - Daniel Song

## System Behaviors

### Skill Matching Override

For skill matching behavior, use the local `skills/skill-matching/SKILL.md` skill.
It supersedes the superpowers using-superpowers skill's matching rules.

### Skill Transparency Protocol

When a skill is activated, briefly announce it:
```
[Skill: <name>] — <one-line reason>
```
Announce once per skill per session. If the user says "skip skill announcements"
or "quiet mode", stop announcing.

### TDD Skill Override

For TDD guidance, use the local `skills/tdd/SKILL.md` skill. Ignore the superpowers test-driven-development skill — the local version is a comprehensive merge that supersedes it.

### Node.js / NVM

When running `node`, `npm`, `npx`, or any Node.js tools, first source nvm:
```bash
source ~/.nvm/nvm.sh && nvm use default --silent && <your command>
```

### Session Handovers

At the start of each session, check for recent handover documents:
```bash
ls -t memory/HANDOVER-*.md 2>/dev/null | head -3
```
If handovers exist, read the most recent one to pick up context from the previous session.

## Personal Preferences

Always use Context7 MCP when I need library/API documentation, code generation, setup or configuration steps without me having to explicitly ask.

When working on any sort of frontend work, use the /frontend-design skill without me having to explicitly ask, and be sure to follow the current project's existing styling conventions, if they exist.
