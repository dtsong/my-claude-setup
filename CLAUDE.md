# Claude Code - Daniel Song

Always use Context7 MCP when I need library/API documentation, code generation, setup or configuration steps without me having to explicitly ask.

When working on any sort of frontend work, use the /frontend-design skill without me having to explicitly ask, and be sure to follow the current project's existing styling conventions, if they exist.

## Node.js / NVM

When running `node`, `npm`, `npx`, or any Node.js tools, first source nvm:
```bash
source ~/.nvm/nvm.sh && nvm use default --silent && <your command>
```

## Session Handovers

At the start of each session, check for recent handover documents:
```bash
ls -t memory/HANDOVER-*.md 2>/dev/null | head -3
```
If handovers exist, read the most recent one to pick up context from the previous session.
