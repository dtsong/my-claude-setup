# Council for Claude.ai

Portable versions of the `/council` and `/brainstorm` workflows for Claude.ai Projects.

## Setup

### Brainstorm (quick 3-agent gut check)

1. Go to [claude.ai](https://claude.ai) and create a new Project
2. Open Project Settings > Custom Instructions
3. Paste the contents of [`brainstorm-project.md`](brainstorm-project.md)
4. Start a conversation and describe any idea

### Full Council (multi-round deliberation)

1. Create a new Project in Claude.ai
2. Paste [`council-project.md`](council-project.md) into Custom Instructions
3. Start a conversation with "council: [your idea]"
4. The Steward will interview you, assemble agents, and run 3 rounds of deliberation

## Differences from Claude Code

| Feature | Claude Code | Claude.ai |
|---------|-------------|-----------|
| Agent execution | Parallel subagents | Sequential role-play |
| Codebase access | Full file system | User provides context |
| Session persistence | File-based sessions | Conversation history only |
| Agent depth | Full persona files | Compressed summaries |
| Skills system | 60+ loadable skills | Not available |
| Output | Files written to disk | Artifacts in conversation |

## Tips

- Paste relevant code or architecture docs into the conversation. Agents can't explore your codebase.
- Start with brainstorm. It'll recommend whether to go deeper.
- After assembly, tell the Steward to swap agents if the selection doesn't fit.
- Ask for the synthesis as an artifact so you can reference it later.
