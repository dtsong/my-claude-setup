# React Best Practices (Vercel)

This skill is a lightweight stub that fetches the latest guidance from Vercel's upstream repository at runtime.

## Upstream

- Repository: https://github.com/vercel-labs/agent-skills/tree/main/skills/react-best-practices
- Announcement: https://vercel.com/blog/introducing-react-best-practices

## How It Works

The skill definition (`SKILL.md`) points to Vercel's compiled rulebook:

- https://raw.githubusercontent.com/vercel-labs/agent-skills/main/skills/react-best-practices/AGENTS.md

Fetch that file during use so the rules stay current.

## Keeping This Up To Date / Offline Use

If you want an offline snapshot, install the upstream repo separately and link it into your Claude Code skills directory.

Example:

```bash
mkdir -p ~/.claude/skills
git clone https://github.com/vercel-labs/agent-skills ~/.claude/skills/_upstream-agent-skills
ln -sfn ~/.claude/skills/_upstream-agent-skills/skills/react-best-practices ~/.claude/skills/react-best-practices
```
