---
name: vercel-react-best-practices
description: "Optimize React and Next.js performance following Vercel Engineering guidelines. Triggers on: React component, Next.js page, bundle optimization, data fetching. Not for: non-React frontend frameworks or backend API performance."
license: MIT
metadata:
  author: vercel
  version: "1.0.0"
---

# React Best Practices (Upstream)

This is a lightweight *stub skill* that fetches the latest React Best Practices guidance from Vercel's upstream repository at runtime.

It intentionally avoids vendoring the full rule set so updates can be adopted quickly and attribution stays clear.

## Upstream Sources

- Repository: https://github.com/vercel-labs/agent-skills/tree/main/skills/react-best-practices
- Announcement: https://vercel.com/blog/introducing-react-best-practices

## Guidelines Source

Fetch fresh guidance before each review:

```text
https://raw.githubusercontent.com/vercel-labs/agent-skills/main/skills/react-best-practices/AGENTS.md
```

## Process

1. Fetch the upstream `AGENTS.md`.
2. Use it as the authoritative rulebook for React/Next.js performance.
3. Apply relevant rules to the current code/task.

## Output Format

- Provide actionable recommendations.
- When possible, cite the upstream rule section heading (and/or a short identifier) so the change can be traced to the upstream guidance.

## Quality Checks

- Do not propose micro-optimizations if there are obvious waterfalls or bundle bloat issues.
- Prefer changes that are correct-by-construction (avoid flaky memoization patterns).
- Be explicit about trade-offs and when not to apply a rule.

## Offline Snapshot (Optional)

If you want an offline copy of the full rule set, install the upstream repo separately and link it into your Claude Code skills directory.

See `skills/vercel-react-best-practices/README.md` for an example.
