---
description: "DEPRECATED — use the built-in /code-review with --fix"
argument-hint: "[--max-cycles N]"
---

# /review-fix — Deprecated

The built-in `/code-review` command now covers this loop:

```
/code-review high --fix     # review the current diff, then apply the findings
```

Effort levels low/medium/high/max control breadth; `ultra` runs a multi-agent
cloud review. `--comment` posts findings as inline PR comments instead.

If the user invoked `/review-fix`, run `/code-review high --fix` on their
behalf now and mention the new entry point once.
