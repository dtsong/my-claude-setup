---
description: "DEPRECATED — invoke the superpowers:test-driven-development skill"
argument-hint: "[TASK, ISSUE URL, or BUG DESCRIPTION...]"
---

# /tdd — Deprecated

This command was a thin wrapper. Invoke the `superpowers:test-driven-development`
skill directly with the task as context — it owns the red-green-refactor
discipline, including the no-production-code-without-a-failing-test rule.

If the user invoked `/tdd <task>`, invoke that skill now with `<task>`
(fetching GitHub issue details via `gh issue view` if the task is an issue
URL) and mention the new entry point once.
