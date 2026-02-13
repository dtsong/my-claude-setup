---
name: code-search
description: "Fast codebase searches using grep and glob patterns. Triggers on: find function, search for, where is, grep for. Not for: git-specific searches (use git-status) or GitHub code search."
model: haiku
tools: [Grep, Glob, Read]
---

# Code Search

Use Grep for content searches, Glob for file pattern matching.

## Examples
- "find all usages of X" → Grep for X
- "where is the config file" → Glob for config patterns
- "search for error handling" → Grep for try/catch, .catch, error patterns
