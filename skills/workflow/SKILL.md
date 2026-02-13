---
name: workflow
description: "Enforce commit format and coding discipline rules for this project. Auto-loaded for commits. Not for: git operations (use git-workflows) or GitHub interactions (use github-workflow)."
model: sonnet
---

# Workflow

## Development Flow
1. Brainstorm → plan → implement (for non-trivial features)
2. Write failing test first, then implementation
3. Verify with actual command output before marking done

## Commits
Format: `<type>: <description>`
Types: feat, fix, refactor, test, docs, chore

## Plans
- Make extremely concise. Sacrifice grammar for concision.
- End with list of unresolved questions, if any.

## Don'ts
- Don't refactor unrelated code
- Don't add dependencies without asking
- Don't skip verification step
