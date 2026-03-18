---
name: workflow
description: "Use when planning implementation steps, deciding commit format, or structuring development approach. Provides brainstorm-plan-implement flow with conventional commits. Triggers on 'how should I approach this', 'commit format'."
model: sonnet
---

# Workflow

## Scope Constraints

- Advisory skill defining development process, commit format, and coding discipline
- Does not execute commands, modify files, or interact with git directly
- Boundaries: delegates git operations to git-status, git-workflows, and github-workflow skills

## Input Sanitization

- Commit messages: free text, reject null bytes
- Plan content: free text, reject null bytes

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

## Output Format

```
Plan: add email validation to signup form

1. Write test for valid/invalid emails
2. Add validateEmail() to src/lib/validators.ts
3. Wire into SignupForm.tsx onSubmit
4. Run tests, verify build

Commit: feat: add email validation to signup form

Open questions: none
```

## Gotchas

- Amending (`--amend`) after a pre-commit hook failure destroys the previous commit — hook failure means commit didn't happen, so `--amend` modifies the WRONG commit. Always create a new commit after fixing hook issues.
- `git add .` or `git add -A` stages secrets (`.env`, credentials) — always add specific files by name
- Skipping verification ("it works, I'll just commit") leads to broken builds — always run the actual test/build command and check output before committing

## Don'ts
- Don't refactor unrelated code
- Don't add dependencies without asking
- Don't skip verification step
