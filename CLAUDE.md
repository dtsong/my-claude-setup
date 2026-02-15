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

## Skill Governance Directive

All skills in this repository must comply with the Skill Governance Specification.

### Token Budgets (Hard Limits)

- Coordinator SKILL.md: ≤800 tokens (~600 words)
- Specialist / Standalone SKILL.md: ≤2,000 tokens (~1,500 words)
- Reference files: ≤1,500 tokens (~1,100 words)
- Maximum simultaneous context load: ≤5,000 tokens

### Architecture Rules

- Coordinators contain ONLY: classification logic, skill registry, load directive, handoff protocol
- Load one specialist at a time — never pre-load multiple specialists
- Checklists >10 items go in reference files, loaded conditionally
- Eval cases and templates live outside skill directories
- No cross-references between specialist skills — use handoff protocol

### Writing Rules

- Procedure steps use imperative sentences — no explanatory prose
- Decision points as inline conditionals — no nested sub-sections
- One compact output example per skill — no redundant schema descriptions
- Reference files are pure content — no preamble or meta-instructions

### Enforcement

Pre-commit hooks validate: token budgets, frontmatter, reference integrity,
cross-skill isolation, and suite context load ceiling.

Run `pre-commit run --all-files` to check compliance manually.

Full spec: `pipeline/specs/SKILL-GOVERNANCE-SPEC.md`
