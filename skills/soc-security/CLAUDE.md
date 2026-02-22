# SoC Security Skills

## Skill Governance Directive

# Skill Governance Directive (v1.3)

All skills in this repository must comply with the Skill Governance
Specification and the Skill Security Hardening Specification.

## Security (Hard — Blocks Commits)

- No references to credential stores, key files, dotfiles, or system directories
  without `# SECURITY: <justification>` annotation on or near the flagged line
- No prompt injection patterns: identity manipulation, safety overrides, data
  exfiltration instructions, privilege escalation
- No dangerous commands in scripts (network, eval, exec, destructive ops) without
  explicit declaration in the skill's Scripts section
- Script checksums must match `scripts.lock` when present
- Every skill must include a `## Scope Constraints` section declaring what it
  can and cannot access
- Skills accepting user input must include `## Input Sanitization` before using
  that input in commands or file paths

Repo-wide suppressions: `pipeline/config/security-suppressions.json`

## Structural Integrity (Hard — Blocks Commits)

- Coordinators contain ONLY: classification logic, skill registry, load directive, handoff protocol
- Load one specialist at a time — never pre-load multiple specialists
- No cross-references between specialist skills — use handoff protocol
- All referenced files must exist on disk
- **One-level-deep references** — reference files must NOT reference other reference files
- Reference files >100 lines must include a table of contents
- Suite context load ceiling: ≤5,500 tokens (coordinator + largest specialist + largest reference)
- Eval cases and templates live outside skill directories

## Token Budgets (Advisory — Warns Only)

- Coordinator: ≤800 tokens (~600 words)
- Specialist / Standalone: ≤2,000 tokens (~1,500 words)
- Reference: ≤1,500 tokens (~1,100 words)
- Exceeding targets is acceptable when justified by output quality
- Document overrides in `pipeline/config/budgets.json` with eval data

## Description Quality (Advisory — Warns Only)

- **Third person** — no "I can" or "you should" (injected into system prompt)
- **≥20 words** (target 40-80) with activation directive opening
- **Negative boundaries** — "Do NOT use for..." with correct alternative named
- **MCP tools** use `ServerName:tool_name` format (not bare tool names)
- See `SKILL-TRIGGER-RELIABILITY-SPEC.md` for full description formula

## Model Routing

Skills declare model preferences in frontmatter (`model.preferred`, `model.minimum`).
Budget zones trigger automatic degradation:
- Green (0-70% budget): use preferred models
- Yellow (70-90%): downgrade low/medium reasoning_demand skills
- Red (90-100%): downgrade all skills to minimum tier

Coordinators default to sonnet. Mechanical tasks (file tracing, pattern matching)
use sonnet. Analytical tasks (classification, code review) use sonnet. Complex
reasoning (debugging, architecture) uses opus.

User overrides always win. Skill `minimum` is respected unless explicitly overridden.

Config: `pipeline/config/model-routing.yaml`
Full spec: `pipeline/specs/SKILL-MODEL-ROUTING-SPEC.md`

## Writing Rules

- **Conciseness hierarchy**: (1) Claude already knows this → cut. (2) Removing it hurts evals → keep. (3) Sentence earns its place.
- **Degrees of freedom**: Low (fragile ops → exact commands), Medium (known pattern → default + escape hatch), High (context-dependent → criteria not commands). Calibrate per step.
- Procedure steps use imperative sentences — no explanatory prose
- Add contextual reasoning when it prevents known failure modes
- Decision points as inline conditionals — no nested sub-sections
- One compact output example per skill — no redundant schema descriptions
- Checklists >10 items go in reference files loaded conditionally
- No temporal references without version context ("deprecated since v2.1")

## Resilience (Long Procedures)

- Progress checklist for procedures with >5 steps
- Compaction recovery note for multi-turn skills
- State checkpoint files for destructive operations
- Feedback loops: action → validate → fix → re-validate → proceed

## Script Quality (Advisory — Warns Only)

- Explicit error handling (no bare exceptions)
- Documented constants (no magic numbers)
- Verbose error messages for agent self-correction
- Dependencies listed with install commands

## Platform Features (Claude Code)

- `context: fork` available for subagent isolation
- Shell preprocessing (`!command`) injects live data before reasoning
- Both are optional — skills should work without them

## Priority Order

1. Output quality  2. Security  3. Structure  4. Token efficiency (model routing)  5. Compression

## Enforcement

Pre-commit hooks validate: security, frontmatter, references, isolation,
context load, triggers (description quality, third person, MCP format),
token budgets (warn only), prose patterns (warn only), script quality (warn only).

Run `pre-commit run --all-files` to check compliance manually.
Run `skill-audit` for a categorized compliance report.
Run `skill-security` for security scan only.

## Development Workflow

Use the Claude A/B workflow: Claude A designs the skill, Claude B (fresh instance)
tests on real tasks. Observe navigation patterns. Iterate based on actual behavior.

## Eval Dimensions

Three types: **trigger evals** (does it activate?), **output evals** (correct result?),
**navigation evals** (reads the right files?). All three are necessary.

Full specs:
- `pipeline/specs/SKILL-GOVERNANCE-SPEC.md`
- `pipeline/specs/SKILL-SECURITY-SPEC.md`
- `pipeline/specs/SKILL-MODEL-ROUTING-SPEC.md`
- `pipeline/specs/SKILL-TRIGGER-RELIABILITY-SPEC.md`

<!-- /skill-governance -->

## Development Setup

```bash
# Install pre-commit hooks
pip install pre-commit pyyaml
pre-commit install
pre-commit install --hook-type commit-msg

# Source shell helpers (add to your shell profile)
source pipeline/shell-helpers.sh
```

## Budget Configuration

Token budgets are configured in `pipeline/config/budgets.json`. Per-file budgets
are advisory targets — they warn but never block commits. Document overrides with
rationale when exceeding targets improves output quality.

## Commit Convention

```
skill(name): description          -- new skill or major change
skill-fix(name): description      -- bug fix
skill-ref(name): description      -- refactor (no behavior change)
skill-eval(name): description     -- eval case changes
skill-docs(name): description     -- documentation only
chore(pipeline): description      -- pipeline/tooling changes
```
