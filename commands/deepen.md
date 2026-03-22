---
description: "Codebase architecture review — find shallow modules, tight coupling, and deepening opportunities"
argument-hint: "[PATH or SCOPE...]"
---

# /deepen — Architecture Review

Explore the codebase for structural improvement opportunities. Finds shallow modules, unnecessary abstractions, and tight coupling — then presents concrete deepening candidates.

## Usage

```
/deepen
/deepen src/api
/deepen "the auth system"
```

## Instructions

When the user runs `/deepen`, follow these steps:

### 1. Scope Resolution

If a path or scope is provided in `$ARGUMENTS`, focus there. Otherwise, scan the project root.

Detect workspace: `git rev-parse --show-toplevel` or `$PWD`. Read project structure, tech stack markers (`package.json`, `pyproject.toml`, etc.), and `CLAUDE.md` for conventions.

### 2. Explore Module Boundaries

Map the codebase structure within scope:
- Directory layout and module organization
- Public interfaces (exports, API surfaces, entry points)
- Import relationships between modules
- Test file locations relative to source

Use Explore agents for large scopes — up to 3 in parallel, each focused on a different area.

### 3. Evaluate Against Deepening Criteria

Load `commands/references/deepening-criteria.md` for the evaluation rubric.

For each module or area, assess:
- **Depth ratio** — is the interface small relative to the implementation?
- **Abstraction value** — does each layer earn its complexity?
- **Coupling** — how entangled are modules with each other?
- **Coherence** — can you understand one concept without bouncing between files?

### 4. Present Deepening Opportunities

For each finding, present:

```
### [Module/Area Name]

**Signal:** [which criterion triggered — e.g., "Shallow module", "Tight coupling"]
**Evidence:** [specific files, exports, import counts]
**Suggestion:** [concrete action — merge these modules, simplify this interface, hide this behind X]
**Impact:** [High/Medium/Low — how much complexity this eliminates]
```

### 5. Prioritize and Recommend

Rank opportunities by impact-to-effort ratio. Recommend a starting point — the change that unlocks the most clarity for the least disruption.

If findings are extensive, suggest: "Run `/council` on the top candidates for deeper architectural deliberation."

### Important Rules

- This is a read-only analysis — do NOT modify any code
- Focus on structure, not style (naming, formatting are out of scope)
- Do not flag things that are intentionally simple (utilities, constants, config)
- One concept = one finding. Don't combine unrelated issues.
- Present at most 7 findings — prioritize ruthlessly
