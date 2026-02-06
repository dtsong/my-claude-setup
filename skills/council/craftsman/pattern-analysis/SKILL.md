---
name: "Pattern Analysis"
department: "craftsman"
description: "Audit codebase patterns and conventions, evaluate proposed changes for consistency"
version: 1
triggers:
  - "pattern"
  - "convention"
  - "consistency"
  - "refactor"
  - "code quality"
  - "style"
  - "architecture"
  - "anti-pattern"
  - "code review"
  - "DX"
---

# Pattern Analysis

## Purpose

Audit the codebase for existing patterns and conventions, then evaluate proposed changes for consistency.

## Inputs

- Codebase or directory to audit
- Proposed changes or new code to evaluate (if applicable)
- Specific concerns or areas of focus (if any)
- Known tech stack and framework conventions

## Process

### Step 1: Scan Structural Patterns

- **File naming conventions:**
  - kebab-case, PascalCase, camelCase, snake_case
  - Suffix conventions (.utils.ts, .types.ts, .test.ts, .stories.tsx)
- **Directory organization:**
  - Feature-based (feature/components, feature/hooks, feature/utils)
  - Layer-based (components/, hooks/, utils/, types/)
  - Hybrid approaches
- **Module export patterns:**
  - Barrel files (index.ts re-exports)
  - Direct imports
  - Default vs named exports

### Step 2: Identify Code Patterns

- **Component patterns:**
  - Server vs client components (React Server Components)
  - Composition patterns (render props, compound components, HOCs)
  - Prop drilling vs context vs stores
- **Data fetching patterns:**
  - Custom hooks (useQuery, useSWR, custom fetch hooks)
  - Server actions
  - API routes
  - Direct fetch in server components
- **State management patterns:**
  - Local state (useState, useReducer)
  - Context (React Context, providers)
  - External stores (Zustand, Jotai, Redux)
  - URL state (search params, pathname)
- **Error handling patterns:**
  - try/catch blocks
  - Result/Either types
  - Error boundaries
  - Toast notifications
- **Type patterns:**
  - interfaces vs type aliases
  - Generic patterns and utility types
  - Zod schemas vs manual types
  - Shared type files vs co-located types

### Step 3: Catalog Existing Conventions

Document discovered conventions:

| Category | Convention | Example File | Frequency |
|----------|-----------|--------------|-----------|
| File naming | ... | ... | ... |
| Component style | ... | ... | ... |
| Data fetching | ... | ... | ... |
| State management | ... | ... | ... |
| Error handling | ... | ... | ... |
| Type definitions | ... | ... | ... |
| Import ordering | ... | ... | ... |
| Comment style | ... | ... | ... |
| Testing patterns | ... | ... | ... |

### Step 4: Evaluate Proposed Changes

For each proposed change, check:
- **Does it follow existing naming conventions?** (files, variables, functions, components)
- **Does it follow existing structural patterns?** (directory placement, export style)
- **Does it reuse existing utilities/helpers?** (don't reinvent what exists)
- **Does it introduce a new pattern?** If so:
  - Is the new pattern justified? (existing pattern inadequate, new requirement)
  - Is it better enough to warrant migration? Or just different?
  - Will it cause confusion having two patterns for the same thing?
- **Does it create inconsistency with similar existing code?** (same feature, neighboring files)

### Step 5: Produce Recommendations

- **Follow these patterns** (with file references as examples):
  - Pattern A: See `src/components/ExampleComponent.tsx`
  - Pattern B: See `src/hooks/useExampleHook.ts`
- **Avoid these patterns** (with rationale):
  - Anti-pattern X: Because [reason]
  - Deprecated pattern Y: Replaced by [alternative]
- **Consider refactoring** (if new patterns are genuinely better):
  - Migrate pattern A to pattern B across [scope]
  - Estimated scope: [number of files affected]

## Output Format

### Pattern Inventory

| Category | Pattern | Example File | Frequency | Status |
|----------|---------|--------------|-----------|--------|
| File naming | kebab-case components | `src/components/team-card.tsx` | High | Standard |
| Data fetching | useQuery hooks | `src/hooks/use-teams.ts` | High | Standard |
| ... | ... | ... | ... | ... |

### Consistency Report

| Proposed Change | Existing Pattern | Match? | Recommendation |
|----------------|-----------------|--------|----------------|
| ... | ... | Yes/No | ... |

### Recommendations

1. **Follow:** [pattern] — see [file reference]
2. **Avoid:** [anti-pattern] — because [rationale]
3. **Refactor:** [migration suggestion] — [scope and effort]

## Quality Checks

- [ ] At least 3 file/code categories audited (naming, structure, data fetching, state, errors)
- [ ] Naming conventions documented with examples
- [ ] Data fetching pattern identified and documented
- [ ] State management pattern identified and documented
- [ ] New code evaluated against each discovered pattern
- [ ] Example files referenced for each pattern
- [ ] Anti-patterns identified with rationale
- [ ] Recommendations are actionable (not vague)

## Evolution Notes
<!-- Observations appended after each use -->
