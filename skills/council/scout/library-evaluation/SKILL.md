---
name: "library-evaluation"
department: "scout"
description: "Use when adding new packages, choosing between dependency alternatives, or auditing existing libraries. Covers popularity metrics, maintenance health, bundle impact, API quality, and license compatibility with weighted scoring. Do not use for evaluating frameworks or platforms (use technology-radar) or comparing competing products (use competitive-analysis)."
version: 1
triggers:
  - "library"
  - "package"
  - "dependency"
  - "npm"
  - "install"
  - "module"
  - "third-party"
---

# Library Evaluation

## Purpose

Produce a structured, weighted comparison of candidate libraries to make dependency decisions based on evidence rather than familiarity or hype.

## Scope Constraints

- Evaluates individual libraries and packages, not full frameworks or platforms.
- Focuses on technical fitness for the project, not market positioning or competitive landscape.
- Does not perform security audits; flag security concerns for handoff to the appropriate skill.

## Inputs

- The need or problem the library should solve
- Any known candidates (or let the process discover them)
- Project constraints (bundle size budget, license requirements, framework compatibility)
- Current tech stack and existing dependencies

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Step 1: Identify Candidate Libraries

- Search npm, GitHub, and community recommendations for the problem space
- Include the most popular option, the most recently trending option, and at least one lightweight alternative
- Note any candidates already in use in the codebase's dependency tree

### Step 2: Evaluate Popularity Metrics

For each candidate:
- npm weekly downloads (absolute number and trend direction)
- GitHub stars and recent star velocity
- Community size (Discord, Stack Overflow tags, GitHub Discussions activity)
- Notable adopters (large companies or well-known projects using it)

### Step 3: Assess Maintenance Health

For each candidate:
- **Commit frequency:** Active development or maintenance-only?
- **Issue response time:** Median time to first response on new issues
- **Release cadence:** Regular releases or long gaps?
- **Bus factor:** Single maintainer or team? Corporate backing?
- **Breaking change history:** How are major versions handled?

### Step 4: Measure Bundle Impact

For each candidate:
- Gzipped bundle size (via bundlephobia or similar)
- Tree-shaking support (ESM exports, side-effect-free)
- Dependency count (transitive dependencies and their health)
- Runtime performance characteristics if applicable

### Step 5: Review API Quality and Developer Experience

For each candidate:
- TypeScript support (built-in types, DefinitelyTyped, quality of types)
- Documentation quality (getting started guide, API reference, examples)
- API ergonomics (intuitive naming, sensible defaults, composability)
- Migration path from current solution if applicable

### Step 6: Check License Compatibility

For each candidate:
- License type (MIT, Apache 2.0, ISC, GPL, etc.)
- Compatibility with project's license
- Transitive dependency license concerns
- Any commercial use restrictions

### Step 7: Produce Weighted Comparison Score

- Assign weights based on project priorities (e.g., bundle size matters more for client-side)
- Score each criterion 1-5
- Calculate weighted total
- Flag any deal-breakers that override the score

### Progress Checklist

- [ ] Step 1: Candidates identified
- [ ] Step 2: Popularity metrics evaluated
- [ ] Step 3: Maintenance health assessed
- [ ] Step 4: Bundle impact measured
- [ ] Step 5: API quality reviewed
- [ ] Step 6: License compatibility checked
- [ ] Step 7: Weighted comparison scored

> **Compaction resilience:** If context was compacted, re-read this SKILL.md and check the Progress Checklist for completed steps before continuing.

## Handoff

- If license or security concerns emerge, recommend loading skeptic/threat-model for threat analysis.
- If the evaluation reveals broader framework or platform adoption questions, recommend loading scout/technology-radar.

## Output Format

### Library Comparison Matrix

| Criterion | Weight | Candidate A | Candidate B | Candidate C |
|-----------|--------|-------------|-------------|-------------|
| Weekly downloads | ... | .../5 | .../5 | .../5 |
| Maintenance health | ... | .../5 | .../5 | .../5 |
| Bundle size | ... | .../5 | .../5 | .../5 |
| TypeScript support | ... | .../5 | .../5 | .../5 |
| API quality | ... | .../5 | .../5 | .../5 |
| License | ... | .../5 | .../5 | .../5 |
| **Weighted Total** | | **...** | **...** | **...** |

### Recommendation

**Recommended:** [Library Name]
**Rationale:** [2-3 sentence justification referencing the top differentiating factors]
**Risks:** [Known risks or caveats with the recommendation]
**Migration notes:** [If replacing an existing dependency, key migration steps]

## Quality Checks

- [ ] At least 3 candidate libraries evaluated
- [ ] npm download trends checked (not just absolute numbers)
- [ ] Maintenance health assessed (commit frequency, issue response, bus factor)
- [ ] Bundle size measured with gzipped numbers
- [ ] TypeScript support quality verified
- [ ] License compatibility confirmed
- [ ] Weighted scores reflect project-specific priorities
- [ ] Deal-breakers explicitly called out

## Evolution Notes
<!-- Observations appended after each use -->
