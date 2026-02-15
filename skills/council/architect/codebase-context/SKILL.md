---
name: "codebase-context"
department: "architect"
description: "Use when analyzing an existing codebase for architecture, tech stack, conventions, and infrastructure. Covers project structure mapping, data model discovery, integration point cataloging, and constraint identification. Do not use for schema changes (use schema-design) or API contract definition (use api-design)."
version: 1
triggers:
  - "codebase"
  - "context"
  - "architecture"
  - "infrastructure"
  - "tech stack"
  - "project structure"
---

# Codebase Context

## Purpose

Analyze the existing codebase and produce a comprehensive context briefing covering architecture, data model, patterns, and constraints. This output becomes shared context for ALL council agents — it is the foundation every other skill builds on.

## Scope Constraints

- Produces read-only analysis; does not modify any project files.
- Covers architecture, data model, conventions, infrastructure, and integrations.
- Does not design new schemas or API contracts — hand off to schema-design or api-design.

## Inputs

- Project root directory ($WORKSPACE)
- Any existing CLAUDE.md or project documentation
- Package manifests (package.json, pyproject.toml, Cargo.toml, etc.)
- Configuration files (tsconfig.json, next.config.js, .env.example, etc.)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
<!-- Track completion across compaction boundaries -->
- [ ] Step 1: Read Project Configuration
- [ ] Step 2: Map Directory Structure
- [ ] Step 3: Identify Core Architectural Patterns
- [ ] Step 4: Map the Existing Data Model
- [ ] Step 5: Catalog Key Conventions
- [ ] Step 6: Note Infrastructure Constraints
- [ ] Step 7: Identify Integration Points

### Step 1: Read Project Configuration

Read CLAUDE.md, package.json (or equivalent), tsconfig, and any config files at the project root. Extract framework, language version, key dependencies, and build tooling.

### Step 2: Map Directory Structure

List top-level directories and identify their purposes. Recurse one level into key directories (src/, app/, lib/, components/, etc.) to understand the organizational pattern.

### Step 3: Identify Core Architectural Patterns

Determine the routing approach (file-based, config-based), data fetching strategy (SSR, SSG, CSR, RSC), state management solution, and component patterns (atomic, feature-based, etc.).

### Step 4: Map the Existing Data Model

Read database schema files, migration history, or ORM models. List tables, their relationships, key entities, and access control policies (e.g., RLS policies for Supabase).

### Step 5: Catalog Key Conventions

Identify naming conventions (camelCase vs snake_case, file naming), file structure patterns, import conventions (barrel exports, path aliases), and error handling patterns used throughout the codebase.

### Step 6: Note Infrastructure Constraints

Document hosting platform, database type and version, auth provider, CDN configuration, edge function usage, environment variable patterns, and deployment pipeline.

### Step 7: Identify Integration Points

Catalog external APIs, webhooks, third-party services, and any inter-service communication patterns. Note authentication methods for each integration.

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Handoff

- If the analysis reveals schema issues, inconsistencies, or new entity requirements, recommend loading architect/schema-design.
- If the analysis reveals API surface gaps, endpoint inconsistencies, or missing contracts, recommend loading architect/api-design.

## Output Format

```markdown
# Context Briefing

## Tech Stack
- **Framework**: [name + version]
- **Language**: [name + version]
- **Database**: [type + provider]
- **Auth**: [provider + method]
- **Hosting**: [platform]
- **Key Dependencies**: [list with versions]

## Directory Structure
```
[tree output with annotations]
```

## Architectural Patterns
- **Routing**: [approach]
- **Data Fetching**: [strategy]
- **State Management**: [solution]
- **Component Pattern**: [style]

## Data Model
| Entity | Key Fields | Relationships |
|--------|-----------|---------------|
| ...    | ...       | ...           |

[ASCII relationship diagram if complex]

## Conventions
1. [Convention with example]
2. [Convention with example]
3. [Convention with example]

## Infrastructure Constraints
- [Constraint and implication]
- [Constraint and implication]

## Integration Points
| Service | Purpose | Auth Method |
|---------|---------|-------------|
| ...     | ...     | ...         |

## Warnings / Tech Debt
- [Known issue or constraint that affects design decisions]
```

## Quality Checks

- [ ] No hardcoded file paths — all paths are relative to $WORKSPACE
- [ ] All 7 process areas are covered in the output
- [ ] At least 3 conventions are identified and documented with examples
- [ ] Tech stack versions are specified (not just names)
- [ ] Data model section includes relationships, not just entity lists
- [ ] Integration points include auth methods
- [ ] Warnings section flags any constraints that would affect new feature design

## Evolution Notes
<!-- Observations appended after each use -->
