---
name: "Architect Department"
executive: "Architect"
color: "Blue"
description: "System design, data models, APIs, integration patterns"
---

# Architect Department — Blue Lens

The Architect's department of focused skills for systems thinking, data modeling, and API design.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [codebase-context](codebase-context/SKILL.md) | Deep infrastructure analysis and context briefing | default | `codebase`, `context`, `architecture`, `infrastructure` |
| [schema-design](schema-design/SKILL.md) | Migration-ready database schema design | default | `database`, `schema`, `table`, `migration`, `data model` |
| [api-design](api-design/SKILL.md) | REST/RPC endpoint contracts and types | default | `API`, `endpoint`, `route`, `REST`, `RPC` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Request mentions codebase analysis, project structure, tech stack discovery, or architecture overview | codebase-context | High |
| Request involves database tables, schema changes, migrations, entity relationships, or data modeling | schema-design | High |
| Request involves API endpoints, REST/RPC contracts, request/response types, or error handling | api-design | High |
| Request mentions infrastructure constraints, hosting, deployment, or integration points | codebase-context | Medium |
| Request mentions data access patterns, indexing, or query optimization | schema-design | Medium |

## Load Directive

Load one specialist skill at a time using the Skill tool. Read the classification logic table to select the appropriate specialist, then invoke the skill. Do not pre-load multiple specialists simultaneously.

## Handoff Protocol

When the specialist skill output reveals issues in another department's domain:
1. Complete the current skill's output format.
2. Note the cross-domain findings in the output.
3. Recommend loading the appropriate department and skill (e.g., "Hand off data model compliance requirements to guardian/data-classification for sensitivity classification").
