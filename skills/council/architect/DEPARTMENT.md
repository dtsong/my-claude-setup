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
| [distributed-patterns](distributed-patterns/SKILL.md) | Distributed system patterns and trade-offs | default | `distributed`, `consensus`, `partition`, `saga`, `CRDT`, `event sourcing`, `microservices` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Request mentions codebase analysis, project structure, tech stack discovery, or architecture overview | codebase-context | High |
| Request involves database tables, schema changes, migrations, entity relationships, or data modeling | schema-design | High |
| Request involves API endpoints, REST/RPC contracts, request/response types, or error handling | api-design | High |
| Request mentions infrastructure constraints, hosting, deployment, or integration points | codebase-context | Medium |
| Distributed system, consensus, partition, saga, CRDT, event sourcing, microservices, CAP, Raft, Paxos | distributed-patterns | High |
| Request mentions data access patterns, indexing, or query optimization | schema-design | Medium |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
