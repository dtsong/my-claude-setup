---
name: "schema-design"
department: "architect"
description: "Use when designing or modifying database schemas with migration plans. Covers entity definition, relationship mapping, normalization trade-offs, indexing strategies, and RLS policies. Do not use for API endpoint contracts (use api-design) or codebase analysis (use codebase-context)."
version: 1
triggers:
  - "database"
  - "schema"
  - "data model"
  - "table"
  - "migration"
  - "entity"
  - "relationship"
  - "foreign key"
  - "index"
  - "normalization"
---

# Schema Design

## Purpose

Design relational database schemas with normalization trade-offs, migration plans, and indexing strategies. Produces migration-ready SQL that can be applied directly to the database.

## Scope Constraints

- Produces schema definitions and migration SQL only; does not execute migrations.
- Covers entity design, relationships, indexes, RLS policies, and rollback plans.
- Does not define API contracts or endpoint shapes — hand off to api-design.

## Inputs

- Feature requirements (from interview/idea phase)
- Existing schema (current tables, relationships, migrations)
- Query patterns (how the data will be read — drives index and denormalization decisions)
- Access control requirements (who can read/write which rows)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
<!-- Track completion across compaction boundaries -->
- [ ] Step 1: Inventory Existing Entities
- [ ] Step 2: Identify New Entities Needed
- [ ] Step 3: Define Entity Attributes
- [ ] Step 4: Map Relationships
- [ ] Step 5: Apply Normalization
- [ ] Step 6: Design Indexes
- [ ] Step 7: Plan RLS Policies
- [ ] Step 8: Draft Migration SQL

### Step 1: Inventory Existing Entities

Read current schema files, migration history, or ORM models. List all existing tables with their columns, types, constraints, and relationships. Note any existing indexes and RLS policies.

### Step 2: Identify New Entities Needed

From the feature requirements and interview output, determine what new data needs to be stored. List candidate entities and their purpose.

### Step 3: Define Entity Attributes

For each new entity, define:
- Column name, data type, and nullability
- Default values and constraints (UNIQUE, CHECK, etc.)
- Primary key strategy (UUID vs serial vs composite)
- Timestamp columns (created_at, updated_at)

### Step 4: Map Relationships

Define all relationships between entities:
- **1:1** — Foreign key with UNIQUE constraint
- **1:N** — Foreign key on the "many" side
- **N:M** — Junction/through table with composite primary key
- Document cascade behavior (ON DELETE CASCADE vs SET NULL vs RESTRICT)

### Step 5: Apply Normalization

Default to 3NF. For each denormalization decision, document:
- What is being denormalized
- Why (query performance, read frequency, join cost)
- How consistency is maintained (triggers, application logic, eventual consistency)

### Step 6: Design Indexes

Drive index choices from query patterns:
- Single-column indexes for filtered/sorted columns
- Composite indexes for multi-column WHERE clauses (column order matters)
- Partial indexes for filtered subsets (WHERE active = true)
- GIN indexes for array/JSONB columns if applicable

### Step 7: Plan RLS Policies

If using Supabase or row-level security:
- Define SELECT, INSERT, UPDATE, DELETE policies per table
- Map policies to user roles (anon, authenticated, service_role)
- Use auth.uid() for user-scoped access
- Document any service_role bypass patterns

### Step 8: Draft Migration SQL

Write executable SQL:
- CREATE TABLE statements for new tables
- ALTER TABLE statements for existing table modifications
- CREATE INDEX statements
- RLS policy statements
- Include a rollback section (DROP TABLE, DROP INDEX, etc.)

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Handoff

- If the schema design reveals API contract requirements or endpoint shape changes, recommend loading architect/api-design.
- If the schema involves sensitive data fields or access control beyond RLS, recommend loading guardian/data-classification.

## Output Format

```markdown
# Schema Design: [Feature Name]

## Entity Overview

| Entity | Purpose | New/Modified |
|--------|---------|-------------|
| ...    | ...     | ...         |

## Entity Definitions

### [entity_name]
| Column | Type | Nullable | Default | Constraints |
|--------|------|----------|---------|-------------|
| id     | uuid | NO       | gen_random_uuid() | PK |
| ...    | ...  | ...      | ...     | ...         |

## Relationships
```
[ASCII diagram]
users 1──N posts
posts N──M tags (through: post_tags)
```

## Index Strategy
| Table | Index | Columns | Type | Rationale |
|-------|-------|---------|------|-----------|
| ...   | ...   | ...     | ...  | ...       |

## Denormalization Decisions
| What | Why | Consistency Strategy |
|------|-----|---------------------|
| ...  | ... | ...                 |

## RLS Policies
| Table | Operation | Policy | Using |
|-------|-----------|--------|-------|
| ...   | ...       | ...    | ...   |

## Migration SQL

### Up
```sql
-- New tables
CREATE TABLE ...

-- Indexes
CREATE INDEX ...

-- RLS
ALTER TABLE ... ENABLE ROW LEVEL SECURITY;
CREATE POLICY ...
```

### Down
```sql
DROP POLICY ...
DROP INDEX ...
DROP TABLE ...
```
```

## Quality Checks

- [ ] Every entity has a primary key
- [ ] Foreign keys reference existing or newly created tables
- [ ] Indexes support the identified query patterns
- [ ] Migration is reversible (Down section undoes Up completely)
- [ ] RLS policies cover all access patterns (SELECT, INSERT, UPDATE, DELETE)
- [ ] Timestamp columns (created_at, updated_at) are present on mutable entities
- [ ] CASCADE behavior is explicitly defined for all foreign keys
- [ ] No orphan tables (every table is reachable via relationships or has a documented reason for isolation)

## Evolution Notes
<!-- Observations appended after each use -->
