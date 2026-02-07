---
name: "Schema Evaluation"
department: "alchemist"
description: "Evaluate and design data warehouse schemas — star, snowflake, data vault, OBT — with grain definition, SCD strategies, and normalization trade-offs"
version: 1
triggers:
  - "schema"
  - "data model"
  - "warehouse"
  - "dimension"
  - "fact table"
  - "SCD"
  - "grain"
  - "normalization"
  - "data vault"
  - "star schema"
  - "snowflake schema"
  - "data contract"
  - "slowly changing"
---

# Schema Evaluation

## Purpose

Evaluate and design data warehouse schemas for analytical workloads. Covers star schemas, snowflake schemas, data vault, and One Big Table (OBT) patterns. Assesses grain definition, normalization trade-offs, slowly changing dimension strategies, and data contracts between producers and consumers.

## Inputs

- Business domain and key entities (e.g., e-commerce: orders, products, customers)
- Analytical queries the schema must support (e.g., "revenue by product category by month")
- Data volume estimates (row counts, growth rate)
- Source systems and their update patterns (CDC, full refresh, event stream)
- Existing schema (if evaluating rather than designing from scratch)

## Process

### Step 1: Define the Grain

Identify the grain of each fact table — what does one row represent? A single transaction? A daily snapshot? A session event? The grain determines everything downstream. Document the grain as a clear English sentence: "One row = one order line item" or "One row = one daily active user per product."

### Step 2: Identify Facts and Dimensions

Separate measurable facts (revenue, quantity, duration, count) from descriptive dimensions (customer, product, date, geography). For each:
- **Facts:** Data type, aggregation method (SUM, AVG, COUNT DISTINCT), nullability
- **Dimensions:** Cardinality, hierarchy levels, whether it changes over time (SCD candidate)

### Step 3: Choose a Modeling Approach

Evaluate which pattern fits the requirements:
- **Star schema** — Simple, fast queries, denormalized dimensions. Best for straightforward BI with a known query pattern.
- **Snowflake schema** — Normalized dimensions for storage efficiency and consistency. Best when dimensions are large or shared across many facts.
- **Data vault** — Hub, link, satellite pattern for auditability and flexibility. Best when source systems change frequently or full history is required.
- **One Big Table (OBT)** — Fully denormalized single table. Best for small teams, simple analytics, or when query simplicity outweighs storage concerns.

Document the chosen approach and the reasoning behind it.

### Step 4: Design Slowly Changing Dimension Strategy

For each dimension that changes over time, specify the SCD type:
- **Type 1** — Overwrite. No history. Simple, but you lose the old value.
- **Type 2** — Add new row with effective dates. Full history, but increases row count and query complexity.
- **Type 3** — Add column for previous value. Limited history (only one prior value), but simple to query.
- **Type 6** — Hybrid (1+2+3). Current value column plus history rows. Best of both but most complex.

Document which SCD type applies to each changing attribute and why.

### Step 5: Define Data Contracts

For each source-to-warehouse interface, specify the contract:
- Schema expectations (required fields, data types, allowed values)
- Freshness SLA (how soon after source update must the warehouse reflect it?)
- Quality thresholds (max null rate, uniqueness constraints, referential integrity)
- Breaking change policy (how are schema changes communicated and handled?)

### Step 6: Validate Against Query Patterns

Test the proposed schema against the required analytical queries:
- Can each query be answered with at most 2-3 joins?
- Are the most common filters (date, category, status) on dimension keys?
- Is the grain appropriate — not too fine (wasteful) or too coarse (lossy)?
- Are aggregate tables or materialized views needed for high-frequency dashboards?

### Step 7: Document the Schema

Produce a complete schema specification with DDL, relationships, and usage notes.

## Output Format

```markdown
# Schema Evaluation: [Domain/Project Name]

## Grain Definitions

| Fact Table | Grain (one row = ...) | Estimated Rows | Growth Rate |
|------------|----------------------|----------------|-------------|
| ...        | ...                  | ...            | ...         |

## Entity Relationship Summary

```
[ASCII diagram showing fact and dimension relationships]
```

## Modeling Approach

**Chosen:** [Star / Snowflake / Data Vault / OBT]
**Rationale:** [1-2 sentences]

## Fact Tables

### fct_[name]
| Column | Type | Description | Aggregation |
|--------|------|-------------|-------------|
| ...    | ...  | ...         | SUM/AVG/... |

## Dimension Tables

### dim_[name]
| Column | Type | Description | SCD Type |
|--------|------|-------------|----------|
| ...    | ...  | ...         | 1/2/3    |

## Slowly Changing Dimensions

| Dimension | Attribute | SCD Type | Rationale |
|-----------|-----------|----------|-----------|
| ...       | ...       | ...      | ...       |

## Data Contracts

| Source → Target | Freshness SLA | Quality Checks | Breaking Change Policy |
|-----------------|---------------|----------------|----------------------|
| ...             | ...           | ...            | ...                  |

## Query Validation

| Query Pattern | Tables Involved | Join Count | Performance Notes |
|---------------|----------------|------------|-------------------|
| ...           | ...            | ...        | ...               |
```

## Quality Checks

- [ ] Every fact table has a clearly stated grain in plain English
- [ ] Facts and dimensions are properly separated — no business logic in fact tables
- [ ] SCD strategy is specified for every dimension attribute that changes
- [ ] Data contracts define freshness SLA, schema expectations, and quality thresholds
- [ ] The schema supports all required analytical queries with minimal joins
- [ ] Cardinality estimates are documented for key dimensions
- [ ] Surrogate keys vs natural keys decision is documented and consistent
- [ ] Indexing strategy is defined for common filter and join columns

## Evolution Notes
<!-- Observations appended after each use -->
