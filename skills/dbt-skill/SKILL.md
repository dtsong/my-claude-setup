---
name: dbt-skill
description: Use when working with dbt (data build tool) - creating models, writing tests, CI/CD pipelines, materializations, sources, staging/intermediate/marts layers, Snowflake/BigQuery warehouse configuration, incremental strategies, Jinja macros, data quality, semantic layer, or making analytics engineering decisions
license: Apache-2.0
metadata:
  author: Daniel Song
  version: 1.0.0
---

# dbt Skill for Claude

Comprehensive dbt guidance covering project structure, modeling methodology, testing, CI/CD, and production patterns. Targets Snowflake and BigQuery as primary warehouses. Beginner-friendly with progressive scaling toward advanced capabilities.

## When to Use This Skill

**Activate this skill when:**
- Creating new dbt projects or adding models to existing ones
- Choosing materializations (view, table, incremental, ephemeral, snapshot)
- Structuring staging, intermediate, and marts layers
- Setting up testing strategies (schema, generic, singular, unit)
- Implementing CI/CD pipelines for dbt
- Configuring sources and freshness monitoring
- Writing Jinja macros or installing dbt packages
- Reviewing or refactoring existing dbt projects
- Making analytics engineering architecture decisions

**Don't use this skill for:**
- Basic SQL syntax questions (Claude knows this)
- Warehouse administration (user management, networking, billing)
- Raw data pipeline configuration (Fivetran, Airbyte, Stitch)
- BI tool configuration (Looker, Tableau, Power BI)

## Core Principles

### 1. DRY via ref() and source()

Every model references upstream dependencies through `ref()` or `source()` — never hardcoded table names.

### 2. Single Source of Truth

Each concept is defined once. Staging models are the single entry point for raw data. Marts are the single interface for consumers.

### 3. Idempotent Transformations

Running `dbt run` twice produces the same result. Models are deterministic and reproducible.

### 4. Test Everything

Tests are not optional. Every model has at minimum a primary key uniqueness and not-null test.

### 5. Progressive Complexity

Start simple (views and tables), add complexity only when data volume or business requirements demand it.

## Project Structure

```
dbt_project/
├── dbt_project.yml              # Project configuration
├── packages.yml                 # Package dependencies
├── profiles.yml                 # Connection profiles (local only, not committed)
├── models/
│   ├── staging/                 # 1:1 with source tables
│   │   ├── stripe/
│   │   │   ├── _stripe__models.yml
│   │   │   ├── _stripe__sources.yml
│   │   │   ├── stg_stripe__payments.sql
│   │   │   └── stg_stripe__customers.sql
│   │   └── shopify/
│   │       ├── _shopify__models.yml
│   │       ├── _shopify__sources.yml
│   │       └── stg_shopify__orders.sql
│   ├── intermediate/            # Business logic joins and transformations
│   │   ├── finance/
│   │   │   ├── _int_finance__models.yml
│   │   │   └── int_payments_pivoted.sql
│   │   └── marketing/
│   │       └── int_web_sessions_sessionized.sql
│   └── marts/                   # Business-facing tables
│       ├── finance/
│       │   ├── _finance__models.yml
│       │   ├── fct_orders.sql
│       │   └── dim_customers.sql
│       └── marketing/
│           ├── _marketing__models.yml
│           └── fct_web_sessions.sql
├── macros/                      # Reusable Jinja macros
├── tests/                       # Singular and generic tests
│   └── generic/                 # Custom generic tests
├── seeds/                       # CSV reference data
├── snapshots/                   # SCD Type 2 snapshots
└── analyses/                    # Ad-hoc analytical queries
```

### dbt_project.yml Template

```yaml
name: 'my_project'
version: '1.0.0'
config-version: 2

profile: 'my_project'

model-paths: ["models"]
analysis-paths: ["analyses"]
test-paths: ["tests"]
seed-paths: ["seeds"]
macro-paths: ["macros"]
snapshot-paths: ["snapshots"]

clean-targets: ["target", "dbt_packages"]

models:
  my_project:
    staging:
      +materialized: view           # Lightweight, always fresh
    intermediate:
      +materialized: ephemeral      # No warehouse cost, inlined as CTEs
    marts:
      +materialized: table          # Fast reads for BI tools
```

## Modeling Methodology — Medallion + Kimball

### Layer Decision Matrix

| Layer | Materialization | Purpose | Naming | Tests |
|-------|----------------|---------|--------|-------|
| **Staging** | `view` | Clean and rename raw data, 1:1 with source | `stg_<source>__<entity>` | not_null, unique on PK |
| **Intermediate** | `ephemeral` | Business logic, joins, pivots | `int_<entity>_<verb>ed` | Tested via downstream |
| **Marts** | `table` / `incremental` | Business-facing facts and dimensions | `fct_<entity>`, `dim_<entity>` | Full test coverage |
| **Reports** | `table` | Pre-aggregated for specific dashboards | `rpt_<entity>` | Acceptance tests |

### Layer Flow

```
Raw Data (sources)
    ↓
Staging (stg_) ── view ── clean, rename, cast, 1:1
    ↓
Intermediate (int_) ── ephemeral ── join, pivot, business logic
    ↓
Marts (fct_, dim_) ── table/incremental ── business entities
    ↓
BI Tools / Consumers
```

### Staging Model Pattern

```sql
-- stg_stripe__payments.sql
with source as (
    select * from {{ source('stripe', 'payments') }}
),

renamed as (
    select
        -- primary key
        id as payment_id,

        -- foreign keys
        order_id,
        customer_id,

        -- properties
        lower(payment_method) as payment_method,
        status as payment_status,

        -- numerics
        amount / 100.0 as amount_dollars,

        -- timestamps
        created_at,
        updated_at

    from source
)

select * from renamed
```

### Intermediate Model Pattern

```sql
-- int_payments_pivoted.sql
with payments as (
    select * from {{ ref('stg_stripe__payments') }}
),

pivoted as (
    select
        order_id,
        sum(case when payment_method = 'credit_card' then amount_dollars else 0 end) as credit_card_amount,
        sum(case when payment_method = 'bank_transfer' then amount_dollars else 0 end) as bank_transfer_amount,
        sum(amount_dollars) as total_amount
    from payments
    where payment_status = 'completed'
    group by order_id
)

select * from pivoted
```

### Marts Model Pattern

```sql
-- fct_orders.sql
with orders as (
    select * from {{ ref('stg_shopify__orders') }}
),

payments as (
    select * from {{ ref('int_payments_pivoted') }}
),

final as (
    select
        orders.order_id,
        orders.customer_id,
        orders.order_date,
        orders.order_status,
        payments.credit_card_amount,
        payments.bank_transfer_amount,
        payments.total_amount
    from orders
    left join payments on orders.order_id = payments.order_id
)

select * from final
```

## Model Naming Conventions

### Models

| Layer | Pattern | Example |
|-------|---------|---------|
| Staging | `stg_<source>__<entity>` | `stg_stripe__payments` |
| Intermediate | `int_<entity>_<verb>ed` | `int_payments_pivoted` |
| Facts | `fct_<entity>` | `fct_orders` |
| Dimensions | `dim_<entity>` | `dim_customers` |
| Reports | `rpt_<entity>` | `rpt_monthly_revenue` |

### YAML Files

| Type | Pattern | Example |
|------|---------|---------|
| Model config | `_<layer>__models.yml` | `_stripe__models.yml` |
| Sources | `_<layer>__sources.yml` | `_stripe__sources.yml` |

Use the leading underscore to sort config files above model files in the directory listing.

## SQL Style Guide

### Rules

1. **Leading commas** — easier to comment out lines, cleaner diffs
2. **Lowercase keywords** — `select`, not `SELECT`
3. **CTEs over subqueries** — always use `with` blocks
4. **Explicit columns** — never `select *` in marts (acceptable in staging `with source`)
5. **Final CTE** — name the last CTE `final` for consistency
6. **4-space indentation** — align for readability
7. **One column per line** — in select statements

### Complete Example

```sql
with source as (
    select * from {{ source('shopify', 'orders') }}
),

renamed as (
    select
        id as order_id,
        user_id as customer_id,
        lower(status) as order_status,
        created_at as order_date,
        updated_at
    from source
),

final as (
    select
        order_id,
        customer_id,
        order_status,
        order_date,
        updated_at
    from renamed
    where order_status is not null
)

select * from final
```

## Materialization Decision Matrix

| Situation | Materialization | Why |
|-----------|----------------|-----|
| Staging models | `view` | Always fresh, minimal storage cost |
| Intermediate logic | `ephemeral` | Zero cost, inlined as CTE |
| Marts < 100M rows | `table` | Simple, fast reads |
| Marts > 100M rows | `incremental` | Only process new/changed data |
| SCD Type 2 tracking | `snapshot` | Track historical changes |
| One-off analysis | `ephemeral` | No need to persist |

### Warehouse-Specific Configuration

| Feature | Snowflake | BigQuery |
|---------|-----------|----------|
| **Incremental default** | `merge` | `merge` |
| **Recommended for events** | `microbatch` (1.9+) | `insert_overwrite` |
| **Clustering** | `cluster_by` (automatic) | `cluster_by` (manual) |
| **Partitioning** | Automatic micro-partitions | `partition_by` (required for large tables) |
| **Transient tables** | `transient: true` (no fail-safe) | N/A |
| **Dynamic tables** | `materialized: dynamic_table` | N/A |
| **Cost model** | Credits (compute time) | Bytes scanned (on-demand) / Slots (flat-rate) |

**For detailed incremental strategies, see:** [Incremental Models & Performance](references/incremental-performance.md)

## Source Configuration

```yaml
# _stripe__sources.yml
version: 2

sources:
  - name: stripe
    description: "Stripe payment data loaded by Fivetran"
    database: raw                     # Snowflake: database name
    schema: stripe                    # Snowflake: schema name
    loader: fivetran
    loaded_at_field: _fivetran_synced # For freshness checks
    freshness:
      warn_after: {count: 12, period: hour}
      error_after: {count: 24, period: hour}
    tables:
      - name: payments
        description: "One record per payment attempt"
        columns:
          - name: id
            description: "Primary key"
            data_tests:
              - unique
              - not_null
          - name: order_id
            description: "Foreign key to orders"
            data_tests:
              - not_null
              - relationships:
                  to: source('shopify', 'orders')
                  field: id
```

### Warehouse Terminology

| Concept | Snowflake | BigQuery |
|---------|-----------|----------|
| Top-level container | Database | Project |
| Schema grouping | Schema | Dataset |
| Freshness field | `_fivetran_synced` | `_fivetran_synced` or `_PARTITIONTIME` |

## Basic Testing Overview

### Testing Pyramid

```
          /\
         /  \        Singular Tests (specific business rules)
        /____\
       /      \      Generic Tests (reusable patterns)
      /________\
     /          \    Schema Tests (YAML-configured)
    /____________\
   /              \  Source Freshness (automated)
  /________________\
```

### What to Test at Each Layer

| Layer | Test Type | Examples |
|-------|-----------|---------|
| **Sources** | Freshness, existence | `loaded_at_field`, `not_null` on keys |
| **Staging** | Primary key integrity | `unique`, `not_null` on PK |
| **Intermediate** | Tested via downstream models | — |
| **Marts** | Full coverage | All keys, accepted values, relationships, row counts |

### Quick Test Example

```yaml
# _finance__models.yml
version: 2

models:
  - name: fct_orders
    description: "One record per order with payment details"
    columns:
      - name: order_id
        description: "Primary key"
        data_tests:
          - unique
          - not_null
      - name: order_status
        data_tests:
          - accepted_values:
              values: ['completed', 'pending', 'cancelled', 'refunded']
      - name: total_amount
        data_tests:
          - not_null
          - dbt_expectations.expect_column_values_to_be_between:
              min_value: 0
```

**For deep testing strategies, see:** [Testing & Quality Strategy](references/testing-quality.md)

## ref() and source() Patterns

### Rules

1. **`source()` only in staging** — staging models are the only gateway to raw data
2. **`ref()` everywhere else** — all other models reference through `ref()`
3. **Never skip layers** — marts must not `ref()` staging directly (go through intermediate)
4. **Never hardcode schema names** — use `source()` and `ref()` exclusively

### Correct DAG Flow

```
source('stripe', 'payments')  →  stg_stripe__payments
                                       ↓
                                 int_payments_pivoted
                                       ↓
                                   fct_orders
```

### Anti-patterns

```sql
-- WRONG: Hardcoded table reference
select * from raw.stripe.payments

-- WRONG: source() outside staging
-- (in a marts model)
select * from {{ source('stripe', 'payments') }}

-- WRONG: Skipping layers
-- (in a marts model referencing staging directly)
select * from {{ ref('stg_stripe__payments') }}

-- CORRECT: Follow the DAG
select * from {{ ref('int_payments_pivoted') }}
```

## Common Commands Cheat Sheet

### Build & Run

| Command | Purpose |
|---------|---------|
| `dbt run` | Run all models |
| `dbt test` | Run all tests |
| `dbt build` | Run + test in DAG order (recommended) |
| `dbt compile` | Compile SQL without executing |
| `dbt run --select fct_orders` | Run a single model |
| `dbt build --select +fct_orders` | Build model and all ancestors |
| `dbt build --select fct_orders+` | Build model and all descendants |

### Selectors

| Selector | Meaning |
|----------|---------|
| `-s model_name` | Select a single model |
| `-s +model_name` | Model + all upstream ancestors |
| `-s model_name+` | Model + all downstream descendants |
| `-s +model_name+` | Model + all ancestors + descendants |
| `-s tag:finance` | All models tagged `finance` |
| `-s path:models/marts` | All models in a directory |
| `-s state:modified+` | Modified models + descendants (Slim CI) |

### Utilities

| Command | Purpose |
|---------|---------|
| `dbt deps` | Install packages from packages.yml |
| `dbt seed` | Load CSV seeds into warehouse |
| `dbt snapshot` | Execute snapshot models |
| `dbt source freshness` | Check source freshness |
| `dbt docs generate` | Generate documentation site |
| `dbt docs serve` | Serve documentation locally |
| `dbt debug` | Test database connection |
| `dbt clean` | Remove compiled artifacts |

## Warehouse Quick Reference

| Configuration | Snowflake | BigQuery |
|--------------|-----------|----------|
| **Profile target** | `type: snowflake` | `type: bigquery` |
| **Auth method** | User/password or key-pair | OAuth or service account |
| **Schema generation** | `database.schema.model` | `project.dataset.model` |
| **Incremental default** | `merge` (using `unique_key`) | `merge` (using `unique_key`) |
| **Partitioning** | Automatic micro-partitions | `partition_by: {field, data_type}` |
| **Clustering** | `{{ config(cluster_by=['col']) }}` | `{{ config(cluster_by=['col']) }}` |
| **Cost optimization** | Warehouse auto-suspend, transient tables | Partition pruning, BI Engine caching |
| **Connection test** | `dbt debug` | `dbt debug` |

## Detailed Guides

This skill uses **progressive disclosure** — essential information is in this main file, detailed guides are available when needed:

**Reference Files:**
- **[Testing & Quality Strategy](references/testing-quality.md)** — Deep dive into schema tests, generic tests, singular tests, unit tests, dbt-expectations, and layer-specific testing strategy
- **[CI/CD & Deployment](references/ci-cd-deployment.md)** — Local dev workflows, Slim CI, GitHub Actions, dbt Cloud jobs, environment strategy, blue/green deployment, SQLFluff
- **[Jinja, Macros & Packages](references/jinja-macros-packages.md)** — Jinja fundamentals, custom macros, essential packages (dbt-utils, dbt-expectations), debugging, warehouse-adaptive patterns
- **[Incremental Models & Performance](references/incremental-performance.md)** — Microbatch (1.9+), merge, delete+insert, insert_overwrite, Snowflake/BigQuery performance tuning, cost monitoring
- **[Data Quality & Observability](references/data-quality-observability.md)** — Source freshness, Elementary package, anomaly detection, alerting, lineage, incident response
- **[Semantic Layer & Governance](references/semantic-layer-governance.md)** — MetricFlow, model contracts, versions, access controls, dbt Mesh, maturity assessment

**How to use:** When you need detailed information on a topic, reference the appropriate guide. Claude will load it on demand to provide comprehensive guidance.

## License

This skill is licensed under the **Apache License 2.0**. See the LICENSE file for full terms.

**Copyright 2026 Daniel Song**
