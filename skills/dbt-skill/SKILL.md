---
name: dbt-skill
description: Use when working with dbt (data build tool) - creating models, writing tests, CI/CD pipelines, materializations, sources, staging/intermediate/marts layers, Snowflake/BigQuery warehouse configuration, incremental strategies, Jinja macros, data quality, semantic layer, or making analytics engineering decisions
license: Apache-2.0
metadata:
  author: Daniel Song
  version: 1.0.0
---

# dbt Skill for Claude

Comprehensive dbt guidance: project structure, modeling, testing, CI/CD, production patterns. Targets Snowflake and BigQuery. Beginner-friendly with progressive scaling.

## When to Use

Activate when: creating/modifying dbt models, choosing materializations, structuring layers, setting up tests, implementing CI/CD, configuring sources/freshness, writing Jinja macros, reviewing dbt projects, making analytics engineering decisions.

Skip when: basic SQL syntax, warehouse admin, raw pipeline config (Fivetran/Airbyte), BI tool config.

## Core Principles

1. **DRY via ref()/source()** -- never hardcode table names
2. **Single Source of Truth** -- each concept defined once; staging = entry point, marts = consumer interface
3. **Idempotent Transformations** -- `dbt run` twice produces identical results
4. **Test Everything** -- every model has at minimum PK uniqueness and not-null tests
5. **Progressive Complexity** -- start with views/tables, add complexity when volume demands it

## Project Structure

```
dbt_project/
├── dbt_project.yml
├── packages.yml
├── profiles.yml                 # local only, not committed
├── models/
│   ├── staging/                 # 1:1 with source tables
│   │   └── <source>/
│   │       ├── _<source>__models.yml
│   │       ├── _<source>__sources.yml
│   │       └── stg_<source>__<entity>.sql
│   ├── intermediate/            # business logic, joins, pivots
│   │   └── <domain>/
│   └── marts/                   # business-facing tables
│       └── <domain>/
│           ├── _<domain>__models.yml
│           ├── fct_<entity>.sql
│           └── dim_<entity>.sql
├── macros/
├── tests/
│   └── generic/
├── seeds/
├── snapshots/
└── analyses/
```

## Layer Decision Matrix

| Layer | Materialization | Purpose | Naming | Tests |
|-------|----------------|---------|--------|-------|
| Staging | `view` | Clean/rename raw data, 1:1 with source | `stg_<source>__<entity>` | not_null, unique on PK |
| Intermediate | `ephemeral` | Business logic, joins, pivots | `int_<entity>_<verb>ed` | Tested via downstream |
| Marts | `table`/`incremental` | Business-facing facts and dimensions | `fct_<entity>`, `dim_<entity>` | Full coverage |

## Materialization Decision Matrix

| Situation | Materialization | Why |
|-----------|----------------|-----|
| Staging models | `view` | Always fresh, minimal storage |
| Intermediate logic | `ephemeral` | Zero cost, inlined as CTE |
| Marts < 100M rows | `table` | Simple, fast reads |
| Marts > 100M rows | `incremental` | Process only new/changed data |
| SCD Type 2 | `snapshot` | Track historical changes |

## ref() and source() Rules

1. `source()` only in staging -- staging is the sole gateway to raw data
2. `ref()` everywhere else
3. Never skip layers -- marts must not ref() staging directly
4. Never hardcode schema names

## SQL Style

- Leading commas, lowercase keywords, CTEs over subqueries
- Explicit columns in marts (no `select *`), final CTE named `final`
- 4-space indentation, one column per line

## Source Configuration

Define sources in `_<source>__sources.yml` with `loaded_at_field` and freshness thresholds. Configure `warn_after` and `error_after` per table.

| Concept | Snowflake | BigQuery |
|---------|-----------|----------|
| Top-level container | Database | Project |
| Schema grouping | Schema | Dataset |

## Warehouse Quick Reference

| Config | Snowflake | BigQuery |
|--------|-----------|----------|
| Profile type | `snowflake` | `bigquery` |
| Auth | User/password or key-pair | OAuth or service account |
| Schema gen | `database.schema.model` | `project.dataset.model` |
| Incremental default | `merge` | `merge` |
| Partitioning | Automatic micro-partitions | `partition_by` required for large tables |
| Clustering | `cluster_by` (automatic) | `cluster_by` (manual) |
| Cost model | Credits (compute time) | Bytes scanned / Slots |

## Common Commands

| Command | Purpose |
|---------|---------|
| `dbt build` | Run + test in DAG order (recommended) |
| `dbt build --select +model` | Build model and all ancestors |
| `dbt build --select model+` | Build model and all descendants |
| `dbt build --select tag:finance` | All models tagged `finance` |
| `dbt build --select state:modified+` | Modified + descendants (Slim CI) |
| `dbt source freshness` | Check source freshness |
| `dbt deps` | Install packages |
| `dbt docs generate && dbt docs serve` | Documentation site |

## Reference Files

Load on demand when detailed guidance is needed:

| Reference | Topics |
|-----------|--------|
| [Testing & Quality](references/testing-quality.md) | Schema/generic/singular/unit tests, dbt-expectations, layer strategy |
| [CI/CD & Deployment](references/ci-cd-deployment.md) | Slim CI, GitHub Actions, dbt Cloud, environments, blue/green, SQLFluff |
| [Jinja, Macros & Packages](references/jinja-macros-packages.md) | Jinja fundamentals, custom macros, packages, debugging |
| [Incremental & Performance](references/incremental-performance.md) | Microbatch, merge, delete+insert, insert_overwrite, warehouse tuning |
| [Data Quality & Observability](references/data-quality-observability.md) | Source freshness, Elementary, anomaly detection, alerting, incidents |
| [Semantic Layer & Governance](references/semantic-layer-governance.md) | MetricFlow, contracts, versions, access controls, dbt Mesh |

## License

Apache License 2.0. See LICENSE file for full terms.

**Copyright 2026 Daniel Song**
