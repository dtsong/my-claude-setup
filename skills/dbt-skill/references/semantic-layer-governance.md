# Semantic Layer & Governance

## Semantic Layer

The dbt Semantic Layer provides centralized metric definitions consumed by any BI tool. Define a metric once in dbt, query from Looker, Tableau, Hex, or Google Sheets.

**Prerequisites:** dbt Cloud (Team tier+) for API, MetricFlow OSS for local dev, dbt Core 1.6+, Snowflake/BigQuery/Databricks/Redshift.

**Adopt when:** multiple BI tools produce conflicting numbers. Skip when just starting -- focus on modeling fundamentals first.

## MetricFlow Configuration

Define semantic models mapping dbt models to entities, dimensions, and measures:

```yaml
semantic_models:
  - name: orders
    model: ref('fct_orders')
    defaults:
      agg_time_dimension: order_date
    entities:
      - name: order_id
        type: primary
      - name: customer_id
        type: foreign
    dimensions:
      - name: order_date
        type: time
        type_params: { time_granularity: day }
      - name: order_status
        type: categorical
    measures:
      - name: total_revenue
        agg: sum
        expr: total_amount
      - name: order_count
        agg: count
        expr: order_id
```

**Entity types:** `primary`, `foreign`, `unique`, `natural`. **Dimension types:** `categorical`, `time`. **Aggregations:** `sum`, `count`, `count_distinct`, `average`, `min`, `max`, `median`, `percentile`.

## Metric Types

- **Simple:** Direct reference to a single measure. Use for straightforward KPIs.
- **Derived:** Math on other metrics (e.g., `total_revenue / order_count`). Use for ratios, percentages.
- **Cumulative:** Running totals with optional window (e.g., `28 days`). Use for MRR, cumulative revenue.
- **Conversion:** Funnel metrics tracking entity progression between events with a conversion window.

Define metrics in dbt, never redefine the same metric logic in each BI tool.

## Model Contracts (dbt 1.5+)

Enforce column names and data types at build time. Build fails if SQL output does not match.

```yaml
models:
  - name: fct_orders
    config:
      contract: { enforced: true }
    columns:
      - name: order_id
        data_type: string
      - name: total_amount
        data_type: float
```

**Type mapping:** Use logical types (`string`, `integer`, `float`, `boolean`, `timestamp`, `date`) -- dbt translates to warehouse-specific types.

**Enforce on:** marts, public models, Semantic Layer models. **Skip on:** staging (too rigid for evolving sources), intermediate (internal helpers).

## Model Versions (dbt 1.6+)

Run multiple versions simultaneously when changing a model's schema without breaking consumers.

```yaml
models:
  - name: fct_orders
    latest_version: 2
    versions:
      - v: 1
        defined_in: fct_orders_v1
        deprecation_date: 2025-06-01
      - v: 2
        defined_in: fct_orders_v2
        columns:
          - include: all
          - name: discount_amount
            data_type: float
```

`ref('fct_orders')` resolves to `latest_version`. Pin with `ref('fct_orders', v=1)`.

**Migration:** Create v2 alongside v1, migrate consumers, set deprecation on v1, remove v1 after migration.

Version only public models with breaking schema changes. Do not version for additive changes.

## Access Controls (dbt 1.5+)

| Level | Who Can ref() | Use Case |
|-------|--------------|----------|
| `private` | Same group only | Internal helpers |
| `protected` | Same project (default) | Standard models |
| `public` | Any project | Cross-project interfaces |

Define groups in `dbt_project.yml` with owner name and email. Assign models to groups via YAML config or `{{ config(group='finance', access='public') }}`.

Public models should always have enforced contracts. Never make intermediate models public.

## dbt Mesh (Multi-Project)

Enables cross-project `ref()` for large organizations. Each team owns a project; projects reference each other's `public` models.

**Split signals:** 50+ models, multiple teams, different deploy cadences, CI >30 min.

**Pattern:** Producer publishes `public` models with contracts. Consumer references via `ref('project_name', 'model_name')`. Configure `dependencies.yml` in consumer projects.

**Checklist:** All shared models are `public` with enforced contracts, groups/owners defined, `dependencies.yml` configured, deployment order documented.

## Maturity Assessment

| Stage | Testing | CI/CD | Governance |
|-------|---------|-------|------------|
| Starting | Basic YAML tests | Manual runs | Naming conventions |
| Running in Prod | Custom generics, unit tests | Slim CI, GitHub Actions | Access controls, groups |
| Multiple Teams | dbt-expectations, contracts | dbt Cloud, blue/green | Versions, contracts |
| Enterprise | Full coverage + anomaly detection | Multi-project orchestration | dbt Mesh, Semantic Layer |

**Next steps by stage:**
- Starting: Add PK tests, set up CI, configure source freshness, write descriptions
- Running: Define groups/ownership, set access levels, enforce contracts, add dbt-expectations
- Multiple Teams: Evaluate dbt Mesh, implement versions, deploy Semantic Layer, set SLAs
- Enterprise: Integrate Semantic Layer with all BI tools, anomaly detection, on-call, governed catalog
