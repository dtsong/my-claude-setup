# Semantic Layer & Governance

> **Part of:** [dbt-skill](../SKILL.md)
> **Purpose:** MetricFlow semantic models, metric types, model contracts, versioning, access controls, dbt Mesh, and maturity assessment

This document covers centralized metric definitions, governance features introduced in dbt 1.5+, and multi-project architecture. For core modeling patterns, see the [main skill file](../SKILL.md).

---

## Table of Contents

1. [Semantic Layer Overview](#semantic-layer-overview)
2. [MetricFlow Configuration](#metricflow-configuration)
3. [Metric Types](#metric-types)
4. [Model Contracts](#model-contracts-dbt-15)
5. [Model Versions](#model-versions-dbt-16)
6. [Access Controls](#access-controls-dbt-15)
7. [dbt Mesh (Multi-Project)](#dbt-mesh-multi-project)
8. [Maturity Assessment](#maturity-assessment)

---

## Semantic Layer Overview

### What It Is

The dbt Semantic Layer provides centralized metric definitions consumed by any BI tool (Looker, Tableau, Hex, Mode, Google Sheets). Define a metric once in dbt, query it from anywhere.

### The Problem It Solves

**"Different numbers in different dashboards."** Without a semantic layer:

- Finance reports `$2.3M` revenue from a Looker dashboard
- Marketing reports `$2.1M` revenue from a Tableau workbook
- The CEO asks: "Which number is right?"

The root cause: each tool has its own metric logic, filters, and joins. The semantic layer moves metric definitions upstream into dbt, creating a single source of truth.

### Maturity Decision Matrix

| Team Stage | Recommendation | Reason |
|------------|---------------|--------|
| Just starting | Skip Semantic Layer | Focus on modeling fundamentals first |
| Running in prod | Evaluate adoption | Define key metrics centrally |
| Multiple BI tools | Strongly adopt | Single source of metric truth |
| Enterprise scale | Full platform | Governance, access control, versioning |

### Prerequisites

- **dbt Cloud:** The Semantic Layer API is a dbt Cloud feature (Team tier or higher)
- **MetricFlow OSS:** Use for local development and testing (`pip install dbt-metricflow`)
- **dbt Core 1.6+:** Required for `semantic_models` and `metrics` YAML blocks
- **Supported warehouses:** Snowflake, BigQuery, Databricks, Redshift

---

## MetricFlow Configuration

### Semantic Models

Semantic models map dbt models to queryable entities, dimensions, and measures. Define them in YAML alongside your model configs.

```yaml
# models/marts/finance/_finance__semantic_models.yml
semantic_models:
  - name: orders
    description: "Order fact table with payment details"
    model: ref('fct_orders')
    defaults:
      agg_time_dimension: order_date  # default time dimension for metrics

    # Entities define join keys
    entities:
      - name: order_id
        type: primary
      - name: customer_id
        type: foreign

    # Dimensions are groupable attributes
    dimensions:
      - name: order_date
        type: time
        type_params:
          time_granularity: day
      - name: order_status
        type: categorical
      - name: payment_method
        type: categorical

    # Measures are aggregatable values
    measures:
      - name: order_count
        description: "Total number of orders"
        agg: count
        expr: order_id
      - name: total_revenue
        description: "Sum of order amounts in dollars"
        agg: sum
        expr: total_amount
      - name: average_order_amount
        description: "Average order value"
        agg: average
        expr: total_amount
      - name: unique_customers
        description: "Distinct customer count"
        agg: count_distinct
        expr: customer_id
```

### Entity Types

| Type | Purpose | Example |
|------|---------|---------|
| `primary` | Unique identifier for the semantic model | `order_id` in orders |
| `foreign` | Join key referencing another semantic model | `customer_id` in orders |
| `unique` | Unique but not the primary identifier | `email` in customers |
| `natural` | Business key that may change over time | `sku` in products |

### Dimension Types

| Type | Purpose | Example |
|------|---------|---------|
| `categorical` | Groupable string/enum values | `order_status`, `region` |
| `time` | Date/timestamp for time-series analysis | `order_date`, `created_at` |

### Measure Aggregation Types

| Aggregation | SQL Equivalent | Use Case |
|-------------|---------------|----------|
| `sum` | `SUM(expr)` | Revenue, quantities |
| `count` | `COUNT(expr)` | Row counts |
| `count_distinct` | `COUNT(DISTINCT expr)` | Unique users, sessions |
| `average` | `AVG(expr)` | Average order value |
| `min` | `MIN(expr)` | First occurrence |
| `max` | `MAX(expr)` | Most recent, largest |
| `median` | `MEDIAN(expr)` | Median order size |
| `percentile` | `PERCENTILE_CONT(expr)` | P95 latency, P50 revenue |

---

## Metric Types

### Simple Metrics

Direct reference to a single measure. Use for straightforward KPIs.

```yaml
metrics:
  - name: total_revenue
    description: "Sum of all order amounts"
    type: simple
    label: "Total Revenue"
    type_params:
      measure: total_revenue  # references measure in semantic model
```

### Derived Metrics

Math on other metrics. Use for ratios, percentages, and calculated KPIs.

```yaml
metrics:
  - name: average_order_value
    description: "Revenue per order"
    type: derived
    label: "Average Order Value (AOV)"
    type_params:
      expr: total_revenue / order_count  # references other metrics
      metrics:
        - name: total_revenue
        - name: order_count

```

### Cumulative Metrics

Running totals over time windows. Use for MRR, cumulative revenue, running user counts.

```yaml
metrics:
  - name: cumulative_revenue
    description: "Running total of revenue over all time"
    type: cumulative
    label: "Cumulative Revenue"
    type_params:
      measure: total_revenue
      # No window = all-time running total

  - name: trailing_28d_revenue
    description: "Rolling 28-day revenue window"
    type: cumulative
    label: "28-Day Revenue"
    type_params:
      measure: total_revenue
      window: 28 days  # rolling window
      # Commonly used: 7 days, 28 days, 90 days, 1 year
```

### Conversion Metrics

Funnel metrics that track progression between events. Use for signup funnels, purchase funnels, onboarding flows.

```yaml
metrics:
  - name: visit_to_purchase_rate
    description: "Percentage of site visits that result in a purchase"
    type: conversion
    label: "Visit-to-Purchase Rate"
    type_params:
      conversion_type_params:
        entity: customer_id                # entity to track through funnel
        base_measure: site_visits          # top of funnel
        conversion_measure: order_count    # bottom of funnel
        window: 7 days                     # conversion window
```

### DO / DON'T: Metric Definitions

```yaml
# DO: Define metrics in dbt, query from BI tools
metrics:
  - name: total_revenue
    type: simple
    type_params:
      measure: total_revenue

# DON'T: Redefine the same metric in each BI tool
# Looker: SUM(total_amount) WHERE status = 'completed'
# Tableau: SUM(total_amount) WHERE status IN ('completed', 'shipped')
# These will produce different numbers
```

---

## Model Contracts (dbt 1.5+)

### What They Are

Model contracts enforce column names and data types at build time. If a downstream consumer expects `order_id` to be a `string`, the contract guarantees it. A build fails if the SQL output does not match the contract.

### Configuration

```yaml
# models/marts/finance/_finance__models.yml
models:
  - name: fct_orders
    description: "One record per order with payment details"
    config:
      contract:
        enforced: true  # build fails if schema doesn't match
    columns:
      - name: order_id
        data_type: string
        data_tests: [unique, not_null]
      - name: customer_id
        data_type: string
        data_tests:
          - not_null
          - relationships:
              to: ref('dim_customers')
              field: customer_id
      - name: order_date
        data_type: date
        data_tests: [not_null]
      - name: order_status
        data_type: string
        data_tests:
          - accepted_values:
              values: ['completed', 'pending', 'cancelled', 'refunded']
      - name: total_amount
        data_type: float
        data_tests: [not_null]
```

### Snowflake vs BigQuery Type Mapping

| Logical Type | Snowflake | BigQuery |
|-------------|-----------|----------|
| string | VARCHAR | STRING |
| integer | NUMBER(38,0) | INT64 |
| float | FLOAT | FLOAT64 |
| boolean | BOOLEAN | BOOL |
| timestamp | TIMESTAMP_NTZ | TIMESTAMP |
| date | DATE | DATE |

Use the **logical type** (left column) in your contract YAML. dbt translates to the warehouse-specific type automatically.

### When to Enforce Contracts

| Layer | Enforce? | Reason |
|-------|----------|--------|
| Staging | No | Too rigid for cleaning layer; schemas change with source |
| Intermediate | No | Internal helper models; not consumed externally |
| Marts | **Yes** | Stable interface for BI tools and downstream teams |
| Any model consumed by external teams | **Yes** | Prevents breaking changes |
| Any model in the Semantic Layer | **Yes** | MetricFlow requires stable schemas |

### DO / DON'T: Contracts

```yaml
# DO: Enforce contracts on marts consumed by BI tools
models:
  - name: fct_orders
    config:
      contract:
        enforced: true
    columns:
      - name: order_id
        data_type: string

# DON'T: Enforce contracts on staging models
models:
  - name: stg_stripe__payments
    config:
      contract:
        enforced: true  # Too rigid -- source schema changes will break builds
```

---

## Model Versions (dbt 1.6+)

### What They Are

Model versions allow multiple versions of the same model to run simultaneously. Use them when you need to change a model's schema without breaking downstream consumers.

### Version Configuration

```yaml
# models/marts/finance/_finance__models.yml
models:
  - name: fct_orders
    description: "One record per order"
    latest_version: 2
    config:
      contract:
        enforced: true
    columns:  # shared across versions
      - name: order_id
        data_type: string
        data_tests: [unique, not_null]
      - name: customer_id
        data_type: string
      - name: order_date
        data_type: date
      - name: order_status
        data_type: string
      - name: total_amount
        data_type: float
    versions:
      - v: 1
        # v1 uses the default column set above
        defined_in: fct_orders_v1       # points to fct_orders_v1.sql
        deprecation_date: 2025-06-01    # warn consumers to migrate
      - v: 2
        defined_in: fct_orders_v2       # points to fct_orders_v2.sql
        columns:
          # v2 adds a new column not in v1
          - include: all
          - name: discount_amount
            data_type: float
            description: "Discount applied to the order"
```

### SQL Files for Each Version

```sql
-- models/marts/finance/fct_orders_v1.sql (original -- no discount column)
with orders as (
    select * from {{ ref('stg_shopify__orders') }}
),
payments as (
    select * from {{ ref('int_payments_pivoted') }}
),
final as (
    select
        orders.order_id, orders.customer_id, orders.order_date,
        orders.order_status, payments.total_amount
    from orders
    left join payments on orders.order_id = payments.order_id
)
select * from final
```

```sql
-- models/marts/finance/fct_orders_v2.sql (adds discount_amount)
with orders as (
    select * from {{ ref('stg_shopify__orders') }}
),
payments as (
    select * from {{ ref('int_payments_pivoted') }}
),
discounts as (
    select * from {{ ref('int_discounts_applied') }}
),
final as (
    select
        orders.order_id, orders.customer_id, orders.order_date,
        orders.order_status, payments.total_amount,
        coalesce(discounts.discount_amount, 0) as discount_amount
    from orders
    left join payments on orders.order_id = payments.order_id
    left join discounts on orders.order_id = discounts.order_id
)
select * from final
```

### Referencing Versioned Models

```sql
-- Default: references the latest_version (v2)
select * from {{ ref('fct_orders') }}

-- Explicit version: pin to a specific version
select * from {{ ref('fct_orders', v=1) }}  -- still using v1
select * from {{ ref('fct_orders', v=2) }}  -- explicitly v2
```

### Migration Strategy

1. **Create v2 alongside v1** -- both run in production simultaneously
2. **Migrate consumers one at a time** -- update `ref()` calls or let `latest_version` handle it
3. **Set deprecation date on v1** -- dbt warns when building deprecated versions
4. **Remove v1 after all consumers migrated** -- delete the version entry and SQL file

### DO / DON'T: Versioning

```yaml
# DO: Use versions for breaking schema changes on public models
models:
  - name: fct_orders
    latest_version: 2
    versions:
      - v: 1
        deprecation_date: 2025-06-01
      - v: 2

# DON'T: Version every model -- only version models with external consumers
# DON'T: Use versions for additive changes (just add the column to the existing model)
```

---

## Access Controls (dbt 1.5+)

### Access Levels

| Level | Who Can `ref()` | Use Case |
|-------|-----------------|----------|
| `private` | Same group only | Internal helper models |
| `protected` | Same project (default) | Standard within-project models |
| `public` | Any project | Stable interfaces for cross-project use |

### Group Definitions

Define groups in `dbt_project.yml` to represent teams or domains:

```yaml
# dbt_project.yml
groups:
  - name: finance
    owner:
      name: Finance Analytics
      email: finance-analytics@company.com
  - name: marketing
    owner:
      name: Marketing Analytics
      email: marketing-analytics@company.com
  - name: product
    owner:
      name: Product Analytics
      email: product-analytics@company.com
```

### Assigning Models to Groups

In YAML (`_finance__models.yml`):

```yaml
models:
  - name: fct_orders
    config: { group: finance }
    access: public           # any project can ref() this model
  - name: int_payments_pivoted
    config: { group: finance }
    access: private          # only finance group can ref() this model
  - name: dim_customers
    config: { group: finance }
    access: protected        # only this project can ref() (default)
```

Or in the model SQL file:

```sql
{{ config(materialized='table', group='finance', access='public') }}
```

### Cross-Group Restrictions

When a model in the `marketing` group tries to `ref()` a `private` model in the `finance` group, dbt raises an error:

```
Access to model 'int_payments_pivoted' is restricted.
Model is private to group 'finance'.
```

**Resolution options:**

1. Change the upstream model to `protected` or `public`
2. Create a `public` interface model in the finance group that exposes only the needed columns
3. Move the consuming model into the same group

### DO / DON'T: Access Controls

```yaml
# DO: Mark marts consumed by other teams as public
models:
  - name: fct_orders
    access: public
    config:
      group: finance
      contract:
        enforced: true  # public models should always have contracts

# DON'T: Make intermediate models public
models:
  - name: int_payments_pivoted
    access: public  # Too much exposure -- internal logic may change
```

---

## dbt Mesh (Multi-Project)

### What It Is

dbt Mesh enables cross-project `ref()` for large organizations. Each team owns a dbt project; projects reference each other's `public` models through a dependency graph.

### When to Split Into Multiple Projects

| Signal | Action |
|--------|--------|
| 50+ models in a single project | Consider splitting by domain |
| Multiple teams owning different domains | Split by domain ownership |
| Different deployment cadences | Split by cadence (hourly vs daily) |
| Shared utility models (date spine, currency rates) | Extract to a shared project |
| CI builds taking 30+ minutes | Split to enable independent builds |

### Producer / Consumer Pattern

```
shared_project (producer)       finance_project (consumer)       marketing_project (consumer)
  dim_date (public) ──────────▶ ref('shared', 'dim_date')
  dim_currency (public) ──────▶ fct_orders ──────────────────▶ ref('finance', 'fct_orders')
  stg_* (private)               dim_customers                   fct_campaigns
```

- **Producer** publishes `public` models with enforced contracts
- **Consumer** references them via cross-project `ref()`

### Dependencies Configuration

```yaml
# finance_project/dependencies.yml
projects:
  - name: shared_project
    # dbt Cloud resolves this automatically
    # For dbt Core, specify the path or package

  - name: marketing_project
    # Only needed if finance also consumes from marketing
```

### Complete Example Setup

**Shared project -- publishes utility models:**

```yaml
# shared_project/models/marts/_shared__models.yml
models:
  - name: dim_date
    access: public
    config:
      group: platform
      contract:
        enforced: true
    columns:
      - name: date_key
        data_type: date
        data_tests: [unique, not_null]
      - name: day_of_week
        data_type: string
      - name: fiscal_quarter
        data_type: string
      - name: is_holiday
        data_type: boolean
```

**Finance project -- consumes shared, publishes to marketing:**

```sql
-- finance_project/models/marts/fct_daily_revenue.sql
{{ config(materialized='table', group='finance', access='public', contract={'enforced': true}) }}

with orders as (
    select * from {{ ref('fct_orders') }}
),
dates as (
    select * from {{ ref('shared_project', 'dim_date') }}  -- cross-project ref
),
final as (
    select
        dates.date_key, dates.fiscal_quarter, dates.is_holiday,
        count(orders.order_id) as order_count,
        sum(orders.total_amount) as daily_revenue
    from orders
    inner join dates on orders.order_date = dates.date_key
    group by 1, 2, 3
)
select * from final
```

### dbt Mesh Checklist

Before enabling cross-project refs:

- [ ] All shared models have `access: public`
- [ ] All public models have `contract: { enforced: true }`
- [ ] Groups and owners are defined for every model
- [ ] `dependencies.yml` is configured in consumer projects
- [ ] Deployment order is documented (producers build before consumers)
- [ ] Cross-project tests are in place (relationships, freshness)

---

## Maturity Assessment

Use this table to identify your current stage and plan next steps.

### Capability Matrix

| Capability | Just Starting | Running in Prod | Multiple Teams | Enterprise |
|------------|--------------|----------------|----------------|------------|
| **Testing** | Basic YAML tests | Custom generics, unit tests | dbt-expectations, contracts | Full coverage + anomaly detection |
| **CI/CD** | Manual runs | GitHub Actions, Slim CI | dbt Cloud, blue/green | Multi-project orchestration |
| **Governance** | Naming conventions | Access controls, groups | Model versions, contracts | dbt Mesh, Semantic Layer |
| **Observability** | Source freshness | Elementary, Slack alerts | SLAs, incident runbooks | Full platform, PagerDuty |
| **Documentation** | Basic descriptions | Column descriptions, exposures | Data dictionary, lineage | Governed catalog |

### Actionable Next Steps by Stage

**Just Starting -- advance to Running in Prod:**

1. Add `unique` and `not_null` tests to every primary key
2. Set up `dbt build` in a CI pipeline (GitHub Actions or similar)
3. Configure source freshness checks with `loaded_at_field`
4. Write column-level descriptions for all marts models

**Running in Prod -- advance to Multiple Teams:**

1. Define groups and assign model ownership in `dbt_project.yml`
2. Set `access: public` on marts, `access: private` on intermediates
3. Enforce contracts on all models consumed by BI tools
4. Install `dbt-expectations` for advanced data quality tests
5. Create Slack alerts for test failures and source freshness warnings

**Multiple Teams -- advance to Enterprise:**

1. Evaluate dbt Mesh: identify producer and consumer projects
2. Implement model versions for any public model with breaking changes
3. Deploy the Semantic Layer: define semantic models and metrics for top 10 KPIs
4. Set SLAs for data freshness (e.g., "marts refresh within 2 hours of source load")
5. Build incident runbooks for common data quality failures

**Enterprise -- maintain and optimize:**

1. Integrate Semantic Layer with all BI tools (single metric definitions)
2. Implement automated anomaly detection (Elementary or Monte Carlo)
3. Set up PagerDuty / on-call rotation for critical pipeline failures
4. Version all public models; enforce deprecation timelines
5. Publish a governed data catalog with lineage and ownership metadata

### Governance Quick Reference

| Feature | dbt Version | Purpose | Apply To |
|---------|------------|---------|----------|
| Access controls | 1.5+ | Restrict who can `ref()` a model | All models |
| Model contracts | 1.5+ | Enforce schema at build time | Marts, public models |
| Groups | 1.5+ | Assign team ownership | All models |
| Model versions | 1.6+ | Run multiple versions simultaneously | Public models with breaking changes |
| Semantic Layer | 1.6+ / Cloud | Centralized metric definitions | Key business metrics |
| dbt Mesh | 1.6+ / Cloud | Cross-project `ref()` | Multi-team organizations |

---

**Back to:** [Main Skill File](../SKILL.md)
