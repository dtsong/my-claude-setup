# Incremental Models & Performance

> **Part of:** [dbt-skill](../SKILL.md)
> **Purpose:** Complete guide to incremental strategies, warehouse-specific performance tuning, and cost optimization for Snowflake and BigQuery

This document covers every incremental materialization strategy, when to use each, warehouse-specific performance techniques, and cost monitoring patterns. For high-level materialization guidance, see the [main skill file](../SKILL.md).

---

## Table of Contents

1. [Incremental Strategy Decision Matrix](#1-incremental-strategy-decision-matrix)
2. [Microbatch Deep Dive (dbt 1.9+)](#2-microbatch-deep-dive-dbt-19)
3. [Traditional Incremental Patterns](#3-traditional-incremental-patterns)
4. [is_incremental() Block Patterns](#4-is_incremental-block-patterns)
5. [Full Refresh Management](#5-full-refresh-management)
6. [Snowflake Performance](#6-snowflake-performance)
7. [BigQuery Performance](#7-bigquery-performance)
8. [Query Optimization](#8-query-optimization)
9. [Cost Monitoring](#9-cost-monitoring)

---

## 1. Incremental Strategy Decision Matrix

| Strategy | How It Works | Best For | Snowflake | BigQuery |
|----------|-------------|----------|-----------|----------|
| `microbatch` (1.9+) | Process time-based batches independently | Event/time-series data | Yes | Yes |
| `merge` | MERGE statement with unique_key | Most use cases, upserts | Yes (default) | Yes (default) |
| `delete+insert` | Delete matching rows, then insert | When merge is expensive | Yes | No |
| `insert_overwrite` | Replace entire partitions | Partition-aligned event data | No | Yes |
| `append` | Insert only, no updates | Immutable event logs | Yes | Yes |

### Decision Flowchart

```
Is the data time-series or event-based?
├── YES → Do rows ever get updated after initial insert?
│   ├── NO → Is the table partitioned by date?
│   │   ├── YES (BigQuery) → insert_overwrite
│   │   ├── YES (Snowflake) → microbatch (1.9+) or append
│   │   └── NO → append
│   └── YES → Is dbt 1.9+ available?
│       ├── YES → microbatch (preferred)
│       └── NO → merge with lookback window
├── NO → Does the source have a reliable updated_at column?
│   ├── YES → merge with updated_at filter
│   └── NO → Does the table have a unique key?
│       ├── YES (Snowflake) → delete+insert
│       ├── YES (BigQuery) → merge
│       └── NO → append (with deduplication downstream)
```

### Strategy Comparison

| Criteria | microbatch | merge | delete+insert | insert_overwrite | append |
|----------|-----------|-------|---------------|------------------|--------|
| Handles late-arriving data | Built-in | Manual lookback | Manual lookback | By partition | No |
| Supports updates | Yes (with unique_key) | Yes | Yes | Partition-level | No |
| Requires unique_key | Optional | Yes | Yes | No | No |
| Partial retry on failure | Yes | No | No | No | No |
| Compute cost | Low (parallel batches) | Medium | Medium | Low | Lowest |
| Complexity | Low | Medium | Medium | Low | Lowest |

---

## 2. Microbatch Deep Dive (dbt 1.9+)

Microbatch is a first-class incremental strategy that processes data in discrete time-based batches. Each batch runs independently, enabling parallel execution and targeted retries.

### How Microbatch Works

```
Source data (30 days)
    ↓
dbt splits into batches (e.g., 1 batch per day)
    ↓
┌─────────┬─────────┬─────────┬─────────┐
│ Day 1   │ Day 2   │ Day 3   │ ... N   │  ← Each batch runs independently
└─────────┴─────────┴─────────┴─────────┘
    ↓
Failed batches retry without re-running successful ones
```

### Configuration

| Config Key | Required | Description |
|-----------|----------|-------------|
| `incremental_strategy` | Yes | Set to `'microbatch'` |
| `event_time` | Yes | Timestamp column for batch slicing |
| `begin` | Yes | Earliest date to process (ISO format) |
| `batch_size` | Yes | `'hour'`, `'day'`, `'month'`, or `'year'` |
| `unique_key` | No | Column(s) for deduplication within batches |
| `lookback` | No | Number of extra prior batches to reprocess (default: `0`) |

### Complete Model Example

```sql
-- fct_app_events.sql
-- Microbatch: dbt handles time filtering automatically.
-- No {% if is_incremental() %} block needed.

{{ config(
    materialized='incremental',
    incremental_strategy='microbatch',
    event_time='event_occurred_at',
    begin='2023-01-01',
    batch_size='day',
    unique_key='event_id'
) }}

select
    event_id,
    user_id,
    event_type,
    event_occurred_at,
    event_payload
from {{ ref('stg_app__events') }}
```

### Key Advantage: No is_incremental() Block

With microbatch, dbt automatically filters each batch by `event_time`. Write the model as if processing all data -- dbt handles the windowing.

```sql
-- DO: Write clean SQL, let microbatch handle filtering
{{ config(
    materialized='incremental',
    incremental_strategy='microbatch',
    event_time='event_occurred_at',
    begin='2023-01-01',
    batch_size='day'
) }}

select
    event_id,
    user_id,
    event_type,
    event_occurred_at
from {{ ref('stg_app__events') }}
-- No {% if is_incremental() %} needed

-- DON'T: Add manual filtering on top of microbatch
{{ config(
    materialized='incremental',
    incremental_strategy='microbatch',
    event_time='event_occurred_at',
    begin='2023-01-01',
    batch_size='day'
) }}

select *
from {{ ref('stg_app__events') }}
{% if is_incremental() %}
where event_occurred_at > (select max(event_occurred_at) from {{ this }})
{% endif %}
-- Redundant: microbatch already filters by event_time
```

### Parallel Batch Execution

Microbatch processes batches independently. On supported adapters, batches execute in parallel, reducing wall-clock time for large backfills.

```bash
# First run: processes all batches from begin date to today
dbt run -s fct_app_events

# Subsequent runs: processes only the latest batch(es)
dbt run -s fct_app_events
```

### Retry Failed Batches

If a run fails partway through, `dbt retry` re-runs only the failed batches:

```bash
# Run processes 30 batches, 3 fail
dbt run -s fct_app_events

# Retry re-runs only the 3 failed batches
dbt retry
```

### Targeted Backfills

Use `--event-time-start` and `--event-time-end` to reprocess a specific time range without touching other data:

```bash
# Reprocess a specific date range (e.g., data correction)
dbt run -s fct_app_events --event-time-start 2024-03-01 --event-time-end 2024-03-15

# Reprocess a single day
dbt run -s fct_app_events --event-time-start 2024-06-15 --event-time-end 2024-06-16
```

### Lookback for Late-Arriving Data

Set `lookback` to reprocess prior batches and capture late-arriving records:

```sql
{{ config(
    materialized='incremental',
    incremental_strategy='microbatch',
    event_time='event_occurred_at',
    begin='2023-01-01',
    batch_size='day',
    unique_key='event_id',
    lookback=3              -- Reprocess 3 prior days each run
) }}

select
    event_id,
    user_id,
    event_type,
    event_occurred_at
from {{ ref('stg_app__events') }}
```

### Batch Size Selection

| Batch Size | Use When | Typical Volume |
|-----------|----------|----------------|
| `hour` | High-volume streams, near-real-time | > 10M rows/day |
| `day` | Standard event data (most common) | 100K - 10M rows/day |
| `month` | Low-volume or slowly changing data | < 100K rows/day |
| `year` | Historical backfill of sparse data | Rarely used in production |

---

## 3. Traditional Incremental Patterns

### Merge (Default Strategy)

Use merge for models that require upserts -- inserting new rows and updating existing ones based on a unique key.

```sql
-- fct_orders.sql
{{ config(
    materialized='incremental',
    unique_key='order_id',
    on_schema_change='append_new_columns'
) }}

select
    order_id,
    customer_id,
    order_status,
    order_total,
    updated_at
from {{ ref('stg_shopify__orders') }}
{% if is_incremental() %}
where updated_at > (select max(updated_at) from {{ this }})
{% endif %}
```

**Snowflake compiled SQL (simplified):**

```sql
merge into analytics.fct_orders as target
using (
    select order_id, customer_id, order_status, order_total, updated_at
    from analytics.stg_shopify__orders
    where updated_at > (select max(updated_at) from analytics.fct_orders)
) as source
on target.order_id = source.order_id
when matched then update set
    customer_id = source.customer_id,
    order_status = source.order_status,
    order_total = source.order_total,
    updated_at = source.updated_at
when not matched then insert
    (order_id, customer_id, order_status, order_total, updated_at)
    values (source.order_id, source.customer_id, source.order_status,
            source.order_total, source.updated_at);
```

### Compound Unique Key

Use a list when a single column does not uniquely identify rows:

```sql
{{ config(
    materialized='incremental',
    unique_key=['order_id', 'line_item_id'],
    on_schema_change='append_new_columns'
) }}

select
    order_id,
    line_item_id,
    product_id,
    quantity,
    unit_price,
    updated_at
from {{ ref('stg_shopify__order_line_items') }}
{% if is_incremental() %}
where updated_at > (select max(updated_at) from {{ this }})
{% endif %}
```

### Delete+Insert (Snowflake Only)

Use delete+insert when merge performance degrades on large tables or when the merge statement becomes expensive due to wide tables.

```sql
-- fct_order_events.sql (Snowflake)
{{ config(
    materialized='incremental',
    incremental_strategy='delete+insert',
    unique_key='event_id'
) }}

select
    event_id,
    order_id,
    event_type,
    event_payload,
    created_at
from {{ ref('stg_shopify__order_events') }}
{% if is_incremental() %}
where created_at > (select max(created_at) from {{ this }})
{% endif %}
```

### Insert Overwrite (BigQuery Only)

Use insert_overwrite for partition-aligned event data. Replaces entire partitions rather than merging individual rows.

```sql
-- fct_page_views.sql (BigQuery)
{{ config(
    materialized='incremental',
    incremental_strategy='insert_overwrite',
    partition_by={
        "field": "page_view_date",
        "data_type": "date",
        "granularity": "day"
    }
) }}

select
    page_view_id,
    user_id,
    page_url,
    referrer_url,
    cast(page_view_at as date) as page_view_date,
    page_view_at
from {{ ref('stg_web__page_views') }}

-- BigQuery automatically determines which partitions to overwrite
-- based on the data returned by this query
```

**With static partitions for controlled overwrites:**

```sql
{{ config(
    materialized='incremental',
    incremental_strategy='insert_overwrite',
    partition_by={
        "field": "page_view_date",
        "data_type": "date",
        "granularity": "day",
        "copy_partitions": true
    },
    partitions=["'2024-01-01'", "'2024-01-02'", "'2024-01-03'"]
) }}
```

### Append (All Warehouses)

Use append for immutable event streams where rows are never updated.

```sql
-- fct_clickstream.sql
{{ config(
    materialized='incremental',
    incremental_strategy='append'
) }}

select
    click_id,
    session_id,
    user_id,
    element_id,
    page_url,
    clicked_at
from {{ ref('stg_analytics__clicks') }}
{% if is_incremental() %}
where clicked_at > (select max(clicked_at) from {{ this }})
{% endif %}

-- No unique_key: rows are never updated or deduplicated
-- If duplicates are possible, handle deduplication in a downstream model
```

---

## 4. is_incremental() Block Patterns

### Basic High-Watermark Pattern

The most common approach -- select rows newer than the most recent row already loaded:

```sql
{% if is_incremental() %}
where updated_at > (select max(updated_at) from {{ this }})
{% endif %}
```

### Lookback Window for Late-Arriving Data

Add a lookback buffer to capture records that arrive after their event timestamp:

```sql
-- 3-hour lookback: reprocess recent data each run
{% if is_incremental() %}
where event_at > (
    select dateadd(hour, -3, max(event_at)) from {{ this }}
)
{% endif %}
```

```sql
-- BigQuery equivalent
{% if is_incremental() %}
where event_at > (
    select timestamp_sub(max(event_at), interval 3 hour) from {{ this }}
)
{% endif %}
```

### Multiple Conditions Pattern

Combine the incremental filter with business logic filters:

```sql
{% if is_incremental() %}
where
    updated_at > (select max(updated_at) from {{ this }})
    and order_status != 'draft'              -- Business filter
    and _fivetran_deleted = false             -- Soft-delete filter
{% endif %}
```

### Partition-Aware Filter (BigQuery)

Filter on the partition column directly for partition pruning:

```sql
{% if is_incremental() %}
where
    date(event_at) >= (
        select date_sub(max(date(event_at)), interval 1 day)
        from {{ this }}
    )
{% endif %}
```

### Anti-Pattern: Overly Complex is_incremental() Blocks

```sql
-- DON'T: Complex multi-step logic inside is_incremental()
{% if is_incremental() %}
    {% set max_ts_query %}
        select max(updated_at) from {{ this }}
    {% endset %}
    {% set max_ts = run_query(max_ts_query).columns[0][0] %}
    {% if max_ts is none %}
        where true
    {% else %}
        where updated_at > '{{ max_ts }}'
              and category in (
                  select distinct category
                  from {{ source('raw', 'categories') }}
                  where is_active = true
              )
    {% endif %}
{% endif %}

-- DO: Use microbatch instead for time-based processing,
-- or simplify the filter to a single high-watermark comparison
{% if is_incremental() %}
where updated_at > (select max(updated_at) from {{ this }})
{% endif %}
```

### When is_incremental() Returns True

`is_incremental()` returns `true` only when ALL of these conditions are met:

1. The model is materialized as `incremental`
2. The target table already exists in the warehouse
3. The run is NOT a `--full-refresh` run
4. The run is NOT the first run (table must exist)

---

## 5. Full Refresh Management

### When to Force a Full Refresh

```bash
# Rebuild a single model from scratch
dbt run --full-refresh -s fct_orders

# Rebuild a model and all its downstream dependents
dbt run --full-refresh -s fct_orders+

# Rebuild all incremental models
dbt run --full-refresh -s config.materialized:incremental
```

**Trigger a full refresh when:**

| Scenario | Why |
|----------|-----|
| Schema change (column added/removed) | Incremental may miss new columns |
| Logic change in the model | Historical data needs reprocessing |
| Data quality issue discovered | Corrupted incremental state |
| Source data was reloaded | Upstream data changed retroactively |
| Switching incremental strategies | New strategy needs clean table |

### on_schema_change Options

| Setting | Behavior | Use When |
|---------|----------|----------|
| `ignore` (default) | Silently skip new columns | Schema is stable, no changes expected |
| `append_new_columns` | Add new columns (nulls for existing rows) | Source adds columns over time |
| `sync_all_columns` | Add new columns, remove dropped columns | Schema must match exactly |
| `fail` | Raise an error on any schema change | Strict CI environments |

```sql
-- Recommended for most incremental models
{{ config(
    materialized='incremental',
    unique_key='order_id',
    on_schema_change='append_new_columns'    -- Safe default for evolving sources
) }}
```

### on_schema_change Decision Table

| Scenario | Recommended Setting | Rationale |
|----------|-------------------|-----------|
| Stable source, production | `ignore` | No schema changes expected |
| Evolving source (e.g., Fivetran) | `append_new_columns` | New columns added without breaking |
| Strict data contract | `fail` | Force explicit schema management |
| Development/experimentation | `sync_all_columns` | Keep schema in sync during iteration |
| Columns may be dropped | `sync_all_columns` | Remove orphaned columns |

### Scheduling Full Refreshes

Build periodic full refreshes into CI/CD to prevent incremental drift:

```yaml
# dbt Cloud job configuration (conceptual)
# Weekly full refresh for all incremental models
- name: "Weekly Full Refresh"
  schedule: "0 2 * * 0"                     # Sunday 2 AM
  command: "dbt run --full-refresh -s config.materialized:incremental"

# Daily incremental run
- name: "Daily Incremental"
  schedule: "0 6 * * *"                     # Daily 6 AM
  command: "dbt run"
```

```yaml
# GitHub Actions example
name: Weekly Full Refresh
on:
  schedule:
    - cron: '0 2 * * 0'
jobs:
  full_refresh:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Run full refresh
        run: dbt run --full-refresh -s config.materialized:incremental
        env:
          DBT_PROFILES_DIR: ./
```

---

## 6. Snowflake Performance

### Cluster Keys

Snowflake micro-partitions are created automatically. Add explicit cluster keys when query patterns consistently filter on specific columns and table scans are slow.

```sql
-- Add cluster keys for large, frequently filtered tables
{{ config(
    materialized='incremental',
    unique_key='event_id',
    cluster_by=['event_date', 'user_id']    -- Most-filtered columns first
) }}
```

**When to use cluster keys:**

| Condition | Action |
|-----------|--------|
| Table < 1 TB | Skip clustering (micro-partitions sufficient) |
| Table > 1 TB with slow filtered queries | Add cluster keys on filter columns |
| High-cardinality filter column | Good candidate (e.g., user_id, date) |
| Low-cardinality column only | Poor candidate (e.g., boolean status) |
| Frequent range scans | Cluster on the range column (e.g., date) |

**Monitor clustering effectiveness:**

```sql
-- Check clustering depth (lower is better)
select system$clustering_information('analytics.fct_events', '(event_date, user_id)');

-- Monitor automatic reclustering credits
select *
from snowflake.account_usage.automatic_clustering_history
where table_name = 'FCT_EVENTS'
order by start_time desc
limit 10;
```

### Transient Tables

Skip Snowflake's 7-day fail-safe period for tables that can be rebuilt from source. Saves significant storage cost on large tables.

```sql
-- Transient: no fail-safe, reducible time travel (0-1 day)
{{ config(
    materialized='incremental',
    unique_key='event_id',
    transient=true                           -- Skip fail-safe, save storage
) }}
```

| Table Type | Time Travel | Fail-Safe | Storage Cost | Use For |
|-----------|-------------|-----------|--------------|---------|
| Permanent (default) | 0-90 days | 7 days | Highest | Critical business data |
| Transient | 0-1 day | None | Lower | Rebuildable dbt models |

```sql
-- Set transient as default for all models in dbt_project.yml
-- dbt_project.yml
-- models:
--   my_project:
--     marts:
--       +transient: true
```

### Dynamic Tables

Snowflake Dynamic Tables automate incremental refreshes at the warehouse level. Use when the transformation is simple and near-real-time freshness is needed.

```sql
-- Dynamic table: Snowflake manages refresh automatically
{{ config(
    materialized='dynamic_table',
    target_lag='5 minutes',                  -- Snowflake refreshes within 5 min of source change
    snowflake_warehouse='transformations_wh'
) }}

select
    order_id,
    customer_id,
    order_total,
    updated_at
from {{ ref('stg_shopify__orders') }}
```

| Feature | dbt Incremental | Snowflake Dynamic Table |
|---------|----------------|------------------------|
| Refresh trigger | dbt run (scheduled) | Automatic (lag-based) |
| Freshness | Minutes to hours (job interval) | Seconds to minutes |
| Complex transforms | Full Jinja/SQL support | SQL only (no Jinja at runtime) |
| Cost control | Warehouse sizing + schedule | Dedicated warehouse + lag setting |
| Retry/backfill | Manual or dbt retry | Automatic |

**Use Dynamic Tables when:**
- Near-real-time freshness required (< 5 min lag)
- Transformation is straightforward SQL
- Upstream tables are in the same Snowflake account

**Use dbt incremental when:**
- Complex Jinja logic or macros involved
- Cross-database sources
- Fine-grained control over refresh logic
- Cost-sensitive batch workloads

### Warehouse Sizing

| Environment | Recommended Size | Rationale |
|-------------|-----------------|-----------|
| Local development | X-SMALL | Minimize cost for ad-hoc queries |
| CI/CD (Slim CI) | SMALL | Fast enough for modified models |
| CI/CD (Full build) | MEDIUM | Balance speed and cost |
| Production (light) | SMALL - MEDIUM | Standard scheduled runs |
| Production (heavy) | LARGE+ | High-volume incremental models |

```sql
-- Set warehouse per model or folder in dbt_project.yml
-- models:
--   my_project:
--     staging:
--       +snowflake_warehouse: transformations_wh_xs
--     marts:
--       +snowflake_warehouse: transformations_wh_m
```

```sql
-- Or per-model override for expensive models
{{ config(
    materialized='incremental',
    unique_key='event_id',
    snowflake_warehouse='transformations_wh_lg'
) }}
```

### Zero-Copy Cloning for Dev/Test

Clone production databases for development without duplicating storage:

```sql
-- Create a dev clone of production (zero storage cost until data diverges)
create database analytics_dev clone analytics;

-- In profiles.yml, point dev target to cloned database
-- profiles.yml:
--   my_project:
--     target: dev
--     outputs:
--       dev:
--         type: snowflake
--         database: analytics_dev
```

### Query Profiling

```sql
-- Find slowest dbt models by execution time
select
    query_text,
    total_elapsed_time / 1000 as elapsed_seconds,
    bytes_scanned / (1024*1024*1024) as gb_scanned,
    rows_produced,
    warehouse_name
from snowflake.account_usage.query_history
where query_tag like '%dbt%'
    and start_time > dateadd(day, -7, current_timestamp())
order by total_elapsed_time desc
limit 20;

-- Warehouse credit usage by model tag
select
    query_tag,
    count(*) as query_count,
    sum(total_elapsed_time) / 1000 as total_seconds,
    sum(credits_used_cloud_services) as credits_used
from snowflake.account_usage.query_history
where query_tag like '%dbt%'
    and start_time > dateadd(day, -7, current_timestamp())
group by query_tag
order by credits_used desc;
```

---

## 7. BigQuery Performance

### Partition Strategies

Every large BigQuery table should be partitioned. Partitioning limits the amount of data scanned per query, directly reducing cost.

| Partition Type | Config | Use When |
|---------------|--------|----------|
| Date/Timestamp column | `"data_type": "date"` or `"timestamp"` | Table has a date/time column |
| Ingestion time | `"data_type": "timestamp", "field": "_PARTITIONTIME"` | No reliable date column |
| Integer range | `"data_type": "int64", "range": {...}` | Partition by numeric ID range |

### Partition Configuration

```sql
-- Date partitioning (most common)
{{ config(
    materialized='incremental',
    unique_key='order_id',
    partition_by={
        "field": "order_date",
        "data_type": "date",
        "granularity": "day"                 -- day, month, or year
    }
) }}

-- Timestamp partitioning (hour-level granularity)
{{ config(
    materialized='incremental',
    unique_key='event_id',
    partition_by={
        "field": "event_at",
        "data_type": "timestamp",
        "granularity": "hour"
    }
) }}

-- Integer range partitioning
{{ config(
    materialized='incremental',
    unique_key='user_id',
    partition_by={
        "field": "user_id",
        "data_type": "int64",
        "range": {
            "start": 0,
            "end": 100000000,
            "interval": 1000
        }
    }
) }}
```

### Partition with copy_partitions

Use `copy_partitions: true` with `insert_overwrite` to avoid unnecessary data movement:

```sql
{{ config(
    materialized='incremental',
    incremental_strategy='insert_overwrite',
    partition_by={
        "field": "event_date",
        "data_type": "date",
        "granularity": "day",
        "copy_partitions": true              -- Copies partitions directly (faster)
    }
) }}
```

### Cluster Columns

Add up to 4 cluster columns to optimize query filtering within partitions. Choose high-cardinality columns that appear in WHERE and JOIN clauses.

```sql
{{ config(
    materialized='incremental',
    unique_key='event_id',
    partition_by={
        "field": "event_date",
        "data_type": "date"
    },
    cluster_by=['user_id', 'event_type']     -- Up to 4 columns
) }}
```

**Cluster column selection:**

| Priority | Column Type | Example |
|----------|------------|---------|
| 1st | Most common filter column | `user_id` |
| 2nd | Second most common filter | `event_type` |
| 3rd | Join key | `product_id` |
| 4th | Secondary filter | `region` |

### require_partition_filter

Prevent accidental full table scans by requiring a partition filter in every query:

```sql
{{ config(
    materialized='incremental',
    unique_key='event_id',
    partition_by={
        "field": "event_date",
        "data_type": "date"
    },
    require_partition_filter=true             -- Queries MUST filter on event_date
) }}
```

**When to use:**

| Scenario | require_partition_filter |
|----------|------------------------|
| Large fact tables (> 1 TB) | Yes -- prevent expensive scans |
| Frequently queried by analysts | Yes -- enforce cost discipline |
| Tables only accessed by dbt downstream | No -- dbt generates correct filters |
| Small dimension tables | No -- full scan is cheap |

### maximum_bytes_billed

Set a safety limit to kill queries that scan too much data:

```sql
-- Per-model safety limit
{{ config(
    materialized='incremental',
    unique_key='event_id',
    maximum_bytes_billed=1000000000000       -- 1 TB limit
) }}
```

### Slot Management

| Pricing Model | How It Works | Best For |
|--------------|-------------|----------|
| On-demand | Pay per TB scanned | Unpredictable workloads |
| Editions (Standard/Enterprise) | Autoscaling reservations | Predictable dbt workloads |

**Autoscaling reservations for dbt:**

```
Baseline slots: 100 (always available)
Autoscale max:  400 (scales up for dbt runs)
Idle scale-down: 0  (no cost when idle)
```

### Bytes Billed Monitoring

```sql
-- Top 20 most expensive dbt queries (last 7 days)
select
    job_id,
    user_email,
    query,
    total_bytes_billed / (1024*1024*1024) as gb_billed,
    total_bytes_billed / (1024*1024*1024*1024) * 6.25 as estimated_cost_usd,
    creation_time,
    total_slot_ms / 1000 as slot_seconds
from `region-us`.INFORMATION_SCHEMA.JOBS
where creation_time > timestamp_sub(current_timestamp(), interval 7 day)
    and statement_type != 'SCRIPT'
    and job_type = 'QUERY'
    and state = 'DONE'
order by total_bytes_billed desc
limit 20;

-- Daily cost trend for dbt jobs
select
    date(creation_time) as query_date,
    count(*) as query_count,
    sum(total_bytes_billed) / (1024*1024*1024*1024) as tb_billed,
    sum(total_bytes_billed) / (1024*1024*1024*1024) * 6.25 as estimated_cost_usd
from `region-us`.INFORMATION_SCHEMA.JOBS
where creation_time > timestamp_sub(current_timestamp(), interval 30 day)
    and user_email like '%dbt%'              -- Filter for dbt service account
    and state = 'DONE'
group by query_date
order by query_date desc;
```

---

## 8. Query Optimization

### CTE Behavior Differences

| Warehouse | CTE Behavior | Implication |
|-----------|-------------|-------------|
| Snowflake | May materialize CTEs as temp results | Repeated CTE references may re-execute; use intermediate models for heavy CTEs |
| BigQuery | Inlines CTEs into the query plan | Large CTEs referenced multiple times increase bytes scanned |

```sql
-- DO: Extract heavily-reused CTEs into their own models
-- models/intermediate/int_user_activity_daily.sql
{{ config(materialized='ephemeral') }}

select
    user_id,
    date(event_at) as activity_date,
    count(*) as event_count
from {{ ref('stg_app__events') }}
group by 1, 2

-- Then reference once in downstream models
-- models/marts/fct_user_engagement.sql
select * from {{ ref('int_user_activity_daily') }}
where event_count > 5

-- DON'T: Define a heavy CTE and reference it 3+ times in the same model
```

### Column Pruning

Select only the columns needed. In BigQuery, every column scanned adds to bytes billed.

```sql
-- DO: Select specific columns
select
    order_id,
    customer_id,
    order_total,
    order_date
from {{ ref('stg_shopify__orders') }}

-- DON'T: Select all columns in marts or downstream models
select *
from {{ ref('stg_shopify__orders') }}
-- In BigQuery, this scans ALL columns (including large payload fields)
-- In Snowflake, this still transfers unnecessary data
```

### Join Optimization

Filter before joining to reduce the data volume in the join operation:

```sql
-- DO: Filter early, then join
with recent_orders as (
    select order_id, customer_id, order_total
    from {{ ref('stg_shopify__orders') }}
    where order_date >= '2024-01-01'         -- Filter before join
),

payments as (
    select order_id, payment_method, amount
    from {{ ref('stg_stripe__payments') }}
    where payment_status = 'completed'       -- Filter before join
)

select
    o.order_id,
    o.customer_id,
    o.order_total,
    p.payment_method,
    p.amount
from recent_orders o
left join payments p on o.order_id = p.order_id

-- DON'T: Join full tables then filter
select
    o.order_id,
    o.customer_id,
    o.order_total,
    p.payment_method,
    p.amount
from {{ ref('stg_shopify__orders') }} o
left join {{ ref('stg_stripe__payments') }} p on o.order_id = p.order_id
where o.order_date >= '2024-01-01'
    and p.payment_status = 'completed'
```

### Window Function Optimization

Partition window functions by high-cardinality columns to limit the sort/partition scope:

```sql
-- DO: Partition by a high-cardinality key
select
    user_id,
    event_at,
    row_number() over (
        partition by user_id                 -- High cardinality, small partitions
        order by event_at desc
    ) as event_rank
from {{ ref('stg_app__events') }}

-- DON'T: Partition by low-cardinality or no partition at all
select
    user_id,
    event_at,
    row_number() over (
        order by event_at desc               -- Sorts entire table, very expensive
    ) as event_rank
from {{ ref('stg_app__events') }}
```

### Avoid SELECT * in Downstream Models

Using `SELECT *` in models that depend on incremental models breaks `on_schema_change` behavior and causes unexpected failures:

```sql
-- DON'T: SELECT * from an incremental model
select * from {{ ref('fct_orders') }}
-- If fct_orders adds a column, this model silently picks it up
-- If fct_orders drops a column, this model breaks

-- DO: Explicitly list columns
select
    order_id,
    customer_id,
    order_total,
    order_date
from {{ ref('fct_orders') }}
```

---

## 9. Cost Monitoring

### Snowflake Credit Monitoring

```sql
-- Daily credit usage by warehouse (last 30 days)
select
    warehouse_name,
    date(start_time) as usage_date,
    sum(credits_used) as total_credits,
    sum(credits_used) * 3.00 as estimated_cost_usd  -- Adjust rate per contract
from snowflake.account_usage.warehouse_metering_history
where start_time > dateadd(day, -30, current_timestamp())
group by warehouse_name, usage_date
order by usage_date desc, total_credits desc;

-- Warehouse utilization (idle vs active time)
select
    warehouse_name,
    sum(credits_used) as credits_used,
    sum(credits_used_compute) as compute_credits,
    sum(credits_used_cloud_services) as cloud_credits,
    avg(avg_running) as avg_concurrent_queries,
    avg(avg_queued_load) as avg_queued_queries
from snowflake.account_usage.warehouse_metering_history
where start_time > dateadd(day, -7, current_timestamp())
group by warehouse_name
order by credits_used desc;
```

### BigQuery Cost Monitoring

```sql
-- Monthly cost by dataset (proxy for dbt layer)
select
    date_trunc(creation_time, month) as month,
    split(destination_table.dataset_id, '_')[safe_offset(0)] as layer,
    count(*) as query_count,
    sum(total_bytes_billed) / power(1024, 4) as tb_billed,
    sum(total_bytes_billed) / power(1024, 4) * 6.25 as estimated_cost_usd
from `region-us`.INFORMATION_SCHEMA.JOBS
where creation_time > timestamp_sub(current_timestamp(), interval 90 day)
    and job_type = 'QUERY'
    and state = 'DONE'
group by month, layer
order by month desc, estimated_cost_usd desc;

-- Identify models causing slot contention
select
    query,
    total_slot_ms / 1000 as slot_seconds,
    total_bytes_billed / (1024*1024*1024) as gb_billed,
    creation_time
from `region-us`.INFORMATION_SCHEMA.JOBS
where creation_time > timestamp_sub(current_timestamp(), interval 7 day)
    and total_slot_ms > 600000               -- > 10 slot-minutes
    and state = 'DONE'
order by total_slot_ms desc
limit 20;
```

### Alerting Thresholds

| Metric | Warning | Critical | Action |
|--------|---------|----------|--------|
| **Snowflake daily credits** | > 120% of baseline | > 200% of baseline | Investigate warehouse usage |
| **Snowflake query queue** | > 5 min avg | > 15 min avg | Upsize warehouse or split workloads |
| **BigQuery daily TB billed** | > 120% of baseline | > 200% of baseline | Check for missing partition filters |
| **BigQuery slot utilization** | > 80% sustained | > 95% sustained | Add autoscaling capacity |
| **dbt model runtime** | > 2x historical avg | > 5x historical avg | Investigate data volume spike |
| **Full refresh cost** | > 3x incremental cost | > 10x incremental cost | Optimize or split model |

### dbt Model-Level Cost Tagging

Tag models to attribute costs back to business domains:

```yaml
# dbt_project.yml
models:
  my_project:
    staging:
      +tags: ['staging', 'low-cost']
    marts:
      finance:
        +tags: ['marts', 'finance']
      marketing:
        +tags: ['marts', 'marketing']
```

```sql
-- Snowflake: Set query tags for cost attribution
-- In a macro (macros/set_query_tag.sql):
{% macro set_query_tag() %}
    {% set tag = "dbt_" ~ this.schema ~ "_" ~ this.name %}
    alter session set query_tag = '{{ tag }}';
{% endmacro %}

-- Use in on-run-start or as a pre-hook
-- dbt_project.yml:
-- on-run-start:
--   - "{{ set_query_tag() }}"
```

### Cost Optimization Comparison

| Technique | Snowflake Impact | BigQuery Impact |
|-----------|-----------------|-----------------|
| **Partitioning** | Automatic (micro-partitions); cluster keys for targeted pruning | Critical -- reduces bytes scanned per query |
| **Clustering** | Reduces scan range on filtered queries | Reduces bytes scanned within partitions |
| **Incremental models** | Reduces compute time (credits) | Reduces bytes scanned (cost) |
| **Column pruning** | Minor -- columnar storage helps | Major -- directly reduces bytes billed |
| **Transient tables** | Saves 7-day fail-safe storage cost | N/A |
| **Warehouse auto-suspend** | Prevents idle credit burn | N/A (on-demand is per-query) |
| **require_partition_filter** | N/A | Prevents accidental full scans |
| **maximum_bytes_billed** | N/A | Kills runaway queries |
| **Reservation autoscaling** | N/A | Controls slot cost with flex capacity |
| **Ephemeral intermediate models** | Eliminates table storage and compute | Eliminates table storage and scan cost |
| **Dynamic tables** | Offloads scheduling to Snowflake; cost depends on lag | N/A |
| **Result caching** | Automatic for identical queries (free) | Automatic for identical queries (free) |

---

**Back to:** [Main Skill File](../SKILL.md)
