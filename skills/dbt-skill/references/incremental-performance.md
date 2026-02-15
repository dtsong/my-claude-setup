# Incremental Models & Performance

## Strategy Decision Matrix

| Strategy | Best For | Snowflake | BigQuery |
|----------|----------|-----------|----------|
| `microbatch` (1.9+) | Time-series/event data | Yes | Yes |
| `merge` | Most use cases, upserts | Yes (default) | Yes (default) |
| `delete+insert` | When merge is expensive | Yes | No |
| `insert_overwrite` | Partition-aligned events | No | Yes |
| `append` | Immutable event logs | Yes | Yes |

**Decision flow:** Time-series data? If rows never update: `insert_overwrite` (BQ) or `append`. If rows update: `microbatch` (1.9+) or `merge` with lookback. Non-time-series: `merge` with `updated_at` filter, or `delete+insert` (Snowflake) for wide tables.

## Microbatch (dbt 1.9+)

Processes data in independent time-based batches. No `is_incremental()` block needed -- dbt handles time filtering automatically.

```sql
{{ config(
    materialized='incremental',
    incremental_strategy='microbatch',
    event_time='event_occurred_at',
    begin='2023-01-01',
    batch_size='day',
    unique_key='event_id',
    lookback=3              -- reprocess 3 prior days for late-arriving data
) }}

select event_id, user_id, event_type, event_occurred_at
from {{ ref('stg_app__events') }}
```

| Config | Required | Description |
|--------|----------|-------------|
| `event_time` | Yes | Timestamp column for batch slicing |
| `begin` | Yes | Earliest date to process |
| `batch_size` | Yes | `hour`, `day`, `month`, `year` |
| `lookback` | No | Extra prior batches to reprocess (default 0) |

Key advantages: partial retry on failure (`dbt retry`), targeted backfills (`--event-time-start`/`--event-time-end`), parallel batch execution.

**Batch size:** `hour` for >10M rows/day, `day` for 100K-10M/day, `month` for <100K/day.

## Traditional Patterns

**Merge** (default): upsert with `unique_key`. Add `on_schema_change='append_new_columns'` for evolving sources.

```sql
{{ config(materialized='incremental', unique_key='order_id', on_schema_change='append_new_columns') }}
select order_id, customer_id, order_status, updated_at
from {{ ref('stg_shopify__orders') }}
{% if is_incremental() %}
where updated_at > (select max(updated_at) from {{ this }})
{% endif %}
```

**Delete+insert** (Snowflake only): better for wide tables where merge is expensive. Same pattern, set `incremental_strategy='delete+insert'`.

**Insert_overwrite** (BigQuery only): replaces entire partitions. Requires `partition_by` config. Use `copy_partitions: true` for efficiency.

**Append**: insert-only for immutable events. No `unique_key`. Handle deduplication downstream.

## is_incremental() Patterns

- **High-watermark:** `where updated_at > (select max(updated_at) from {{ this }})`
- **Lookback window:** `where event_at > (select dateadd(hour, -3, max(event_at)) from {{ this }})` (Snowflake) or `timestamp_sub(..., interval 3 hour)` (BigQuery)
- **Partition-aware (BQ):** Filter on partition column for pruning
- Returns `true` only when: model is incremental, target table exists, not `--full-refresh`

## Full Refresh

Trigger when: schema change, logic change, data quality issue, source reload, or switching strategies.

```bash
dbt run --full-refresh -s fct_orders       # single model
dbt run --full-refresh -s config.materialized:incremental  # all incremental
```

**on_schema_change options:** `ignore` (default, stable schemas), `append_new_columns` (evolving sources, recommended), `sync_all_columns` (strict match), `fail` (CI environments).

## Snowflake Performance

- **Cluster keys:** Add on tables >1TB with slow filtered queries. Use most-filtered columns first. Monitor with `system$clustering_information()`.
- **Transient tables:** `transient=true` skips 7-day fail-safe, saves storage on rebuildable models.
- **Dynamic tables:** `materialized='dynamic_table'` with `target_lag='5 minutes'` for near-real-time. Use for simple SQL only (no Jinja at runtime).
- **Warehouse sizing:** X-SMALL for dev/CI, SMALL-MEDIUM for CI full build, MEDIUM+ for production.
- **Zero-copy cloning:** `CREATE DATABASE analytics_dev CLONE analytics` for dev without storage cost.

## BigQuery Performance

- **Partitioning:** Required for large tables. Use date/timestamp column partitioning. Set `granularity` to day, month, or year. Add `require_partition_filter=true` on large fact tables.
- **Clustering:** Up to 4 columns. Choose high-cardinality columns from WHERE/JOIN clauses.
- **Cost controls:** `maximum_bytes_billed` per model or in profile. Autoscaling reservations for predictable workloads.
- **Insert_overwrite + copy_partitions:** Most efficient for partition-aligned event data.

## Query Optimization

- Extract heavy CTEs reused 3+ times into their own models
- Select only needed columns (critical for BigQuery bytes billed)
- Filter before joining to reduce join data volume
- Partition window functions by high-cardinality columns
- Avoid `SELECT *` in downstream models (breaks `on_schema_change`, hides dependencies)

## Cost Monitoring

**Snowflake:** Query `snowflake.account_usage.warehouse_metering_history` for daily credit usage. Use `query_tag` for cost attribution by model.

**BigQuery:** Query `INFORMATION_SCHEMA.JOBS` for bytes billed and slot usage.

| Metric | Warning | Critical |
|--------|---------|----------|
| Daily cost | >120% baseline | >200% baseline |
| Model runtime | >2x historical avg | >5x historical avg |
| Full refresh cost | >3x incremental | >10x incremental |
