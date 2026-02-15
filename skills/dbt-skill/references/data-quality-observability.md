# Data Quality & Observability

## Source Freshness

Configure `loaded_at_field` and thresholds in sources YAML, run `dbt source freshness`.

| Ingestion Tool | loaded_at_field |
|----------------|----------------|
| Fivetran | `_fivetran_synced` |
| Airbyte | `_airbyte_extracted_at` |
| Stitch | `_sdc_batched_at` |
| BigQuery native | `_PARTITIONTIME` |

```yaml
sources:
  - name: shopify
    loaded_at_field: _fivetran_synced
    freshness:
      warn_after: { count: 12, period: hour }
      error_after: { count: 24, period: hour }
    tables:
      - name: orders
      - name: customers
        freshness:
          warn_after: { count: 24, period: hour }
          error_after: { count: 48, period: hour }
```

Schedule freshness checks in CI (e.g., cron every 2 hours). Run before `dbt build` to catch stale sources early.

## Elementary Package

Adds anomaly detection and schema monitoring inside your warehouse.

Install: `elementary-data/elementary` (pin version). Set `+schema: elementary` in `dbt_project.yml`.

**Key tests:**
- `elementary.volume_anomalies` -- row count anomaly detection with configurable sensitivity
- `elementary.freshness_anomalies` -- data arrival delay detection
- `elementary.schema_changes` -- column add/remove/type change monitoring
- `elementary.column_anomalies` -- zero_count, null_count, average tracking

Generate HTML report: `dbt run-operation elementary.generate_report`. Send Slack alerts via webhook config.

## Anomaly Detection Patterns

Use when Elementary is unavailable, or as supplementary checks.

**Row count monitoring:** Compare today's count against 30-day mean +/- 3 standard deviations.

**Column distribution drift:** Compare last 7 days against 60-day baseline. Flag shifts >15 percentage points.

**Null rate tracking:** Fail if null rate exceeds threshold (e.g., >5% emails null, >10% addresses null).

```sql
-- tests/assert_order_count_within_range.sql
with daily_counts as (
    select order_date, count(*) as order_count
    from {{ ref('fct_orders') }}
    where order_date >= current_date - 30
    group by order_date
),
stats as (
    select avg(order_count) as avg_count, stddev(order_count) as stddev_count
    from daily_counts
)
select dc.order_date, dc.order_count
from daily_counts dc cross join stats s
where dc.order_count < s.avg_count - (3 * s.stddev_count)
   or dc.order_count > s.avg_count + (3 * s.stddev_count)
```

## Data Quality Pillars

| Pillar | Measurement | Example |
|--------|-------------|---------|
| Completeness | `1 - (null_count / total_count)` | email 98% populated |
| Accuracy | Format/range validation | order_total > 0 |
| Timeliness | `now() - max(loaded_at)` | data < 2 hours old |
| Consistency | Cross-source reconciliation | Stripe revenue = Shopify revenue |

Build a `fct_data_quality_scores` model tracking these pillars per model per day. Use `dbt_utils.generate_surrogate_key` for the primary key. Define an exposure linking to a quality dashboard.

## Alerting

| Severity | Condition | Channel | Response |
|----------|-----------|---------|----------|
| P1 | Mart data missing/incorrect | PagerDuty | 15 min |
| P2 | Source freshness error | Slack #data-alerts | 1 hour |
| P3 | Test warning threshold | Slack #data-notifications | Next business day |
| P4 | Schema change detected | Log only | Weekly review |

Tag models with `meta.owner` and `meta.severity` for alert routing. Configure Elementary Slack webhook or custom Python script for notifications.

**Reduce alert fatigue:** severity thresholds, deduplication by model per run, snooze for known issues, daily digest for P3/P4, ownership-based routing.

## Lineage & Impact Analysis

```bash
dbt ls --select +fct_orders               # all upstream ancestors
dbt ls --select fct_orders+               # all downstream descendants
dbt ls --select model+ --resource-type exposure  # affected dashboards
```

Define exposures for dashboards and ML models with `type`, `maturity`, `owner`, `depends_on`, `url`. Always check downstream impact before modifying any model.

## Incident Response

1. **Detect:** Alert from test failure, freshness error, anomaly, or stakeholder report
2. **Triage:** Assess severity. `dbt ls --select result:error --state target/`
3. **Communicate:** Notify stakeholders with impact, ETA, workaround
4. **Fix:** `dbt retry` (failed only), `dbt build --select result:error+ --state target/` (failed + downstream), `--full-refresh` if corrupted
5. **Verify:** Re-run tests, check freshness, generate Elementary report
6. **Post-mortem:** Document timeline, root cause, impact, prevention actions

## Three-Tier Adoption Path

| Tier | When | Implement |
|------|------|-----------|
| Essential | Day 1 | Source freshness, PK tests, model contracts on marts |
| Mature | Running in prod | Elementary, Slack alerts, anomaly tests, exposures |
| Enterprise | Multiple teams | PagerDuty, SLAs per model tier, quality scoring dashboard, incident triage automation |
