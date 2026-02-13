# Data Quality & Observability

> **Part of:** [dbt-skill](../SKILL.md)
> **Purpose:** Source freshness monitoring, anomaly detection, alerting, lineage analysis, and incident response for dbt projects

For basic testing and source configuration, see the [main skill file](../SKILL.md#basic-testing-overview).

---

## Table of Contents

1. [Source Freshness](#source-freshness)
2. [Elementary Package](#elementary-package)
3. [Anomaly Detection Patterns](#anomaly-detection-patterns)
4. [Data Quality Metrics](#data-quality-metrics)
5. [Alerting](#alerting)
6. [Lineage & Impact Analysis](#lineage--impact-analysis)
7. [Incident Response](#incident-response)
8. [Three-Tier Adoption Path](#three-tier-adoption-path)

---

## Source Freshness

Configure `loaded_at_field` and threshold values in sources YAML, then run `dbt source freshness` to check.

### loaded_at_field by Platform

| Ingestion Tool | loaded_at_field | Notes |
|----------------|----------------|-------|
| Fivetran | `_fivetran_synced` | Added automatically to every table |
| Airbyte | `_airbyte_extracted_at` | Available in raw tables |
| Stitch | `_sdc_batched_at` | Stitch metadata column |
| BigQuery native | `_PARTITIONTIME` | Pseudo-column on ingestion-time partitioned tables |
| Custom pipeline | `loaded_at` / `updated_at` | Define in your ETL process |

### Complete Source Freshness Example

```yaml
# _shopify__sources.yml
version: 2

sources:
  - name: shopify
    description: "Shopify e-commerce data loaded by Fivetran"
    database: raw
    schema: shopify
    loader: fivetran
    loaded_at_field: _fivetran_synced      # timestamp column to check
    freshness:
      warn_after: {count: 12, period: hour}  # yellow alert
      error_after: {count: 24, period: hour} # red alert
    tables:
      - name: orders
        columns:
          - name: id
            data_tests: [unique, not_null]
      - name: customers
        freshness:                           # override source-level thresholds
          warn_after: {count: 24, period: hour}
          error_after: {count: 48, period: hour}
      - name: order_events
        loaded_at_field: event_timestamp     # override source-level field
        freshness:
          warn_after: {count: 1, period: hour}
          error_after: {count: 3, period: hour}
```

**BigQuery with `_PARTITIONTIME`:**

```yaml
sources:
  - name: ga4
    database: "{{ var('gcp_project') }}"
    schema: analytics_123456789
    loaded_at_field: _PARTITIONTIME          # BigQuery pseudo-column
    freshness:
      warn_after: {count: 26, period: hour}
      error_after: {count: 50, period: hour}
```

### Running Freshness Checks

```bash
dbt source freshness                           # check all sources
dbt source freshness --select source:shopify   # check single source
dbt source freshness --output json > target/sources.json  # JSON for automation
```

**Example output:**

```
Running freshness check on source shopify.orders ...
  max_loaded_at = 2026-02-12 08:15:22+00:00
  snapshotted_at = 2026-02-12 09:00:00+00:00
  age = 0:44:38     status = PASS

Running freshness check on source shopify.customers ...
  max_loaded_at = 2026-02-11 02:30:00+00:00
  age = 30:30:00     status = WARN
```

### Scheduling Freshness in CI/CD

```yaml
# .github/workflows/source-freshness.yml
name: Source Freshness Check
on:
  schedule:
    - cron: '0 */2 * * *'                     # every 2 hours
jobs:
  freshness:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with: { python-version: '3.11' }
      - run: pip install dbt-snowflake         # or dbt-bigquery
      - run: dbt deps && dbt source freshness
        env: { DBT_PROFILES_DIR: ./ci_profiles }
```

---

## Elementary Package

[Elementary](https://www.elementary-data.com/) adds anomaly detection, schema monitoring, and observability reporting directly inside your warehouse.

### Installation and Configuration

```yaml
# packages.yml
packages:
  - package: elementary-data/elementary
    version: "0.16.1"                          # pin to specific version
```

```yaml
# dbt_project.yml
models:
  elementary:
    +schema: elementary                        # isolate in own schema
    +materialized: table
```

```bash
dbt deps && dbt run --select elementary        # install and create models
```

### Anomaly Tests

```yaml
# _finance__models.yml
models:
  - name: fct_orders
    config:
      tags: ['finance', 'daily']
    columns:
      - name: order_id
        data_tests:
          - unique
          - not_null
          - elementary.volume_anomalies:       # row count anomaly detection
              timestamp_column: order_date
              where: "order_date >= current_date - 90"
              time_bucket: {period: day, count: 1}
              sensitivity: 3                   # standard deviations
      - name: order_date
        data_tests:
          - elementary.freshness_anomalies:    # data arrival delay detection
              timestamp_column: order_date
              sensitivity: 3
      - name: order_id
        data_tests:
          - elementary.schema_changes:         # column add/remove/type change
              tags: ['schema_monitor']
```

### Report and Slack Integration

```bash
dbt run-operation elementary.generate_report   # HTML report at target/elementary_report.html
dbt run-operation elementary.send_slack_report  # send alerts to Slack
```

```yaml
# dbt_project.yml — Slack webhook config
vars:
  elementary:
    slack_webhook: "{{ env_var('ELEMENTARY_SLACK_WEBHOOK') }}"
    slack_channel_name: "#data-alerts"
    slack_group_alerts_by: "table"
```

**Setup sequence:** install package, run elementary models, add anomaly tests to YAML, run `dbt test`, generate report, configure Slack, send first alert.

---

## Anomaly Detection Patterns

Use these DIY patterns when Elementary is unavailable, or as supplementary checks.

### Row Count Monitoring Macro

```sql
-- macros/test_row_count_anomaly.sql
{% macro test_row_count_anomaly(model, timestamp_column, lookback_days=30, sensitivity=3) %}
with daily_counts as (
    select
        date_trunc('day', {{ timestamp_column }}) as check_date,
        count(*) as row_count
    from {{ model }}
    where {{ timestamp_column }} >= current_date - {{ lookback_days }}
    group by 1
),
stats as (
    select avg(row_count) as avg_count, stddev(row_count) as stddev_count
    from daily_counts
    where check_date < current_date            -- exclude today (partial)
),
today as (
    select check_date, row_count
    from daily_counts where check_date = current_date
)
select t.check_date, t.row_count, s.avg_count,
    s.avg_count - ({{ sensitivity }} * s.stddev_count) as lower_bound,
    s.avg_count + ({{ sensitivity }} * s.stddev_count) as upper_bound
from today t cross join stats s
where t.row_count < s.avg_count - ({{ sensitivity }} * s.stddev_count)
   or t.row_count > s.avg_count + ({{ sensitivity }} * s.stddev_count)
{% endmacro %}
```

### Order Count Anomaly (Singular Test)

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

### Column Distribution Drift

```sql
-- tests/assert_payment_method_distribution.sql
with current_dist as (
    select payment_method,
        count(*) * 1.0 / sum(count(*)) over() as current_pct
    from {{ ref('fct_orders') }}
    where order_date >= current_date - 7
    group by payment_method
),
baseline_dist as (
    select payment_method,
        count(*) * 1.0 / sum(count(*)) over() as baseline_pct
    from {{ ref('fct_orders') }}
    where order_date between current_date - 60 and current_date - 8
    group by payment_method
)
-- fail if any method share shifted >15 percentage points
select c.payment_method,
    round(c.current_pct * 100, 1) as current_pct,
    round(b.baseline_pct * 100, 1) as baseline_pct
from current_dist c
left join baseline_dist b on c.payment_method = b.payment_method
where abs(c.current_pct - coalesce(b.baseline_pct, 0)) > 0.15
```

### Null Rate Tracking

```sql
-- tests/assert_null_rate_within_threshold.sql
with null_rates as (
    select
        count(*) as total_rows,
        sum(case when customer_email is null then 1 else 0 end) as null_email,
        sum(case when shipping_address is null then 1 else 0 end) as null_address
    from {{ ref('fct_orders') }}
    where order_date >= current_date - 7
)
select *
from null_rates
where null_email * 1.0 / total_rows > 0.05    -- fail if >5% emails null
   or null_address * 1.0 / total_rows > 0.10  -- fail if >10% addresses null
```

---

## Data Quality Metrics

### The Four Pillars

| Pillar | Definition | Measurement | Example |
|--------|-----------|-------------|---------|
| **Completeness** | Non-null values in required fields | `1 - (null_count / total_count)` | `customer_email` 98% populated |
| **Accuracy** | Values match expected formats/ranges | Format validation, range checks | `order_total > 0` |
| **Timeliness** | Data arrives within SLA windows | `now() - max(loaded_at)` | Orders data < 2 hours old |
| **Consistency** | Cross-source agreement | Sum reconciliation, row counts | Stripe revenue = Shopify revenue |

### Quality Scores Model

```sql
-- models/marts/observability/fct_data_quality_scores.sql
{{ config(materialized='incremental', unique_key='quality_check_id') }}

with completeness_checks as (
    select
        current_date as check_date,
        'fct_orders' as model_name,
        'completeness' as pillar,
        'customer_email' as column_name,
        count(*) as total_rows,
        count(customer_email) as passing_rows,
        round(count(customer_email) * 100.0 / nullif(count(*), 0), 2) as score
    from {{ ref('fct_orders') }}
    where order_date >= current_date - 1
),
accuracy_checks as (
    select
        current_date as check_date,
        'fct_orders' as model_name,
        'accuracy' as pillar,
        'total_amount' as column_name,
        count(*) as total_rows,
        sum(case when total_amount > 0 then 1 else 0 end) as passing_rows,
        round(sum(case when total_amount > 0 then 1 else 0 end) * 100.0
            / nullif(count(*), 0), 2) as score
    from {{ ref('fct_orders') }}
    where order_date >= current_date - 1
),
timeliness_checks as (
    select
        current_date as check_date,
        'fct_orders' as model_name,
        'timeliness' as pillar,
        'order_date' as column_name,
        count(*) as total_rows,
        count(*) as passing_rows,
        case when max(order_date) >= current_date - 1 then 100.0 else 0.0 end as score
    from {{ ref('fct_orders') }}
),
all_checks as (
    select * from completeness_checks union all
    select * from accuracy_checks union all
    select * from timeliness_checks
)
select
    {{ dbt_utils.generate_surrogate_key(['check_date','model_name','pillar','column_name']) }}
        as quality_check_id,
    check_date, model_name, pillar, column_name, total_rows, passing_rows, score
from all_checks
{% if is_incremental() %}
where check_date > (select max(check_date) from {{ this }})
{% endif %}
```

### Exposure for Quality Dashboard

```yaml
exposures:
  - name: data_quality_dashboard
    type: dashboard
    maturity: high
    owner: {name: Data Engineering, email: data-eng@company.com}
    depends_on:
      - ref('fct_data_quality_scores')
    url: https://looker.company.com/dashboards/data-quality
    description: "Tracks quality scores across all mart models for daily monitoring and SLA reporting."
```

---

## Alerting

### Severity Matrix

| Severity | Condition | Channel | Response Time |
|----------|-----------|---------|---------------|
| **P1** | Mart data missing or incorrect | PagerDuty | 15 min |
| **P2** | Source freshness error threshold | Slack `#data-alerts` | 1 hour |
| **P3** | Test warning threshold | Slack `#data-notifications` | Next business day |
| **P4** | Schema change detected | Log only | Weekly review |

### dbt Cloud Webhooks

Configure in dbt Cloud: **Account Settings > Webhooks > Create Webhook**. Payload includes job name, run ID, status, failed models/tests, and run URL.

### Slack Alert Script

```python
# scripts/dbt_slack_alert.py
import requests, os

SLACK_WEBHOOK = os.environ["SLACK_WEBHOOK_URL"]
CHANNELS = {"p1": "#data-incidents", "p2": "#data-alerts", "p3": "#data-notifications"}
COLORS = {"p1": "#FF0000", "p2": "#FFA500", "p3": "#FFFF00"}

def send_alert(severity, model_name, error_message, run_url):
    requests.post(SLACK_WEBHOOK, json={
        "channel": CHANNELS.get(severity, "#data-notifications"),
        "attachments": [{
            "color": COLORS.get(severity, "#808080"),
            "title": f"[{severity.upper()}] dbt failure: {model_name}",
            "text": error_message,
            "fields": [
                {"title": "Model", "value": model_name, "short": True},
                {"title": "Severity", "value": severity.upper(), "short": True},
            ],
            "actions": [{"type": "button", "text": "View Run", "url": run_url}]
        }]
    })
```

### PagerDuty for P1 Incidents

```yaml
# .github/workflows/dbt-production.yml (partial)
- name: Alert on P1 failure
  if: failure()
  run: |
    curl -X POST https://events.pagerduty.com/v2/enqueue \
      -H 'Content-Type: application/json' \
      -d '{
        "routing_key": "${{ secrets.PAGERDUTY_ROUTING_KEY }}",
        "event_action": "trigger",
        "payload": {
          "summary": "dbt production build failed - mart data may be stale",
          "severity": "critical",
          "source": "dbt-ci",
          "component": "data-pipeline"
        }
      }'
```

### Alert Fatigue Tuning

| Technique | Implementation | Effect |
|-----------|---------------|--------|
| **Severity thresholds** | `warn_after` before `error_after` | Fewer false-positive pages |
| **Deduplication** | Group alerts by model per run | No alert storms |
| **Snooze rules** | Suppress known issues 24-48 hours | Time for planned fixes |
| **Batch notifications** | Daily digest for P3/P4 | Reduced notification volume |
| **Ownership routing** | Tag with `meta.owner`, route per team | No cross-team noise |

```yaml
models:
  - name: fct_orders
    meta:
      owner: "finance-analytics"               # route alerts to owning team
      severity: "p1"
    config:
      tags: ['finance', 'p1']
```

---

## Lineage & Impact Analysis

### Generate and View the DAG

```bash
dbt docs generate                              # build lineage graph
dbt docs serve --port 8080                     # serve interactive DAG
```

### Ancestor and Descendant Queries

```bash
dbt ls --select +fct_orders                    # all upstream ancestors
dbt ls --select fct_orders+                    # all downstream descendants
dbt ls --select +fct_orders+                   # both directions
```

### Exposure Definitions

```yaml
# models/marts/finance/_finance__exposures.yml
version: 2

exposures:
  - name: weekly_revenue_dashboard
    type: dashboard
    maturity: high
    owner: {name: Analytics Team, email: analytics@company.com}
    depends_on:
      - ref('fct_orders')
      - ref('dim_customers')
    url: https://looker.company.com/dashboards/123
    description: "Weekly revenue reporting for the executive team. Refreshes Mondays 6am UTC."

  - name: customer_segmentation_model
    type: ml
    maturity: medium
    owner: {name: Data Science, email: data-science@company.com}
    depends_on:
      - ref('fct_orders')
      - ref('dim_customers')
      - ref('fct_web_sessions')
    description: "Customer segmentation for targeted marketing. Retrained weekly on 90 days of data."
```

### Impact Analysis Workflow

Before changing any model, check downstream dependencies:

```bash
# 1. List downstream models
dbt ls --select stg_shopify__orders+

# 2. List affected dashboards and ML models
dbt ls --select stg_shopify__orders+ --resource-type exposure

# 3. Dry-run build of all affected nodes
dbt build --select stg_shopify__orders+ --defer --state prod-artifacts/
```

**DO:** Check `dbt ls --select model+ --resource-type exposure` before modifying any model, then notify owners listed in exposure YAML.

**DON'T:** Push column renames or logic changes without checking downstream impact first.

---

## Incident Response

### Runbook: Six Steps

**1. Detect** -- Alert fires from: dbt test failure, source freshness error, Elementary anomaly, or stakeholder report.

**2. Triage** -- Assess severity using the [matrix above](#severity-matrix).

```bash
dbt ls --select result:error --state target/   # what failed in last run
dbt source freshness --select source:shopify   # freshness status
```

**3. Communicate** -- Notify stakeholders immediately for P1/P2:

```
Subject: [P{n}] Data Incident - {model_name}
Status: Investigating
Impact: {affected data and dashboards}
Affected dashboards: {from dbt ls --select model+ --resource-type exposure}
ETA: {estimated resolution time}
Workaround: {e.g., "use yesterday's snapshot"}
Updates: every {30 min for P1 | 2 hours for P2}
```

**4. Fix** -- Common remediation:

```bash
dbt build --select +fct_orders                 # re-run model + ancestors
dbt run --select fct_orders --full-refresh     # full refresh if corrupted
dbt retry                                      # re-run only failed models
dbt build --select result:error+ --state target/  # failed + downstream
```

**5. Verify** -- Confirm the fix:

```bash
dbt build --select +fct_orders+ --resource-type test
dbt source freshness
dbt run-operation elementary.generate_report
```

**6. Post-mortem** -- Document the incident:

```markdown
# Post-Mortem: {title}
**Date:** YYYY-MM-DD | **Severity:** P{n} | **Duration:** {time}

## Timeline
- HH:MM Alert fired | HH:MM Acknowledged | HH:MM Root cause found | HH:MM Fixed | HH:MM Verified

## Root Cause
{Technical explanation}

## Impact
Models: {list} | Dashboards: {list} | Data gap: {time range}

## Prevention
| Action | Owner | Due Date |
|--------|-------|----------|
| {measure} | {name} | YYYY-MM-DD |
```

### Recovery Commands Reference

| Scenario | Command |
|----------|---------|
| Re-run failed only | `dbt retry` |
| Failed + downstream | `dbt build --select result:error+ --state target/` |
| Full refresh corrupted | `dbt run --select model_name --full-refresh` |
| Rebuild DAG branch | `dbt build --select +model_name+` |
| Validate after fix | `dbt test --select +model_name` |
| Check freshness | `dbt source freshness` |

---

## Three-Tier Adoption Path

| Tier | Label | What to Implement | When |
|------|-------|-------------------|------|
| 1 | **Essential** | Source freshness, model contracts, basic YAML tests | Day 1 |
| 2 | **Mature** | Elementary, Slack alerts, anomaly detection, custom tests | Running in prod |
| 3 | **Enterprise** | Full observability platform, PagerDuty, SLAs, data quality scores | Multiple teams |

### Tier 1: Essential (Day 1)

Implement on every dbt project from the start.

```yaml
# Source freshness on all sources
sources:
  - name: shopify
    loaded_at_field: _fivetran_synced
    freshness:
      warn_after: {count: 12, period: hour}
      error_after: {count: 24, period: hour}
    tables: [orders, customers]

---
# Primary key tests on every model
models:
  - name: fct_orders
    columns:
      - name: order_id
        data_tests: [unique, not_null]

---
# Model contracts on marts (dbt 1.5+)
models:
  - name: fct_orders
    config:
      contract: {enforced: true}
    columns:
      - name: order_id
        data_type: string
        data_tests: [unique, not_null]
      - name: total_amount
        data_type: float
        data_tests: [not_null]
```

Run freshness in CI: `dbt source freshness && dbt build`

### Tier 2: Mature (Running in Production)

Add once the project actively serves stakeholders.

- Install Elementary (`elementary-data/elementary`, pin version)
- Add `volume_anomalies` and `freshness_anomalies` tests on critical models
- Configure Slack webhook for Elementary alerts
- Write custom anomaly tests for business-critical metrics (revenue, order counts)
- Define exposures for all dashboards and ML models

```sql
-- tests/assert_daily_revenue_within_range.sql
with daily_revenue as (
    select order_date, sum(total_amount) as revenue
    from {{ ref('fct_orders') }}
    where order_date >= current_date - 30
    group by order_date
),
stats as (
    select avg(revenue) as avg_rev, stddev(revenue) as std_rev
    from daily_revenue where order_date < current_date
)
select dr.order_date, dr.revenue
from daily_revenue dr cross join stats s
where dr.revenue < s.avg_rev - (3 * s.std_rev)
   or dr.revenue > s.avg_rev + (3 * s.std_rev)
```

### Tier 3: Enterprise (Multiple Teams)

Implement when scaling to multiple data teams with strict SLAs.

- Schedule Elementary report after every production run
- Configure PagerDuty for P1 incidents (see [PagerDuty section](#pagerduty-for-p1-incidents))
- Define SLA metadata per model tier:

```yaml
# dbt_project.yml
models:
  my_project:
    marts:
      finance:
        +meta: {sla: "data by 06:00 UTC", owner: finance-analytics, tier: p1}
      marketing:
        +meta: {sla: "data by 09:00 UTC", owner: marketing-analytics, tier: p2}
```

- Build quality scoring dashboard on `fct_data_quality_scores`
- Automate incident triage script:

```bash
#!/usr/bin/env bash
# scripts/incident-triage.sh
set -euo pipefail
echo "=== Failed models ==="
dbt ls --select result:error --state target/ 2>/dev/null || echo "No failures"
echo "=== Source freshness ==="
dbt source freshness 2>/dev/null || echo "Freshness check failed"
echo "=== Downstream impact ==="
for model in $(dbt ls --select result:error --state target/ 2>/dev/null); do
    echo "--- $model ---"
    dbt ls --select "${model}+" --resource-type exposure 2>/dev/null || echo "  None"
done
```

### Adoption Checklist

| Tier | Item |
|------|------|
| 1 | Source freshness configured for all sources |
| 1 | Primary key tests on every model |
| 1 | Model contracts on mart models |
| 1 | Freshness check in CI pipeline |
| 2 | Elementary installed and configured |
| 2 | Volume + freshness anomaly tests on critical models |
| 2 | Slack alerts configured |
| 2 | Exposures defined for all dashboards |
| 2 | Custom anomaly tests for key business metrics |
| 3 | PagerDuty integration for P1 |
| 3 | SLA definitions per model tier |
| 3 | Data quality scoring model + dashboard |
| 3 | Automated incident triage script |
| 3 | Post-mortem process documented |

---

**Back to:** [Main Skill File](../SKILL.md)
