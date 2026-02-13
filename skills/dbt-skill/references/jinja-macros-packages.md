# Jinja, Macros & Packages

> **Part of:** [dbt-skill](../SKILL.md)
> **Purpose:** Jinja templating fundamentals, custom macro development, essential package ecosystem, warehouse-adaptive patterns, and debugging workflows

This document provides detailed guidance on Jinja in dbt, writing and organizing macros, leveraging the package ecosystem, and debugging compiled SQL. For project structure and modeling methodology, see the [main skill file](../SKILL.md).

---

## Table of Contents

1. [Jinja Fundamentals](#jinja-fundamentals)
2. [Control Flow Patterns](#control-flow-patterns)
3. [Writing Custom Macros](#writing-custom-macros)
4. [Macro Organization](#macro-organization)
5. [Essential Packages](#essential-packages)
6. [Package Management](#package-management)
7. [Common Macro Patterns](#common-macro-patterns)
8. [Debugging Jinja](#debugging-jinja)

---

## Jinja Fundamentals

### Three Tag Types

| Tag | Syntax | Purpose | Compiles to SQL? |
|-----|--------|---------|-----------------|
| Expression | `{{ }}` | Output a value | Yes |
| Statement | `{% %}` | Control flow, variable assignment | No (controls what SQL is generated) |
| Comment | `{# #}` | Documentation, notes | No (stripped entirely) |

### Expression Tags — `{{ }}`

Output values into compiled SQL. Use for references, variables, and macro calls.

```sql
-- References
select * from {{ ref('stg_shopify__orders') }}
select * from {{ source('stripe', 'payments') }}

-- Variables
where order_date >= '{{ var("start_date") }}'

-- Config
{{ config(materialized='incremental', unique_key='order_id') }}

-- Environment variables
{% set api_schema = env_var('DBT_STRIPE_SCHEMA', 'stripe') %}
```

### Statement Tags — `{% %}`

Control what SQL gets generated. Never appear in compiled output.

```sql
{% set payment_methods = ['credit_card', 'bank_transfer', 'gift_card'] %}

{% if is_incremental() %}
    where updated_at > (select max(updated_at) from {{ this }})
{% endif %}

{% for method in payment_methods %}
    sum(case when payment_method = '{{ method }}' then amount_dollars else 0 end) as {{ method }}_amount
    {%- if not loop.last %},{% endif %}
{% endfor %}
```

### Comment Tags — `{# #}`

Stripped during compilation. Use for Jinja-level documentation.

```sql
{# This comment will NOT appear in compiled SQL #}
-- This SQL comment WILL appear in compiled SQL

{# TODO: Replace with macro once dbt-utils supports this natively #}
```

### Whitespace Control

Add a hyphen inside tags to strip whitespace on that side.

```sql
-- Without whitespace control (produces extra blank lines)
{% if is_incremental() %}
    where updated_at > (select max(updated_at) from {{ this }})
{% endif %}

-- With whitespace control (clean output)
{%- if is_incremental() %}
    where updated_at > (select max(updated_at) from {{ this }})
{%- endif %}
```

| Syntax | Effect |
|--------|--------|
| `{%- ... %}` | Strip whitespace before the tag |
| `{% ... -%}` | Strip whitespace after the tag |
| `{%- ... -%}` | Strip whitespace on both sides |

### dbt-Specific Context Objects

| Object | Purpose | Example |
|--------|---------|---------|
| `ref()` | Reference another model | `{{ ref('stg_stripe__payments') }}` |
| `source()` | Reference a source table | `{{ source('shopify', 'orders') }}` |
| `config()` | Set model configuration | `{{ config(materialized='table') }}` |
| `var()` | Access project variables | `{{ var('start_date', '2020-01-01') }}` |
| `env_var()` | Read environment variables | `{{ env_var('DBT_TARGET', 'dev') }}` |
| `this` | Current model relation | `{{ this }}` (in incremental models) |
| `target` | Connection target info | `{{ target.name }}`, `{{ target.type }}` |
| `is_incremental()` | Check if running incrementally | `{% if is_incremental() %}` |

### Complete Example — All Three Tag Types

```sql
{# fct_orders.sql — Combines order and payment data into a single fact table #}

{{ config(
    materialized='incremental',
    unique_key='order_id',
    on_schema_change='append_new_columns'
) }}

{% set payment_methods = ['credit_card', 'bank_transfer', 'gift_card'] %}

with orders as (
    select * from {{ ref('stg_shopify__orders') }}
    {%- if is_incremental() %}
    where updated_at > (select max(updated_at) from {{ this }})
    {%- endif %}
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
        {% for method in payment_methods %}
        payments.{{ method }}_amount
        {%- if not loop.last %},{% endif %}
        {% endfor %}
    from orders
    left join payments on orders.order_id = payments.order_id
)

select * from final
```

---

## Control Flow Patterns

### Environment-Specific Logic

Use `target.name` to vary behavior across environments.

```sql
{{ config(
    materialized='table',
    pre_hook=[
        "{{ 'alter warehouse analytics_wh set warehouse_size = xlarge' if target.name == 'prod' else '' }}"
    ]
) }}

select *
from {{ ref('stg_shopify__orders') }}
{% if target.name == 'dev' %}
    {# Limit data in dev for faster iteration #}
    where order_date >= dateadd('month', -3, current_date)
{% endif %}
```

### Incremental Filtering

```sql
{{ config(materialized='incremental', unique_key='order_id') }}

select
    order_id,
    customer_id,
    order_date,
    total_amount,
    updated_at

from {{ ref('stg_shopify__orders') }}

{% if is_incremental() %}
    where updated_at > (select max(updated_at) from {{ this }})
{% endif %}
```

### Dynamic Column Generation — Pivot Pattern

Generate pivot columns from a list without repetitive SQL.

```sql
-- int_payments_pivoted.sql
{% set payment_methods = dbt_utils.get_column_values(
    table=ref('stg_stripe__payments'),
    column='payment_method'
) %}

with payments as (
    select * from {{ ref('stg_stripe__payments') }}
),

pivoted as (
    select
        order_id,
        {% for method in payment_methods %}
        sum(case when payment_method = '{{ method }}' then amount_dollars else 0 end) as {{ method }}_amount
        {%- if not loop.last %},{% endif %}
        {% endfor %}
    from payments
    where payment_status = 'completed'
    group by order_id
)

select * from pivoted
```

### Conditional Warehouse-Specific SQL

```sql
-- Generate date truncation that works across warehouses
{% macro trunc_date(date_column, granularity) %}
    {% if target.type == 'snowflake' %}
        date_trunc('{{ granularity }}', {{ date_column }})
    {% elif target.type == 'bigquery' %}
        date_trunc({{ date_column }}, {{ granularity }})
    {% endif %}
{% endmacro %}
```

### Loop Over Metrics to Aggregate

```sql
-- rpt_monthly_revenue.sql
{% set metrics = [
    {'column': 'total_amount', 'agg': 'sum', 'alias': 'total_revenue'},
    {'column': 'order_id', 'agg': 'count', 'alias': 'total_orders'},
    {'column': 'total_amount', 'agg': 'avg', 'alias': 'avg_order_value'},
] %}

select
    date_trunc('month', order_date) as order_month,
    {% for metric in metrics %}
    {{ metric.agg }}({{ metric.column }}) as {{ metric.alias }}
    {%- if not loop.last %},{% endif %}
    {% endfor %}

from {{ ref('fct_orders') }}
group by 1
order by 1
```

### Variable Assignment with `{% set %}`

```sql
{# Simple assignment #}
{% set days_lookback = 90 %}

{# List assignment #}
{% set statuses = ['completed', 'refunded'] %}

{# Query result assignment #}
{% set max_date_query %}
    select max(order_date) from {{ ref('fct_orders') }}
{% endset %}
{% set max_date = run_query(max_date_query).columns[0][0] %}

{# Dictionary assignment #}
{% set warehouse_sizes = {
    'dev': 'xsmall',
    'staging': 'small',
    'prod': 'large'
} %}
```

---

## Writing Custom Macros

### Definition Syntax

```sql
{# macros/utils/safe_divide.sql #}

{% macro safe_divide(numerator, denominator, default=0) %}
    {% if target.type == 'snowflake' %}
        div0({{ numerator }}, {{ denominator }})
    {% elif target.type == 'bigquery' %}
        safe_divide({{ numerator }}, {{ denominator }})
    {% else %}
        case when {{ denominator }} != 0
            then {{ numerator }}::float / {{ denominator }}
            else {{ default }}
        end
    {% endif %}
{% endmacro %}
```

### Return Values

```sql
{# Implicit return — the rendered template is the return value #}
{% macro cents_to_dollars(column_name) %}
    ({{ column_name }} / 100.0)
{% endmacro %}

{# Explicit return — use when computing a value, not generating SQL #}
{% macro get_payment_methods() %}
    {% set methods = ['credit_card', 'bank_transfer', 'gift_card'] %}
    {% do return(methods) %}
{% endmacro %}

{# Usage of explicit return #}
{% set payment_methods = get_payment_methods() %}
{% for method in payment_methods %}
    ...
{% endfor %}
```

### File Location and Naming Convention

```
macros/
├── utils/
│   ├── safe_divide.sql          # Cross-warehouse safe division
│   ├── cents_to_dollars.sql     # Currency conversion helper
│   └── deduplicate.sql          # Row deduplication macro
├── schema/
│   ├── generate_schema_name.sql # Custom schema routing
│   └── generate_alias_name.sql  # Custom table aliasing
├── tests/
│   ├── test_not_negative.sql    # Custom generic test
│   └── test_row_count.sql       # Row count bounds test
├── grants/
│   └── grant_select.sql         # Post-hook grant management
└── logging/
    └── log_model_timing.sql     # Structured debug logging
```

### Calling Macros

**In a model:**
```sql
-- models/marts/fct_orders.sql
select
    order_id,
    {{ cents_to_dollars('amount_cents') }} as amount_dollars,
    {{ safe_divide('discount_amount', 'subtotal_amount') }} as discount_rate
from {{ ref('stg_stripe__payments') }}
```

**From the CLI:**
```bash
# Run a macro directly (useful for operational macros)
dbt run-operation grant_select --args '{"role": "analytics_reader"}'

# Run with named arguments
dbt run-operation log_model_timing --args '{"model_name": "fct_orders"}'
```

### Warehouse-Adaptive Macros

Use `target.type` to emit warehouse-specific SQL from a single macro.

```sql
{# macros/utils/safe_divide.sql #}

{% macro safe_divide(numerator, denominator) %}
    {% if target.type == 'snowflake' %}
        div0({{ numerator }}, {{ denominator }})
    {% elif target.type == 'bigquery' %}
        safe_divide({{ numerator }}, {{ denominator }})
    {% else %}
        case when {{ denominator }} != 0
            then {{ numerator }} / {{ denominator }}
            else 0
        end
    {% endif %}
{% endmacro %}
```

---

## Macro Organization

### Group by Purpose

| Directory | Contents | Examples |
|-----------|----------|----------|
| `macros/utils/` | Reusable SQL helpers | `safe_divide`, `deduplicate`, `cents_to_dollars` |
| `macros/schema/` | Schema/alias overrides | `generate_schema_name`, `generate_alias_name` |
| `macros/tests/` | Custom generic tests | `test_not_negative`, `test_accepted_range` |
| `macros/grants/` | Permission management | `grant_select`, `grant_usage` |
| `macros/logging/` | Debug and observability | `log_model_timing`, `log_row_counts` |
| `macros/staging/` | Staging helpers | `generate_base_model`, `standardize_timestamps` |

### Document Macros

```sql
{# macros/utils/safe_divide.sql #}

{% macro safe_divide(numerator, denominator) %}
    {# Cross-warehouse safe division that returns 0 instead of dividing by zero.
       Works on Snowflake (div0), BigQuery (safe_divide), and generic SQL.

       Args:
           numerator: column or expression for the numerator
           denominator: column or expression for the denominator

       Usage:
           {{ safe_divide('revenue', 'total_orders') }}
    #}
    ...
{% endmacro %}
```

Add corresponding `{% docs %}` blocks for the dbt docs site:

```markdown
{# in macros/utils/safe_divide.sql or a separate docs block file #}

{% docs safe_divide %}
Cross-warehouse safe division macro. Returns 0 when the denominator is zero.

**Supported warehouses:** Snowflake, BigQuery, Postgres

**Arguments:**
- `numerator` — column or expression
- `denominator` — column or expression

**Example:**
```sql
select {{ safe_divide('revenue', 'total_orders') }} as avg_revenue_per_order
```
{% enddocs %}
```

### When to Extract vs Inline

| Reuse Count | Complexity | Action | Rationale |
|-------------|------------|--------|-----------|
| 1 | Low | Inline | Extraction adds indirection for no benefit |
| 1 | High | Extract | Improves readability of the model |
| 2+ | Any | Extract to macro | DRY principle, single source of truth |
| Cross-project | Any | Extract to package | Share via git or hub package |

### Testing Macros with `dbt run-operation`

```bash
# Test a macro that generates SQL
dbt run-operation safe_divide --args '{"numerator": "10", "denominator": "3"}'

# Test a macro that returns a list
dbt run-operation get_payment_methods

# Test with --target to verify warehouse-specific branches
dbt run-operation safe_divide --args '{"numerator": "10", "denominator": "0"}' --target prod
```

---

## Essential Packages

### Package Overview

| Package | Category | Purpose | Install Priority |
|---------|----------|---------|-----------------|
| `dbt-utils` | Must-have | Cross-database helpers, surrogate keys, pivot, unpivot | First |
| `dbt-expectations` | Must-have | Great Expectations-style data tests | First |
| `codegen` | Development | Generate YAML, base models from sources | Dev only |
| `dbt-date` | Situational | Date spine, fiscal calendars | When needed |
| `audit-helper` | Situational | Compare model versions during refactoring | When needed |
| `dbt-project-evaluator` | Recommended | Lint dbt project structure and naming | CI |
| `elementary` | Recommended | Data observability, anomaly detection | Production |

---

### dbt-utils (Must-Have)

**Install:**
```yaml
# packages.yml
packages:
  - package: dbt-labs/dbt_utils
    version: [">=1.3.0", "<2.0.0"]
```

**Compatibility:** Snowflake, BigQuery, Postgres, Redshift, Databricks, Spark

**Top features:**

**1. Surrogate keys:**
```sql
-- Generate a deterministic surrogate key from multiple columns
select
    {{ dbt_utils.generate_surrogate_key(['order_id', 'payment_id']) }} as unique_key,
    order_id,
    payment_id,
    amount_dollars
from {{ ref('stg_stripe__payments') }}
```

**2. Pivot / Unpivot:**
```sql
-- Pivot payment methods into columns
select
    order_id,
    {{ dbt_utils.pivot(
        'payment_method',
        dbt_utils.get_column_values(ref('stg_stripe__payments'), 'payment_method'),
        agg='sum',
        then_value='amount_dollars',
        else_value='0'
    ) }}
from {{ ref('stg_stripe__payments') }}
group by order_id
```

**3. Date spine:**
```sql
-- Generate a continuous date range (fill gaps in event data)
{{ dbt_utils.date_spine(
    datepart="day",
    start_date="cast('2020-01-01' as date)",
    end_date="current_date"
) }}
```

---

### dbt-expectations (Must-Have)

**Install:**
```yaml
# packages.yml
packages:
  - package: calogica/dbt_expectations
    version: [">=0.10.0", "<0.11.0"]
```

**Compatibility:** Snowflake, BigQuery, Postgres, Redshift

**Top features:**

**1. Column value ranges:**
```yaml
# _finance__models.yml
models:
  - name: fct_orders
    columns:
      - name: total_amount
        data_tests:
          - dbt_expectations.expect_column_values_to_be_between:
              min_value: 0
              max_value: 100000
              row_condition: "order_status != 'cancelled'"
```

**2. Row count validation:**
```yaml
models:
  - name: fct_orders
    data_tests:
      - dbt_expectations.expect_table_row_count_to_be_between:
          min_value: 1000
          warn_if: "<5000"
          error_if: "<1000"
```

**3. Distribution tests:**
```yaml
columns:
  - name: order_status
    data_tests:
      - dbt_expectations.expect_column_distinct_count_to_be_between:
          min_value: 3
          max_value: 6
```

---

### codegen (Dev Only)

**Install:**
```yaml
# packages.yml
packages:
  - package: dbt-labs/codegen
    version: [">=0.12.0", "<0.13.0"]
```

**Compatibility:** Snowflake, BigQuery, Postgres, Redshift

**Top features:**

**1. Generate base model SQL:**
```bash
dbt run-operation codegen.generate_base_model --args '{"source_name": "stripe", "table_name": "payments"}'
```

**2. Generate model YAML:**
```bash
dbt run-operation codegen.generate_model_yaml --args '{"model_names": ["stg_stripe__payments"]}'
```

**3. Generate source YAML:**
```bash
dbt run-operation codegen.generate_source --args '{"schema_name": "stripe", "database_name": "raw"}'
```

---

### dbt-date (Situational)

**Install:**
```yaml
# packages.yml
packages:
  - package: calogica/dbt_date
    version: [">=0.10.0", "<0.11.0"]
```

**Compatibility:** Snowflake, BigQuery, Postgres, Redshift

**Top features:**

**1. Date spine with fiscal support:**
```sql
select * from {{ dbt_date.get_date_dimension("2020-01-01", "2025-12-31") }}
```

**2. Date part helpers:**
```sql
select
    order_date,
    {{ dbt_date.day_name('order_date', short=true) }} as day_of_week,
    {{ dbt_date.last_day('order_date', 'month') }} as month_end
from {{ ref('fct_orders') }}
```

**3. Relative date ranges:**
```sql
where order_date >= {{ dbt_date.n_days_ago(30) }}
```

---

### audit-helper (Situational)

**Install:**
```yaml
# packages.yml
packages:
  - package: dbt-labs/audit_helper
    version: [">=0.12.0", "<0.13.0"]
```

**Compatibility:** Snowflake, BigQuery, Postgres, Redshift

**Top features:**

**1. Compare model versions during refactoring:**
```sql
-- analyses/compare_orders_refactor.sql
{% set old_relation = ref('fct_orders_v1') %}
{% set new_relation = ref('fct_orders_v2') %}

{{ audit_helper.compare_relations(
    a_relation=old_relation,
    b_relation=new_relation,
    primary_key="order_id"
) }}
```

**2. Compare column values:**
```sql
{{ audit_helper.compare_column_values(
    a_relation=ref('fct_orders_v1'),
    b_relation=ref('fct_orders_v2'),
    primary_key="order_id",
    column_to_compare="total_amount"
) }}
```

**3. Compare row counts:**
```sql
{{ audit_helper.compare_row_counts(
    a_relation=ref('fct_orders_v1'),
    b_relation=ref('fct_orders_v2')
) }}
```

---

### dbt-project-evaluator (Recommended)

**Install:**
```yaml
# packages.yml
packages:
  - package: dbt-labs/dbt_project_evaluator
    version: [">=0.8.0", "<0.9.0"]
```

**Compatibility:** Snowflake, BigQuery, Postgres, Redshift, Databricks

**Top features:**

**1. Detect DAG violations (marts referencing staging directly):**
```bash
dbt build --select package:dbt_project_evaluator
```

**2. Naming convention enforcement:**
- Flags models not following `stg_`, `int_`, `fct_`, `dim_` conventions
- Detects missing primary key tests

**3. CI integration:**
```yaml
# Run in CI to enforce project standards
- name: Evaluate project structure
  run: dbt build --select package:dbt_project_evaluator --target ci
```

---

### elementary (Recommended)

**Install:**
```yaml
# packages.yml
packages:
  - package: elementary-data/elementary
    version: [">=0.16.0", "<0.17.0"]
```

**Compatibility:** Snowflake, BigQuery, Postgres, Redshift, Databricks

**Top features:**

**1. Anomaly detection tests:**
```yaml
models:
  - name: fct_orders
    data_tests:
      - elementary.volume_anomalies:
          timestamp_column: order_date
          where: "order_status != 'cancelled'"
      - elementary.freshness_anomalies:
          timestamp_column: updated_at
```

**2. Column-level monitoring:**
```yaml
columns:
  - name: total_amount
    data_tests:
      - elementary.column_anomalies:
          timestamp_column: order_date
          column_anomalies:
            - zero_count
            - null_count
            - average
```

**3. Observability report:**
```bash
# Generate HTML report of data quality
edr report
```

---

## Package Management

### packages.yml Syntax

```yaml
# packages.yml — Three installation methods

packages:
  # 1. Hub packages (recommended for public packages)
  - package: dbt-labs/dbt_utils
    version: [">=1.3.0", "<2.0.0"]

  # 2. Git packages (for private or forked packages)
  - git: "https://github.com/your-org/dbt-internal-utils.git"
    revision: v0.3.0  # Tag, branch, or commit SHA

  # 3. Local packages (for monorepo or co-located packages)
  - local: ../dbt-shared-macros
```

### Version Pinning Strategies

| Strategy | Syntax | Use Case |
|----------|--------|----------|
| Exact | `version: "1.3.0"` | Maximum stability, manual updates only |
| Range (recommended) | `version: [">=1.3.0", "<2.0.0"]` | Accept patches and minors, block breaking changes |
| Pessimistic | `version: [">=1.3.0", "<1.4.0"]` | Accept patches only |
| Latest | (no version) | Never use in production |

```yaml
# DO: Pin with a range to accept patches
packages:
  - package: dbt-labs/dbt_utils
    version: [">=1.3.0", "<2.0.0"]

# DON'T: Leave version unpinned
packages:
  - package: dbt-labs/dbt_utils
    # No version — will pull latest on every dbt deps run
```

### `dbt deps` — When and What

| When to Run | What It Does |
|-------------|-------------|
| After cloning a repo | Installs all packages to `dbt_packages/` |
| After editing `packages.yml` | Installs new or updated packages |
| After pulling changes with `packages.yml` updates | Syncs local packages |
| In CI pipeline (every run) | Ensures consistent package state |

```bash
# Install packages
dbt deps

# Packages installed to dbt_packages/ (add to .gitignore)
echo "dbt_packages/" >> .gitignore
```

### Lock File Considerations

dbt generates `package-lock.yml` to pin exact resolved versions.

```yaml
# Commit package-lock.yml for reproducible builds
# dbt deps reads lock file when present, skipping resolution
```

| File | Commit? | Purpose |
|------|---------|---------|
| `packages.yml` | Yes | Declares version ranges |
| `package-lock.yml` | Yes | Locks exact resolved versions |
| `dbt_packages/` | No (.gitignore) | Installed package files |

### Private Packages via Git

**SSH authentication:**
```yaml
packages:
  - git: "git@github.com:your-org/dbt-internal-utils.git"
    revision: v0.3.0
```

**Token authentication (CI/CD):**
```yaml
packages:
  - git: "https://{{ env_var('GIT_TOKEN') }}@github.com/your-org/dbt-internal-utils.git"
    revision: v0.3.0
```

**Deploy key setup for CI:**
```bash
# In CI environment, configure SSH key
mkdir -p ~/.ssh
echo "$DEPLOY_KEY" > ~/.ssh/id_rsa
chmod 600 ~/.ssh/id_rsa
ssh-keyscan github.com >> ~/.ssh/known_hosts
dbt deps
```

### Monorepo Local Packages

```yaml
# When multiple dbt projects share macros in the same repo
packages:
  - local: ../dbt-shared-macros

# Directory structure:
# monorepo/
# ├── dbt-shared-macros/
# │   ├── dbt_project.yml
# │   └── macros/
# │       └── utils/
# ├── dbt-analytics/
# │   ├── dbt_project.yml
# │   ├── packages.yml       ← references ../dbt-shared-macros
# │   └── models/
# └── dbt-marketing/
#     ├── dbt_project.yml
#     ├── packages.yml       ← references ../dbt-shared-macros
#     └── models/
```

---

## Common Macro Patterns

### `generate_schema_name` — Custom Schema Routing

Override where models are built. The most commonly customized macro.

```sql
{# macros/schema/generate_schema_name.sql #}

{% macro generate_schema_name(custom_schema_name, node) -%}
    {%- set default_schema = target.schema -%}

    {%- if target.name == 'prod' -%}
        {# In prod: use the custom schema directly (e.g., "finance", "marketing") #}
        {%- if custom_schema_name is not none -%}
            {{ custom_schema_name | trim }}
        {%- else -%}
            {{ default_schema }}
        {%- endif -%}

    {%- else -%}
        {# In dev/ci: prefix with developer schema (e.g., "dbt_dsong_finance") #}
        {%- if custom_schema_name is not none -%}
            {{ default_schema }}_{{ custom_schema_name | trim }}
        {%- else -%}
            {{ default_schema }}
        {%- endif -%}

    {%- endif -%}
{%- endmacro %}
```

**Result:**

| Environment | `custom_schema` | Built As |
|-------------|----------------|----------|
| dev (schema=dbt_dsong) | `finance` | `dbt_dsong_finance.fct_orders` |
| dev (schema=dbt_dsong) | none | `dbt_dsong.my_model` |
| prod (schema=analytics) | `finance` | `finance.fct_orders` |
| prod (schema=analytics) | none | `analytics.my_model` |

### `generate_alias_name` — Custom Table Alias

Override the table name without renaming the file.

```sql
{# macros/schema/generate_alias_name.sql #}

{% macro generate_alias_name(custom_alias_name, node) -%}
    {%- if custom_alias_name -%}
        {{ custom_alias_name | trim }}
    {%- elif node.version -%}
        {{ return(node.name ~ "_v" ~ node.version) }}
    {%- else -%}
        {{ node.name }}
    {%- endif -%}
{%- endmacro %}
```

### Grant Macros — Auto-Grant After Build

```sql
{# macros/grants/grant_select.sql #}

{% macro grant_select(role) %}
    {% if target.type == 'snowflake' %}
        grant usage on schema {{ target.schema }} to role {{ role }};
        grant select on all tables in schema {{ target.schema }} to role {{ role }};
        grant select on all views in schema {{ target.schema }} to role {{ role }};
    {% elif target.type == 'bigquery' %}
        {# BigQuery uses IAM, not SQL grants — handle in Terraform/console #}
        {{ log("BigQuery permissions managed via IAM, skipping SQL grant", info=true) }}
    {% endif %}
{% endmacro %}
```

**Usage as post-hook:**
```yaml
# dbt_project.yml
models:
  my_project:
    marts:
      +post-hook:
        - "{{ grant_select('analytics_reader') }}"
```

### Logging Macros — Structured Debugging

```sql
{# macros/logging/log_model_timing.sql #}

{% macro log_model_timing(step_name) %}
    {{ log("TIMING | model=" ~ this.name ~ " | step=" ~ step_name ~ " | target=" ~ target.name, info=true) }}
{% endmacro %}

{# macros/logging/log_row_count.sql #}

{% macro log_row_count(relation) %}
    {% set row_count_query %}
        select count(*) as row_count from {{ relation }}
    {% endset %}
    {% set results = run_query(row_count_query) %}
    {% if execute %}
        {% set row_count = results.columns[0][0] %}
        {{ log("ROW_COUNT | relation=" ~ relation ~ " | count=" ~ row_count, info=true) }}
    {% endif %}
{% endmacro %}
```

### Deduplicate Macro — Snowflake QUALIFY vs BigQuery Workaround

```sql
{# macros/utils/deduplicate.sql #}

{% macro deduplicate(relation, partition_by, order_by) %}
    {% if target.type == 'snowflake' %}
        select *
        from {{ relation }}
        qualify row_number() over (
            partition by {{ partition_by }}
            order by {{ order_by }} desc
        ) = 1

    {% elif target.type == 'bigquery' %}
        select * except(rn)
        from (
            select
                *,
                row_number() over (
                    partition by {{ partition_by }}
                    order by {{ order_by }} desc
                ) as rn
            from {{ relation }}
        )
        where rn = 1
    {% endif %}
{% endmacro %}
```

**Usage:**
```sql
-- stg_shopify__orders.sql
-- Deduplicate orders keeping the most recently updated record
with source as (
    select * from {{ source('shopify', 'orders') }}
),

deduped as (
    {{ deduplicate(
        relation='source',
        partition_by='id',
        order_by='updated_at'
    ) }}
)

select
    id as order_id,
    customer_id,
    status as order_status,
    created_at as order_date,
    updated_at
from deduped
```

### Incremental Merge Predicate Macro

```sql
{# macros/utils/incremental_filter.sql #}

{% macro incremental_filter(timestamp_column, lookback_hours=24) %}
    {# Apply incremental filter with a safety lookback window #}
    {% if is_incremental() %}
        where {{ timestamp_column }} > (
            select dateadd('hour', -{{ lookback_hours }}, max({{ timestamp_column }}))
            from {{ this }}
        )
    {% endif %}
{% endmacro %}
```

**Usage:**
```sql
select
    event_id,
    customer_id,
    event_type,
    event_timestamp
from {{ ref('stg_segment__events') }}
{{ incremental_filter('event_timestamp', lookback_hours=6) }}
```

---

## Debugging Jinja

### Core Debugging Workflow

```
1. dbt compile          →  Inspect generated SQL in target/compiled/
2. {{ log() }}          →  Print variables and intermediate values
3. dbt run-operation    →  Test macros in isolation
4. dbt --debug run      →  Full verbose output with adapter logs
```

### `dbt compile` — Inspect Generated SQL

```bash
# Compile all models
dbt compile

# Compile a single model
dbt compile --select fct_orders

# Find compiled output
cat target/compiled/my_project/models/marts/finance/fct_orders.sql
```

Compare the compiled SQL against expectations. Every Jinja tag is resolved — what remains is pure SQL.

### `{{ log() }}` — Print Debug Messages

```sql
{# Print variable values during compilation #}
{% set payment_methods = ['credit_card', 'bank_transfer', 'gift_card'] %}
{{ log("payment_methods: " ~ payment_methods, info=true) }}

{# Print target info #}
{{ log("target.name=" ~ target.name ~ " target.type=" ~ target.type, info=true) }}

{# Debug inside a loop #}
{% for method in payment_methods %}
    {{ log("Processing method: " ~ method ~ " (loop.index=" ~ loop.index ~ ")", info=true) }}
{% endfor %}

{# Debug macro arguments #}
{% macro safe_divide(numerator, denominator) %}
    {{ log("safe_divide called with: " ~ numerator ~ " / " ~ denominator, info=true) }}
    ...
{% endmacro %}
```

### `dbt run-operation` — Test Macros in Isolation

```bash
# Run a macro without building any models
dbt run-operation safe_divide --args '{"numerator": "revenue", "denominator": "order_count"}'

# Test macro with different targets
dbt run-operation safe_divide --args '{"numerator": "10", "denominator": "0"}' --target dev

# Run operational macros (grants, cleanup)
dbt run-operation grant_select --args '{"role": "analytics_reader"}'
```

### Common Errors and Solutions

| Error Message | Cause | Fix |
|---------------|-------|-----|
| `Compilation Error: 'xxx' is undefined` | Typo in variable, ref, or macro name | Check spelling; verify macro is in `macros/` directory |
| `Compilation Error in ... (Jinja syntax)` | Mismatched `{% %}` tags or missing `{% endif %}` | Check every `if`/`for` has a matching `endif`/`endfor` |
| `Parsing Error: expected token 'end of statement block', got '='` | Using `=` inside `{{ }}` (use `{% set %}` instead) | Move assignment to a `{% set %}` statement tag |
| `Recursion limit reached` | Macro A calls macro B which calls macro A | Review call graph; break circular dependency |
| `Runtime Error: maximum recursion depth` | `is_incremental()` logic causing self-reference loop | Ensure `{{ this }}` is only used inside `{% if is_incremental() %}` blocks |
| `Database Error: relation does not exist` | `ref()` target model not yet built | Run with `dbt build` (respects DAG) or build upstream first |
| `Encountered an error: 'run_query' is not defined` | Using `run_query` outside of execution context | Wrap with `{% if execute %}` guard |

### The `execute` Guard

`run_query()` and similar functions only work during execution, not during parsing.

```sql
{# DON'T: This fails during dbt parse/compile #}
{% set results = run_query("select 1") %}
{% set value = results.columns[0][0] %}

{# DO: Guard with execute flag #}
{% if execute %}
    {% set results = run_query("select 1") %}
    {% set value = results.columns[0][0] %}
{% else %}
    {% set value = none %}
{% endif %}
```

### `dbt --debug run` — Verbose Output

```bash
# Full debug output including adapter SQL and timing
dbt --debug run --select fct_orders

# Combine with compile for maximum visibility
dbt --debug compile --select fct_orders
```

### Debugging Checklist

When Jinja produces unexpected SQL, follow this sequence:

1. **Compile first:** `dbt compile --select <model>` and read `target/compiled/.../model.sql`
2. **Add logging:** Insert `{{ log("variable=" ~ my_var, info=true) }}` around the problem area
3. **Check context:** Verify `target.name`, `target.type`, `is_incremental()` return expected values
4. **Isolate macros:** Test with `dbt run-operation` and explicit arguments
5. **Check execute flag:** Ensure `run_query()` calls are inside `{% if execute %}` blocks
6. **Review whitespace:** Use `{%- -%}` if extra blank lines appear in compiled SQL
7. **Go verbose:** Run `dbt --debug run` for adapter-level SQL and response logging

---

**Back to:** [Main Skill File](../SKILL.md)
