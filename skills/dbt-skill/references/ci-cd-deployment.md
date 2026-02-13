# CI/CD & Deployment

> **Part of:** [dbt-skill](../SKILL.md)
> **Purpose:** Local dev workflows, Slim CI, GitHub Actions, dbt Cloud jobs, environment strategy, blue/green deployment, cost optimization, and SQLFluff integration

---

## Table of Contents

1. [Development Workflow](#development-workflow)
2. [Slim CI](#slim-ci)
3. [GitHub Actions Workflow](#github-actions-workflow)
4. [dbt Cloud Job Configuration](#dbt-cloud-job-configuration)
5. [Environment Strategy](#environment-strategy)
6. [Blue/Green Deployment](#bluegreen-deployment)
7. [Cost Optimization](#cost-optimization)
8. [SQLFluff Integration](#sqlfluff-integration)

---

## Development Workflow

### Local Dev Loop

```
edit SQL -> dbt compile --select model  -> dbt run --select model  -> dbt test --select model  -> iterate
```

Prefer `dbt build` over separate `dbt run` + `dbt test`. Build executes in DAG order, running tests immediately after each model materializes.

```bash
# DO: build runs + tests in DAG order
dbt build --select +fct_orders

# DON'T: run everything, then test everything (late failure detection)
dbt run --select +fct_orders && dbt test --select +fct_orders
```

### dbt compile for SQL Inspection

Use `dbt compile` to preview generated SQL without executing. Output lands in `target/compiled/`.

```bash
dbt compile --select stg_stripe__payments
cat target/compiled/my_project/models/staging/stripe/stg_stripe__payments.sql
```

### Defer to Production Artifacts

Use `--defer` and `--state` to reference production artifacts during local development, avoiding full DAG rebuilds.

```bash
mkdir -p ./prod-artifacts
cp /path/to/production/manifest.json ./prod-artifacts/

# build only modified models, defer upstream refs to prod
dbt build --select state:modified+ --defer --state ./prod-artifacts
```

### profiles.yml for Local Development

Store in `~/.dbt/profiles.yml` (never commit this file).

**Snowflake:**

```yaml
my_project:
  target: dev
  outputs:
    dev:
      type: snowflake
      account: "{{ env_var('SNOWFLAKE_ACCOUNT') }}"
      user: "{{ env_var('SNOWFLAKE_USER') }}"
      password: "{{ env_var('SNOWFLAKE_PASSWORD') }}"
      role: transformer
      database: analytics
      warehouse: dev_wh
      schema: "dev_{{ env_var('USER') }}"    # dev_jsmith
      threads: 4
```

**BigQuery:**

```yaml
my_project:
  target: dev
  outputs:
    dev:
      type: bigquery
      method: oauth                          # use gcloud auth for local dev
      project: my-analytics-project
      dataset: "dev_{{ env_var('USER') }}"   # dev_jsmith
      threads: 4
      location: US
```

Run `dbt debug` to verify the connection before starting development.

---

## Slim CI

### What It Is

Slim CI builds and tests only modified models plus their downstream descendants, using dbt's state comparison against a previous `manifest.json`.

| Approach | Models Built | Duration | Cost |
|----------|-------------|----------|------|
| Full build (500 models) | 500 | 30-45 min | High |
| Slim CI | 5-20 | 2-5 min | Low |

### state:modified+ Selector

| Selector | Meaning |
|----------|---------|
| `state:modified` | Only models with SQL, config, or schema changes |
| `state:modified+` | Modified models + all downstream descendants |
| `state:new` | Newly added models |
| `state:modified+ state:new+` | Modified and new, plus all descendants |

The `+` suffix is critical -- a change to `stg_stripe__payments` must also rebuild `int_payments_pivoted`, `fct_orders`, and any downstream model.

### manifest.json Artifacts

Produced by every `dbt run`, `dbt build`, or `dbt compile` in `target/`. Store production artifacts for CI comparison:

| Method | How |
|--------|-----|
| GitHub Actions artifact | Upload after prod deploy, download in CI |
| S3/GCS bucket | Write on deploy, read in CI |
| dbt Cloud | Automatic via `--defer` in CI jobs |

### --empty Flag (dbt 1.8+)

Run models with `limit 0` injected into all `ref()` and `source()` calls -- zero warehouse cost, validates SQL compilation and schemas only.

```bash
dbt build --select state:modified+ --defer --state ./prod-artifacts --empty
```

Use `--empty` as a fast first gate. Follow with a real Slim CI build for data-level validation.

---

## GitHub Actions Workflow

### Snowflake CI Workflow

```yaml
# .github/workflows/dbt-ci.yml
name: dbt Slim CI

on:
  pull_request:
    branches: [main]

env:
  DBT_PROFILES_DIR: .

jobs:
  dbt-ci:
    runs-on: ubuntu-latest
    permissions:
      contents: read
      pull-requests: write

    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with:
          python-version: "3.11"

      - name: Install dbt
        run: pip install dbt-snowflake

      - name: Create profiles.yml
        run: |
          cat <<EOF > profiles.yml
          my_project:
            target: ci
            outputs:
              ci:
                type: snowflake
                account: "${{ secrets.SNOWFLAKE_ACCOUNT }}"
                user: "${{ secrets.SNOWFLAKE_CI_USER }}"
                password: "${{ secrets.SNOWFLAKE_CI_PASSWORD }}"
                role: ci_role
                database: analytics
                warehouse: ci_wh_xs
                schema: "ci_pr_${{ github.event.pull_request.number }}"
                threads: 4
          EOF

      - run: dbt deps

      - name: Download production manifest
        uses: dawidd6/action-download-artifact@v3
        with:
          name: dbt-prod-manifest
          workflow: dbt-prod-deploy.yml
          branch: main
          path: ./prod-artifacts
        continue-on-error: true    # first run won't have artifacts

      - name: dbt build (Slim CI)
        run: |
          if [ -f ./prod-artifacts/manifest.json ]; then
            dbt build --select state:modified+ --defer --state ./prod-artifacts
          else
            dbt build
          fi

      - name: Comment PR with results
        if: always()
        uses: actions/github-script@v7
        with:
          script: |
            const fs = require('fs');
            const r = JSON.parse(fs.readFileSync('target/run_results.json', 'utf8'));
            const passed = r.results.filter(x => x.status === 'pass').length;
            const failed = r.results.filter(x => x.status === 'fail' || x.status === 'error').length;
            const icon = failed > 0 ? ':x:' : ':white_check_mark:';
            github.rest.issues.createComment({
              issue_number: context.issue.number,
              owner: context.repo.owner, repo: context.repo.repo,
              body: `## ${icon} dbt CI\n| Passed | Failed | Total |\n|--------|--------|-------|\n| ${passed} | ${failed} | ${r.results.length} |`
            });
```

### BigQuery CI -- Key Differences

Replace the install and profiles steps:

```yaml
      - run: pip install dbt-bigquery

      - uses: google-github-actions/auth@v2
        with:
          credentials_json: "${{ secrets.GCP_SA_KEY }}"

      - name: Create profiles.yml
        run: |
          cat <<EOF > profiles.yml
          my_project:
            target: ci
            outputs:
              ci:
                type: bigquery
                method: service-account
                project: my-analytics-project
                dataset: "ci_pr_${{ github.event.pull_request.number }}"
                threads: 4
                location: US
                keyfile: "${{ steps.auth.outputs.credentials_file_path }}"
                maximum_bytes_billed: 10000000000    # 10 GB safety limit
          EOF
```

### Production Deploy Workflow

Capture the production manifest for future Slim CI runs:

```yaml
# .github/workflows/dbt-prod-deploy.yml
name: dbt Production Deploy
on:
  push:
    branches: [main]
    paths: ["models/**", "macros/**", "tests/**", "dbt_project.yml", "packages.yml"]

jobs:
  deploy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with: { python-version: "3.11" }
      - run: pip install dbt-snowflake    # or dbt-bigquery
      # ... create profiles.yml for prod (same pattern as CI) ...
      - run: dbt deps && dbt build
      - uses: actions/upload-artifact@v4
        with:
          name: dbt-prod-manifest
          path: target/manifest.json
          retention-days: 90
```

---

## dbt Cloud Job Configuration

### CI Job (Triggered on PR)

| Setting | Value |
|---------|-------|
| **Trigger** | Pull request to main |
| **Commands** | `dbt build --select state:modified+ --defer --favor-state` |
| **Defer to** | Production environment |
| **Schema** | `ci_pr_{{ env_var('DBT_CLOUD_PR_ID') }}` |

### Production Job (Triggered on Merge)

| Setting | Value |
|---------|-------|
| **Trigger** | On merge to main |
| **Commands** | `dbt build` |
| **Generate docs** | Enabled |
| **Run source freshness** | Enabled |

### Scheduled Full Refresh

| Setting | Value |
|---------|-------|
| **Trigger** | Cron: `0 4 * * *` (4 AM UTC daily) |
| **Commands** | `dbt build --full-refresh --select config.materialized:incremental` |

Rebuild incremental models nightly to clear drift from late-arriving data.

### Environment Variables

| Variable | Scope | Example |
|----------|-------|---------|
| `DBT_CLOUD_PR_ID` | CI | Auto-populated |
| `DBT_TARGET_SCHEMA` | Per env | `prod`, `staging` |
| `DBT_WAREHOUSE` | Per env | `prod_wh`, `ci_wh_xs` |
| `DBT_THREADS` | Per env | `8` (prod), `4` (ci) |

### Job Chaining

Configure in dbt Cloud under **Triggers** > "Run when another job completes":

```
Source Freshness Check -> Production Build -> Documentation Generation
```

---

## Environment Strategy

### Schema-Based Environments

| Environment | Schema Pattern | Example |
|-------------|---------------|---------|
| Local dev | `dev_<username>` | `dev_jsmith` |
| CI | `ci_pr_<number>` | `ci_pr_142` |
| Staging | `staging` | `staging` |
| Production | `prod` | `prod` |

### generate_schema_name Override

```sql
-- macros/generate_schema_name.sql
{% macro generate_schema_name(custom_schema_name, node) -%}
    {%- set default_schema = target.schema -%}
    {%- if target.name == 'prod' -%}
        {#-- prod: use custom schema directly (e.g., "finance") --#}
        {{ custom_schema_name | trim if custom_schema_name is not none else default_schema }}
    {%- else -%}
        {#-- dev/ci: prefix with target schema (e.g., "dev_jsmith_finance") --#}
        {%- if custom_schema_name is not none -%}
            {{ default_schema }}_{{ custom_schema_name | trim }}
        {%- else -%}
            {{ default_schema }}
        {%- endif -%}
    {%- endif -%}
{%- endmacro %}
```

| Target | Custom Schema | Result |
|--------|--------------|--------|
| prod | `finance` | `finance` |
| prod | (none) | `prod` |
| dev | `finance` | `dev_jsmith_finance` |
| ci | `finance` | `ci_pr_142_finance` |

### generate_database_name (Snowflake Multi-Database)

```sql
-- macros/generate_database_name.sql
{% macro generate_database_name(custom_database_name, node) -%}
    {%- set default_database = target.database -%}
    {%- if target.name == 'prod' and custom_database_name is not none -%}
        {{ custom_database_name | trim }}
    {%- else -%}
        {{ default_database }}
    {%- endif -%}
{%- endmacro %}
```

Prevents dev runs from writing to production databases.

### Target-Based Conditional Config

```yaml
# dbt_project.yml -- global config
models:
  my_project:
    staging:
      +materialized: view
    intermediate:
      +materialized: ephemeral
    marts:
      +materialized: "{{ 'table' if target.name == 'prod' else 'view' }}"
```

```sql
-- per-model config
{{ config(
    materialized = 'view' if target.name == 'dev' else 'table',
    cluster_by = ['order_date'] if target.name == 'prod' else none
) }}
```

```yaml
# DO: views in dev for speed, tables in prod for BI
marts:
  +materialized: "{{ 'table' if target.name == 'prod' else 'view' }}"

# DON'T: incremental in dev (unnecessary complexity)
staging:
  +materialized: "{{ 'incremental' if target.name == 'prod' else 'view' }}"
```

---

## Blue/Green Deployment

### Concept

Build into a shadow schema (green), verify, then atomically swap with the live schema (blue).

```
Production (blue):  analytics.prod         <- BI tools point here
Shadow (green):     analytics.prod_shadow  <- dbt builds here
                         |
    After validation:  SWAP blue <-> green
```

### Snowflake: Atomic Schema Swap

```sql
-- macros/blue_green_swap.sql
{% macro blue_green_swap(database, live_schema, shadow_schema) %}
    {% set swap_query %}
        alter schema {{ database }}.{{ live_schema }}
            swap with {{ database }}.{{ shadow_schema }};
    {% endset %}
    {% do run_query(swap_query) %}
    {{ log("Swapped " ~ live_schema ~ " with " ~ shadow_schema, info=True) }}
{% endmacro %}
```

```bash
dbt run-operation blue_green_swap \
    --args '{database: analytics, live_schema: prod, shadow_schema: prod_shadow}'
```

### BigQuery: View Routing

BigQuery lacks schema swaps. Route views to the new dataset instead:

```sql
-- macros/bigquery_blue_green.sql
{% macro update_routing_views(prod_dataset, shadow_dataset) %}
    {% set models = graph.nodes.values()
        | selectattr("resource_type", "equalto", "model")
        | selectattr("config.materialized", "in", ["table", "incremental"])
        | list %}
    {% for model in models %}
        {% set q %}
            create or replace view `{{ target.project }}.{{ prod_dataset }}.{{ model.name }}` as
            select * from `{{ target.project }}.{{ shadow_dataset }}.{{ model.name }}`;
        {% endset %}
        {% do run_query(q) %}
    {% endfor %}
{% endmacro %}
```

### When to Use Blue/Green

| Scenario | Approach | Reason |
|----------|----------|--------|
| Small project (< 50 models) | Direct deploy | Low risk, fast rebuild |
| Large project with BI consumers | Blue/green | Zero-downtime swap |
| Incremental-heavy project | Direct deploy | Full rebuild too expensive |
| SLA-critical / regulated | Blue/green | Atomic cutover, instant rollback |

### Rollback

**Snowflake:** Swap schemas back. Keep the old schema for 24h before dropping.

```sql
alter schema analytics.prod swap with analytics.prod_shadow;    -- instant rollback
```

**BigQuery:** Re-point routing views to the previous dataset.

**Snowflake Time Travel:** Query previous state without swapping:

```sql
select * from analytics.prod.fct_orders at (offset => -3600);
```

---

## Cost Optimization

### Snowflake Warehouse Sizing

| Environment | Size | Auto-Suspend |
|-------------|------|-------------|
| CI | X-SMALL | 60s |
| Dev | X-SMALL | 120s |
| Staging | SMALL | 300s |
| Production | MEDIUM+ | 300s |

```sql
create warehouse if not exists ci_wh_xs
    warehouse_size = 'X-SMALL'
    auto_suspend = 60
    auto_resume = true
    initially_suspended = true;
```

### BigQuery Cost Controls

Set `maximum_bytes_billed` in profiles to cap per-query cost. For flat-rate pricing, assign CI to a separate reservation with limited slots.

### Schema Cleanup After Merge

```sql
-- macros/drop_pr_schema.sql
{% macro drop_pr_schema(pr_number) %}
    {% set drop_query %}
        drop schema if exists {{ target.database }}.ci_pr_{{ pr_number }} cascade;
    {% endset %}
    {% do run_query(drop_query) %}
    {{ log("Dropped schema: ci_pr_" ~ pr_number, info=True) }}
{% endmacro %}
```

Automate via GitHub Actions on PR close:

```yaml
# .github/workflows/dbt-cleanup.yml
name: Cleanup PR Schema
on:
  pull_request:
    types: [closed]
jobs:
  cleanup:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: pip install dbt-snowflake
      - run: dbt run-operation drop_pr_schema --args '{pr_number: ${{ github.event.pull_request.number }}}'
```

### Monitoring CI Costs

**Snowflake:**

```sql
select date_trunc('week', start_time) as week, sum(credits_used) as ci_credits
from snowflake.account_usage.warehouse_metering_history
where warehouse_name = 'CI_WH_XS'
    and start_time >= dateadd('month', -3, current_timestamp())
group by 1 order by 1;
```

**BigQuery:**

```sql
select date_trunc(creation_time, week) as week,
    sum(total_bytes_billed) / power(1024, 4) as tb_billed
from `region-us`.INFORMATION_SCHEMA.JOBS
where destination_table.dataset_id like 'ci_pr_%'
    and creation_time >= timestamp_sub(current_timestamp(), interval 90 day)
group by 1 order by 1;
```

---

## SQLFluff Integration

### What SQLFluff Is

SQLFluff is a SQL linter and auto-formatter that understands dbt's Jinja templating. It catches style inconsistencies and auto-fixes common issues before code review.

### .sqlfluff Configuration

```ini
[sqlfluff]
templater = dbt
dialect = snowflake
# for BigQuery: dialect = bigquery
max_line_length = 120
indent_unit = space

[sqlfluff:indentation]
tab_space_size = 4

[sqlfluff:layout:type:comma]
line_position = leading              # leading commas

[sqlfluff:rules:capitalisation.keywords]
capitalisation_policy = lower        # select, not SELECT

[sqlfluff:rules:capitalisation.identifiers]
extended_capitalisation_policy = lower

[sqlfluff:rules:capitalisation.functions]
extended_capitalisation_policy = lower

[sqlfluff:rules:aliasing.table]
aliasing = explicit                  # "from t as t" not "from t t"

[sqlfluff:rules:aliasing.column]
aliasing = explicit
```

### Rules Reference

| Rule | Recommendation | Reason |
|------|---------------|--------|
| `capitalisation.keywords` | Enable (lower) | Match dbt conventions |
| `aliasing.table` | Enable (explicit) | Readability |
| `layout.type:comma` | Enable (leading) | Cleaner diffs |
| `ambiguous.column_references` | Enable | Prevent ambiguous joins |
| `structure.subquery` | Disable | dbt CTEs handle this |
| `jinja.padding` | Enable | Consistent Jinja spacing |

### Pre-commit Hook

```yaml
# .pre-commit-config.yaml
repos:
  - repo: https://github.com/sqlfluff/sqlfluff
    rev: 3.3.0
    hooks:
      - id: sqlfluff-lint
        additional_dependencies: [dbt-snowflake]
        args: [--dialect, snowflake]
      - id: sqlfluff-fix
        additional_dependencies: [dbt-snowflake]
        args: [--dialect, snowflake, --force]
```

### CI Integration

```yaml
# add to dbt-ci.yml
      - run: pip install sqlfluff dbt-snowflake
      - name: Lint SQL
        run: sqlfluff lint models/ --dialect snowflake --format github-annotation
```

The `github-annotation` format produces inline annotations on the PR diff.

**DO/DON'T:**

```sql
-- DO: lowercase keywords, leading commas, explicit aliases
select
    orders.order_id
    , orders.customer_id
    , payments.total_amount
from {{ ref('stg_shopify__orders') }} as orders
left join {{ ref('int_payments_pivoted') }} as payments
    on orders.order_id = payments.order_id

-- DON'T: uppercase keywords, trailing commas, implicit aliases
SELECT
    o.order_id,
    o.customer_id,
    p.total_amount
FROM {{ ref('stg_shopify__orders') }} o
LEFT JOIN {{ ref('int_payments_pivoted') }} p
    ON o.order_id = p.order_id
```

---

**Back to:** [Main Skill File](../SKILL.md)
