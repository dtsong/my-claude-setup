# CI/CD & Deployment

## Development Workflow

Prefer `dbt build` over separate run + test. Build executes in DAG order, testing immediately after each model.

```bash
dbt build --select +fct_orders          # build model + ancestors in DAG order
dbt compile --select stg_stripe__payments  # preview SQL without executing
```

Use `--defer` and `--state` to reference production artifacts during local dev:

```bash
dbt build --select state:modified+ --defer --state ./prod-artifacts
```

Store `profiles.yml` in `~/.dbt/` (never commit). Run `dbt debug` to verify connection.

## Slim CI

Build and test only modified models + downstream descendants using state comparison against production `manifest.json`.

| Selector | Meaning |
|----------|---------|
| `state:modified` | Models with SQL/config/schema changes |
| `state:modified+` | Modified + all downstream descendants |
| `state:new` | Newly added models |

Store production `manifest.json` via GitHub Actions artifact, S3/GCS, or dbt Cloud `--defer`.

**--empty flag (dbt 1.8+):** Run models with `limit 0` injected -- zero warehouse cost, validates SQL compilation only. Use as fast first gate before real Slim CI build.

## GitHub Actions -- Snowflake CI

```yaml
name: dbt Slim CI
on:
  pull_request:
    branches: [main]
jobs:
  dbt-ci:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with: { python-version: "3.11" }
      - run: pip install dbt-snowflake
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
        env: { DBT_PROFILES_DIR: . }
      - run: dbt deps
      - name: Download production manifest
        uses: dawidd6/action-download-artifact@v3
        with: { name: dbt-prod-manifest, workflow: dbt-prod-deploy.yml, branch: main, path: ./prod-artifacts }
        continue-on-error: true
      - name: dbt build (Slim CI)
        run: |
          if [ -f ./prod-artifacts/manifest.json ]; then
            dbt build --select state:modified+ --defer --state ./prod-artifacts
          else
            dbt build
          fi
```

For BigQuery: replace `dbt-snowflake` with `dbt-bigquery`, add `google-github-actions/auth@v2`, set `maximum_bytes_billed` in profile.

## Production Deploy

Capture manifest for future Slim CI:

```yaml
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
      - run: pip install dbt-snowflake && dbt deps && dbt build
      - uses: actions/upload-artifact@v4
        with: { name: dbt-prod-manifest, path: target/manifest.json, retention-days: 90 }
```

## dbt Cloud Jobs

| Job | Trigger | Command |
|-----|---------|---------|
| CI | PR to main | `dbt build --select state:modified+ --defer --favor-state` |
| Production | Merge to main | `dbt build` (with docs + freshness enabled) |
| Full refresh | Cron `0 4 * * *` | `dbt build --full-refresh --select config.materialized:incremental` |

## Environment Strategy

| Environment | Schema Pattern |
|-------------|---------------|
| Local dev | `dev_<username>` |
| CI | `ci_pr_<number>` |
| Staging | `staging` |
| Production | `prod` |

Override `generate_schema_name` macro: in prod use custom schema directly (e.g., `finance`); in dev/ci prefix with target schema (e.g., `dev_jsmith_finance`).

Use target-based conditional config: views in dev for speed, tables in prod for BI.

## Blue/Green Deployment

Build into shadow schema, verify, then atomically swap with live schema.

- **Snowflake:** `ALTER SCHEMA ... SWAP WITH ...` for atomic cutover and instant rollback
- **BigQuery:** Route views to new dataset (no native schema swap)

Use blue/green for large projects with BI consumers or SLA-critical deployments. Use direct deploy for small projects or incremental-heavy workloads.

## Cost Optimization

| Environment | Snowflake Size | Auto-Suspend |
|-------------|---------------|-------------|
| CI | X-SMALL | 60s |
| Dev | X-SMALL | 120s |
| Production | MEDIUM+ | 300s |

BigQuery: set `maximum_bytes_billed` in profiles. For flat-rate pricing, assign CI to a separate reservation.

Automate CI schema cleanup on PR close with `drop_pr_schema` macro.

## SQLFluff Integration

Configure `.sqlfluff` with `templater = dbt`, set dialect, leading commas, lowercase keywords, explicit aliases. Add pre-commit hook and CI step with `github-annotation` format for inline PR annotations.
