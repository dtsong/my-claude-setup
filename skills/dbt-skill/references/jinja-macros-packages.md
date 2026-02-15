# Jinja, Macros & Packages

## Jinja Fundamentals

| Tag | Syntax | Purpose |
|-----|--------|---------|
| Expression | `{{ }}` | Output values into SQL (refs, vars, macros) |
| Statement | `{% %}` | Control flow, variable assignment |
| Comment | `{# #}` | Stripped during compilation |

**Whitespace control:** `{%- ... -%}` strips whitespace on the hyphen side.

**Key context objects:** `ref()`, `source()`, `config()`, `var()`, `env_var()`, `this`, `target`, `is_incremental()`.

## Control Flow Patterns

**Environment-specific logic:** Use `target.name` to vary behavior.

```sql
{% if target.name == 'dev' %}
    where order_date >= dateadd('month', -3, current_date)
{% endif %}
```

**Dynamic pivot:**

```sql
{% set payment_methods = dbt_utils.get_column_values(
    table=ref('stg_stripe__payments'), column='payment_method') %}
{% for method in payment_methods %}
sum(case when payment_method = '{{ method }}' then amount_dollars else 0 end) as {{ method }}_amount
{%- if not loop.last %},{% endif %}
{% endfor %}
```

**Variable assignment:** `{% set %}` for simple values, lists, dicts, or query results (wrap `run_query` in `{% if execute %}` guard).

## Writing Custom Macros

```sql
{% macro safe_divide(numerator, denominator) %}
    {% if target.type == 'snowflake' %}
        div0({{ numerator }}, {{ denominator }})
    {% elif target.type == 'bigquery' %}
        safe_divide({{ numerator }}, {{ denominator }})
    {% else %}
        case when {{ denominator }} != 0 then {{ numerator }} / {{ denominator }} else 0 end
    {% endif %}
{% endmacro %}
```

**Return values:** Implicit (rendered template) for SQL generation. Explicit `{% do return(value) %}` for computed values.

**Macro organization:**

| Directory | Contents |
|-----------|----------|
| `macros/utils/` | `safe_divide`, `deduplicate`, `cents_to_dollars` |
| `macros/schema/` | `generate_schema_name`, `generate_alias_name` |
| `macros/tests/` | Custom generic tests |
| `macros/grants/` | Permission management post-hooks |

**When to extract:** 1 use + high complexity = extract for readability. 2+ uses = always extract. Cross-project = extract to package.

## Common Macro Patterns

**generate_schema_name:** In prod, use custom schema directly. In dev/ci, prefix with target schema.

**Deduplicate (warehouse-adaptive):**

```sql
{% macro deduplicate(relation, partition_by, order_by) %}
    {% if target.type == 'snowflake' %}
        select * from {{ relation }}
        qualify row_number() over (partition by {{ partition_by }} order by {{ order_by }} desc) = 1
    {% elif target.type == 'bigquery' %}
        select * except(rn) from (
            select *, row_number() over (partition by {{ partition_by }} order by {{ order_by }} desc) as rn
            from {{ relation }}
        ) where rn = 1
    {% endif %}
{% endmacro %}
```

**Incremental filter:** Reusable macro wrapping `is_incremental()` with configurable lookback window.

**Grant macros:** Post-hook `grant_select` using `target.type` for Snowflake SQL grants vs BigQuery IAM.

## Essential Packages

| Package | Priority | Purpose |
|---------|----------|---------|
| `dbt-labs/dbt_utils` | Must-have | Surrogate keys, pivot/unpivot, date spine, `unique_combination_of_columns` |
| `calogica/dbt_expectations` | Must-have | Great Expectations-style tests: ranges, regex, row counts, distributions |
| `dbt-labs/codegen` | Dev only | Generate base models, model YAML, source YAML from existing tables |
| `calogica/dbt_date` | Situational | Date spine, fiscal calendars, relative date helpers |
| `dbt-labs/audit_helper` | Situational | Compare model versions during refactoring |
| `dbt-labs/dbt_project_evaluator` | CI | Lint project structure, naming, DAG violations |
| `elementary-data/elementary` | Production | Anomaly detection, schema monitoring, observability |

## Package Management

Pin versions with ranges: `version: [">=1.3.0", "<2.0.0"]`. Never leave unpinned.

Commit `packages.yml` and `package-lock.yml`. Add `dbt_packages/` to `.gitignore`. Run `dbt deps` after clone, after editing `packages.yml`, and in every CI run.

**Private packages:** Use SSH (`git@github.com:...`) or token auth (`https://{{ env_var('GIT_TOKEN') }}@github.com/...`). Local packages via `local: ../path`.

## Debugging Jinja

1. `dbt compile --select model` -- inspect `target/compiled/` for generated SQL
2. `{{ log("var=" ~ my_var, info=true) }}` -- print debug values
3. `dbt run-operation macro_name --args '{...}'` -- test macros in isolation
4. `dbt --debug run` -- full verbose adapter logging

**Common errors:**
- `'xxx' is undefined` -- check spelling, verify macro in `macros/` dir
- `expected 'end of statement block'` -- using `=` inside `{{ }}`, use `{% set %}` instead
- `run_query is not defined` -- wrap in `{% if execute %}` guard
- `relation does not exist` -- build upstream first or use `dbt build` (DAG order)
