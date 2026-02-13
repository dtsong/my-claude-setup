# Testing & Quality Strategy

> **Part of:** [dbt-skill](../SKILL.md)
> **Purpose:** Deep dive into schema tests, generic tests, singular tests, unit tests, dbt-expectations, dbt-utils testing helpers, and layer-specific testing strategy

This document provides comprehensive testing guidance for dbt projects. For the testing overview and quick examples, see the [main skill file](../SKILL.md#basic-testing-overview).

---

## Table of Contents

1. [Schema Tests (YAML-based)](#schema-tests-yaml-based)
2. [Custom Singular Tests](#custom-singular-tests)
3. [Custom Generic Tests](#custom-generic-tests)
4. [Unit Tests (dbt 1.8+)](#unit-tests-dbt-18)
5. [dbt-expectations Package](#dbt-expectations-package)
6. [dbt-utils Testing Helpers](#dbt-utils-testing-helpers)
7. [Test Configuration](#test-configuration)
8. [Testing Strategy by Layer](#testing-strategy-by-layer)
9. [Anti-patterns](#anti-patterns)

---

## Schema Tests (YAML-based)

Schema tests are the foundation of dbt testing. Define them in YAML alongside model documentation. dbt ships four built-in tests.

### Built-in Tests

```yaml
# _finance__models.yml
version: 2

models:
  - name: fct_orders
    columns:
      - name: order_id
        data_tests:
          - unique                          # Every value must be distinct
          - not_null                        # No NULL values allowed
      - name: order_status
        data_tests:
          - accepted_values:               # Value must be in the set
              values: ['completed', 'pending', 'cancelled', 'refunded']
              # Snowflake/BigQuery: case-sensitive — apply lower() in staging
      - name: customer_id
        data_tests:
          - not_null:
              where: "order_status != 'draft'"   # Conditional scope
          - relationships:                  # Referential integrity
              to: ref('dim_customers')
              field: customer_id
              # Runs a LEFT JOIN — watch for cost on large tables
              where: "customer_id is not null"    # Skip intentional orphans
```

### Configuration Options

Every schema test accepts optional configuration:

```yaml
      - name: order_id
        data_tests:
          - unique:
              severity: warn            # warn (non-blocking) or error (default, blocks pipeline)
              where: "order_date >= '2024-01-01'"  # Filter test scope
              config:
                store_failures: true    # Persist failing rows to a table for debugging
                limit: 100             # Cap number of failure rows returned
                tags: ['primary_key']  # Tag for selective test execution
```

### Compound Uniqueness with dbt-utils

When a primary key is a combination of columns:

```yaml
models:
  - name: fct_order_items
    description: "One record per order line item"
    data_tests:
      - dbt_utils.unique_combination_of_columns:
          combination_of_columns:
            - order_id
            - line_item_id
          # Generates: SELECT ... GROUP BY order_id, line_item_id HAVING count(*) > 1
```

---

## Custom Singular Tests

Singular tests are standalone SQL files in the `tests/` directory. The query must return **zero rows** to pass. Any row returned is a test failure.

### File Naming

```
tests/
├── assert_total_payment_amount_is_positive.sql
├── assert_order_dates_not_in_future.sql
├── assert_payment_revenue_matches_orders.sql
└── generic/                  # Generic tests go in a subdirectory
```

Use the prefix `assert_` for clarity.

### Example: Revenue Reconciliation

```sql
-- tests/assert_payment_revenue_matches_orders.sql
-- Returns rows where revenue totals diverge by more than $1.00
with order_totals as (
    select sum(total_amount) as total_order_revenue
    from {{ ref('fct_orders') }}
    where order_status = 'completed'
),
payment_totals as (
    select sum(amount_dollars) as total_payment_revenue
    from {{ ref('stg_stripe__payments') }}
    where payment_status = 'completed'
)
select
    order_totals.total_order_revenue,
    payment_totals.total_payment_revenue,
    abs(order_totals.total_order_revenue - payment_totals.total_payment_revenue) as difference
from order_totals
cross join payment_totals
where abs(order_totals.total_order_revenue - payment_totals.total_payment_revenue) > 1.00
```

### Example: Date Range Validation

```sql
-- tests/assert_order_dates_not_in_future.sql
select order_id, order_date
from {{ ref('fct_orders') }}
where order_date > current_date
   or order_date < '2020-01-01'  -- Business founded in 2020
```

### Example: Cross-table Consistency

```sql
-- tests/assert_completed_orders_have_payments.sql
-- Returns completed orders with no corresponding payment record
select o.order_id, o.order_status, o.order_date
from {{ ref('fct_orders') }} o
left join {{ ref('stg_stripe__payments') }} p
    on o.order_id = p.order_id
where o.order_status = 'completed'
  and p.payment_id is null
```

### Singular vs Generic: Decision Table

| Criterion | Use Singular | Use Generic |
|-----------|-------------|-------------|
| Business rule specific to one model | Yes | No |
| Cross-table reconciliation | Yes | No |
| Reusable across multiple models | No | Yes |
| Needs parameters (column, threshold) | No | Yes |
| Complex multi-step validation | Yes | No |
| Standard data quality check | No | Yes |

---

## Custom Generic Tests

Generic tests are reusable test macros. Define them in `tests/generic/` and apply them in YAML like built-in tests.

### Example: `is_positive`

```sql
-- tests/generic/is_positive.sql
{% test is_positive(model, column_name) %}

select {{ column_name }} as failing_value
from {{ model }}
where {{ column_name }} < 0

{% endtest %}
```

```yaml
models:
  - name: fct_orders
    columns:
      - name: total_amount
        data_tests:
          - is_positive           # Custom generic test
```

### Example: `row_count_matches`

```sql
-- tests/generic/row_count_matches.sql
{% test row_count_matches(model, compare_model) %}

with source_count as (
    select count(*) as row_count from {{ model }}
),
compare_count as (
    select count(*) as row_count from {{ ref(compare_model) }}
)
select
    source_count.row_count as source_rows,
    compare_count.row_count as compare_rows
from source_count
cross join compare_count
where source_count.row_count != compare_count.row_count

{% endtest %}
```

```yaml
models:
  - name: fct_orders
    data_tests:
      - row_count_matches:
          compare_model: stg_shopify__orders
```

### Parameterized with Defaults

```sql
-- tests/generic/value_is_between.sql
{% test value_is_between(model, column_name, min_value=0, max_value=none) %}

select {{ column_name }} as failing_value
from {{ model }}
where {{ column_name }} < {{ min_value }}
{% if max_value is not none %}
   or {{ column_name }} > {{ max_value }}
{% endif %}

{% endtest %}
```

```yaml
      - name: discount_percent
        data_tests:
          - value_is_between:
              min_value: 0
              max_value: 100
```

---

## Unit Tests (dbt 1.8+)

Unit tests validate transformation logic by mocking inputs and asserting expected outputs. They run against static data without querying the warehouse.

### YAML Syntax

```yaml
unit_tests:
  - name: test_fct_orders_total_calculation
    description: "Verify order totals sum correctly from payment pivots"
    model: fct_orders
    given:
      - input: ref('stg_shopify__orders')
        rows:
          - { order_id: 1, customer_id: 100, order_date: '2024-06-01', order_status: 'completed' }
          - { order_id: 2, customer_id: 101, order_date: '2024-06-02', order_status: 'completed' }
      - input: ref('int_payments_pivoted')
        rows:
          - { order_id: 1, credit_card_amount: 50.00, bank_transfer_amount: 25.00, total_amount: 75.00 }
          - { order_id: 2, credit_card_amount: 100.00, bank_transfer_amount: 0.00, total_amount: 100.00 }
    expect:
      rows:
        - { order_id: 1, customer_id: 100, order_status: 'completed', total_amount: 75.00 }
        - { order_id: 2, customer_id: 101, order_status: 'completed', total_amount: 100.00 }
```

### Complete Example: Testing Business Logic

Test a model that applies tiered discount logic:

```sql
-- models/intermediate/int_orders_with_discount.sql
with orders as (
    select * from {{ ref('stg_shopify__orders') }}
),
final as (
    select
        order_id, customer_id, subtotal,
        case
            when subtotal >= 500 then subtotal * 0.10   -- 10% discount over $500
            when subtotal >= 200 then subtotal * 0.05   -- 5% discount over $200
            else 0
        end as discount_amount,
        subtotal - case
            when subtotal >= 500 then subtotal * 0.10
            when subtotal >= 200 then subtotal * 0.05
            else 0
        end as total_after_discount
    from orders
)
select * from final
```

```yaml
unit_tests:
  - name: test_tiered_discount_logic
    description: "Verify discount tiers: 10% over $500, 5% over $200, 0% under $200"
    model: int_orders_with_discount
    given:
      - input: ref('stg_shopify__orders')
        rows:
          - { order_id: 1, customer_id: 100, subtotal: 600.00 }  # 10% tier
          - { order_id: 2, customer_id: 101, subtotal: 300.00 }  # 5% tier
          - { order_id: 3, customer_id: 102, subtotal: 100.00 }  # No discount
    expect:
      rows:
        - { order_id: 1, customer_id: 100, subtotal: 600.00, discount_amount: 60.00, total_after_discount: 540.00 }
        - { order_id: 2, customer_id: 101, subtotal: 300.00, discount_amount: 15.00, total_after_discount: 285.00 }
        - { order_id: 3, customer_id: 102, subtotal: 100.00, discount_amount: 0, total_after_discount: 100.00 }
```

### Overriding Macros

```yaml
unit_tests:
  - name: test_with_mocked_macro
    model: fct_orders
    given:
      - input: ref('stg_shopify__orders')
        rows:
          - { order_id: 1, customer_id: 100, order_date: '2024-06-01', order_status: 'completed' }
    overrides:
      macros:
        is_incremental: false     # Force full-refresh path in unit test
    expect:
      rows:
        - { order_id: 1, customer_id: 100, order_status: 'completed' }
```

### Limitations and Compatibility

| Limitation | Details |
|-----------|---------|
| No warehouse functions | Cannot test `current_timestamp()`, warehouse-specific UDFs |
| Static data only | Mocked rows are hardcoded — no dynamic test data |
| No incremental testing | Cannot test merge behavior or deduplication |
| Column matching | `expect` must include all columns the model selects |

| Feature | Snowflake | BigQuery |
|---------|-----------|----------|
| Unit test support | dbt 1.8+ | dbt 1.8+ |
| Date format in rows | `'2024-06-01'` (ISO) | `'2024-06-01'` (ISO) |
| Numeric precision | FLOAT/NUMBER | FLOAT64/NUMERIC |
| Execution method | Temporary tables | Temporary tables |

### When to Use Unit Tests

| Scenario | Use Unit Tests? |
|----------|----------------|
| Complex CASE/WHEN business logic | Yes |
| Multi-step calculations (discounts, taxes) | Yes |
| Jinja conditional logic paths | Yes |
| Simple column renames in staging | No -- overkill |
| Incremental merge behavior | No -- not supported |
| Testing warehouse functions | No -- not supported |

---

## dbt-expectations Package

[dbt-expectations](https://github.com/calogica/dbt-expectations) ports Great Expectations tests to dbt.

### Installation

```yaml
# packages.yml
packages:
  - package: calogica/dbt_expectations
    version: [">=0.10.0", "<0.11.0"]  # Pin to minor version range
```

### Top 10 Most Useful Expectations

#### 1. `expect_column_values_to_not_be_null`

Like `not_null` but supports `row_condition` filtering.

```yaml
      - name: customer_id
        data_tests:
          - dbt_expectations.expect_column_values_to_not_be_null:
              row_condition: "order_status = 'completed'"
```

#### 2. `expect_column_values_to_be_between`

Assert numeric values fall within a range.

```yaml
      - name: total_amount
        data_tests:
          - dbt_expectations.expect_column_values_to_be_between:
              min_value: 0
              max_value: 100000      # Flag suspiciously large orders
```

#### 3. `expect_column_values_to_be_in_set`

Like `accepted_values` with more configuration.

```yaml
      - name: payment_method
        data_tests:
          - dbt_expectations.expect_column_values_to_be_in_set:
              value_set: ['credit_card', 'bank_transfer', 'gift_card', 'store_credit']
              row_condition: "payment_status != 'failed'"
```

#### 4. `expect_column_distinct_count_to_equal`

Assert the exact number of distinct values.

```yaml
      - name: order_status
        data_tests:
          - dbt_expectations.expect_column_distinct_count_to_equal:
              value: 4              # Catches silent schema drift
```

#### 5. `expect_column_values_to_match_regex`

Validate string format with regular expressions.

```yaml
      - name: email
        data_tests:
          - dbt_expectations.expect_column_values_to_match_regex:
              regex: "^[a-zA-Z0-9_.+-]+@[a-zA-Z0-9-]+\\.[a-zA-Z0-9-.]+$"
              # Snowflake: REGEXP_LIKE | BigQuery: REGEXP_CONTAINS
```

#### 6. `expect_table_row_count_to_be_between`

Assert table size stays within bounds. Catches catastrophic data drops.

```yaml
models:
  - name: fct_orders
    data_tests:
      - dbt_expectations.expect_table_row_count_to_be_between:
          min_value: 1000        # Fewer = data pipeline issue
          max_value: 10000000    # More = duplication bug
```

#### 7. `expect_column_values_to_be_unique`

Like `unique` but supports `row_condition`.

```yaml
      - name: email
        data_tests:
          - dbt_expectations.expect_column_values_to_be_unique:
              row_condition: "is_active = true"
```

#### 8. `expect_column_pair_values_A_to_be_greater_than_B`

Assert ordering between two columns.

```yaml
    data_tests:
      - dbt_expectations.expect_column_pair_values_A_to_be_greater_than_B:
          column_A: total_amount
          column_B: discount_amount
          or_equal: true          # total >= discount
```

#### 9. `expect_column_mean_to_be_between`

Statistical guardrail for anomalous shifts.

```yaml
      - name: total_amount
        data_tests:
          - dbt_expectations.expect_column_mean_to_be_between:
              min_value: 20        # Avg below $20 = problem
              max_value: 500       # Avg above $500 = duplication
              severity: warn
```

#### 10. `expect_table_row_count_to_equal_other_table`

Assert two tables have matching row counts.

```yaml
    data_tests:
      - dbt_expectations.expect_table_row_count_to_equal_other_table:
          compare_model: ref('fct_orders_v2')
          # Migration validation: old model count must match new
```

---

## dbt-utils Testing Helpers

```yaml
# packages.yml
packages:
  - package: dbt-labs/dbt_utils
    version: [">=1.3.0", "<2.0.0"]
```

### `equal_rowcount`

```yaml
models:
  - name: fct_orders
    data_tests:
      - dbt_utils.equal_rowcount:
          compare_model: ref('stg_shopify__orders')
          # Staging and fact should have same row count (1:1 grain)
```

### `fewer_rows_than`

```yaml
models:
  - name: dim_customers
    data_tests:
      - dbt_utils.fewer_rows_than:
          compare_model: ref('fct_orders')
          # Customers should always be fewer than orders
```

### `not_accepted_values`

```yaml
      - name: order_status
        data_tests:
          - dbt_utils.not_accepted_values:
              values: ['test', 'debug', 'staging']
              # Ensure test data never leaks into production
```

### `expression_is_true`

The most flexible test -- assert any SQL expression evaluates to true for all rows.

```yaml
models:
  - name: fct_orders
    data_tests:
      - dbt_utils.expression_is_true:
          expression: "total_amount >= 0"
      - dbt_utils.expression_is_true:
          expression: "order_date <= current_date"
      - dbt_utils.expression_is_true:
          expression: "credit_card_amount + bank_transfer_amount = total_amount"
```

### `recency`

Assert that the most recent record is within an expected time window.

```yaml
models:
  - name: fct_orders
    data_tests:
      - dbt_utils.recency:
          datepart: day
          field: order_date
          interval: 3
          # Snowflake: DATEDIFF | BigQuery: DATE_DIFF
```

---

## Test Configuration

### Severity: `warn` vs `error`

| Severity | Behavior | Use When |
|----------|----------|----------|
| `error` (default) | Blocks pipeline | Primary keys, referential integrity, critical business rules |
| `warn` | Logs warning, continues | Data quality monitoring, statistical checks, soft constraints |

```yaml
      - name: email
        data_tests:
          - unique:
              severity: warn       # Duplicates are concerning but not blocking
          - not_null:
              severity: error      # Missing email on active customer IS blocking
              where: "is_active = true"
```

### Tags for Selective Execution

```yaml
      - name: order_id
        data_tests:
          - unique:
              config:
                tags: ['primary_key', 'critical']
      - name: total_amount
        data_tests:
          - dbt_expectations.expect_column_values_to_be_between:
              min_value: 0
              max_value: 100000
              config:
                tags: ['data_quality', 'statistical']
```

```bash
dbt test --select tag:critical        # Run only critical tests
dbt test --select tag:data_quality    # Run only data quality tests
dbt test --select fct_orders          # Run all tests for a model
```

### `store_failures` for Debugging

Persist failing rows to a table for inspection.

```yaml
      - name: customer_id
        data_tests:
          - relationships:
              to: ref('dim_customers')
              field: customer_id
              config:
                store_failures: true
                # Creates: <schema>_dbt_test__audit.relationships_fct_orders_customer_id
```

Enable globally:

```yaml
# dbt_project.yml
tests:
  my_project:
    +store_failures: true
    +schema: dbt_test_failures
```

### `limit` to Cap Failure Rows

```yaml
          - unique:
              config:
                store_failures: true
                limit: 500          # Store at most 500 failing rows
```

### Per-environment Configuration

```yaml
# Skip expensive statistical tests in dev
      - name: total_amount
        data_tests:
          - dbt_expectations.expect_column_mean_to_be_between:
              min_value: 20
              max_value: 500
              config:
                enabled: "{{ target.name != 'dev' }}"
                tags: ['statistical', 'expensive']
```

### `+meta` for Test Documentation

```yaml
      - name: order_id
        data_tests:
          - unique:
              config:
                meta:
                  owner: "data-engineering"
                  sla: "must pass within 15 min of pipeline start"
                  runbook: "https://wiki.example.com/runbooks/duplicate-orders"
```

---

## Testing Strategy by Layer

### Decision Matrix

| Layer | Required Tests | Recommended Tests | Optional Tests |
|-------|---------------|-------------------|----------------|
| **Sources** | Freshness (`loaded_at_field`) | `not_null` on PKs | `unique` on PKs |
| **Staging** | `unique` + `not_null` on PK | `accepted_values` on status cols | Relationships to other staging |
| **Intermediate** | None (tested via downstream) | `unique` + `not_null` if materialized | `expression_is_true` for logic |
| **Marts (facts)** | `unique` + `not_null` on PK, `not_null` on FKs, `relationships` | `accepted_values`, row count bounds, `recency` | Statistical, cross-table reconciliation |
| **Marts (dims)** | `unique` + `not_null` on PK | `accepted_values` on type cols, `not_null` on key attrs | Regex on formatted columns |

### Staging Layer: Minimal but Essential

```yaml
models:
  - name: stg_stripe__payments
    columns:
      - name: payment_id
        data_tests:
          - unique                 # Required: PK integrity
          - not_null               # Required: PK integrity
      - name: payment_status
        data_tests:
          - accepted_values:       # Recommended: catch schema drift
              values: ['completed', 'pending', 'failed', 'refunded']
```

### Intermediate Layer: Tested Indirectly

Intermediate models use `ephemeral` materialization by default. They are inlined as CTEs and tested through downstream mart models. Add direct tests only when materialized as a view or table.

### Marts Layer: Full Coverage

```yaml
models:
  - name: fct_orders
    data_tests:
      - dbt_expectations.expect_table_row_count_to_be_between:
          min_value: 1000
          max_value: 10000000
      - dbt_utils.recency:
          datepart: day
          field: order_date
          interval: 3
          severity: warn
    columns:
      - name: order_id
        data_tests:
          - unique
          - not_null
      - name: customer_id
        data_tests:
          - not_null
          - relationships:
              to: ref('dim_customers')
              field: customer_id
      - name: order_status
        data_tests:
          - accepted_values:
              values: ['completed', 'pending', 'cancelled', 'refunded']
      - name: total_amount
        data_tests:
          - not_null
          - dbt_expectations.expect_column_values_to_be_between:
              min_value: 0
              max_value: 100000
      - name: order_date
        data_tests:
          - not_null

  - name: dim_customers
    columns:
      - name: customer_id
        data_tests:
          - unique
          - not_null
      - name: email
        data_tests:
          - unique:
              severity: warn
          - dbt_expectations.expect_column_values_to_match_regex:
              regex: "^[a-zA-Z0-9_.+-]+@[a-zA-Z0-9-]+\\.[a-zA-Z0-9-.]+$"
              severity: warn
```

---

## Anti-patterns

### 1. Over-testing Staging

```yaml
# DON'T: Exhaustive tests on staging models
models:
  - name: stg_stripe__payments
    data_tests:
      - dbt_expectations.expect_table_row_count_to_be_between:
          min_value: 1000
          max_value: 10000000
    columns:
      - name: amount_dollars
        data_tests:
          - dbt_expectations.expect_column_mean_to_be_between:
              min_value: 10
              max_value: 500
```

```yaml
# DO: Keep staging tests focused on PK integrity — test business rules in marts
models:
  - name: stg_stripe__payments
    columns:
      - name: payment_id
        data_tests:
          - unique
          - not_null
```

**Why:** Staging is a thin cleaning layer. Row count checks and statistical tests belong on marts where data is consumed.

### 2. Skipping Mart Tests

```yaml
# DON'T: Assume upstream tests are sufficient
models:
  - name: fct_orders
    columns:
      - name: order_id
        # "It's already tested in staging" — no tests here
```

```yaml
# DO: Test independently — joins introduce duplicates and nulls
models:
  - name: fct_orders
    columns:
      - name: order_id
        data_tests:
          - unique       # LEFT JOIN can duplicate rows
          - not_null
      - name: total_amount
        data_tests:
          - not_null     # LEFT JOIN can introduce NULLs
```

**Why:** Joins change data guarantees. A LEFT JOIN introduces NULLs; a many-to-many join creates duplicates. Always re-test at the mart layer.

### 3. Testing Warehouse Functions

```sql
-- DON'T: Test that Snowflake/BigQuery functions work correctly
-- tests/assert_datediff_works.sql
select 1 where datediff('day', '2024-01-01', '2024-01-02') != 1
```

**Why:** Trust the warehouse engine. Test your transformations and business logic, not built-in functions.

### 4. Ignoring Failures / All Warnings

```yaml
# DON'T: Set everything to warn to avoid pipeline failures
      - name: order_id
        data_tests:
          - unique:
              severity: warn       # Should be error — PK violations are critical
```

```yaml
# DO: Reserve warn for soft constraints, error for hard constraints
      - name: order_id
        data_tests:
          - unique:
              severity: error      # Hard constraint — pipeline must stop
      - name: email
        data_tests:
          - unique:
              severity: warn       # Soft constraint — investigate, don't block
```

**Why:** When everything is a warning, nothing is a warning. Use `error` for anything that produces incorrect analytics if ignored.

### 5. Not Using `store_failures` When Debugging

```bash
# DON'T: Stare at "Got 47 results, configured to fail if != 0" with no context
dbt test --select fct_orders
```

```yaml
# DO: Enable store_failures to inspect actual failing rows
      - name: order_id
        data_tests:
          - unique:
              config:
                store_failures: true
```

```sql
-- Then query the failure table:
select * from dbt_test_failures.unique_fct_orders_order_id limit 100;
```

**Why:** Without `store_failures`, debugging requires re-running test queries manually. With it, failing rows are persisted for immediate inspection.

---

**Back to:** [Main Skill File](../SKILL.md)
