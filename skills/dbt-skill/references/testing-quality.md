# Testing & Quality Strategy

## Schema Tests (YAML-based)

Four built-in tests: `unique`, `not_null`, `accepted_values`, `relationships`.

```yaml
models:
  - name: fct_orders
    columns:
      - name: order_id
        data_tests: [unique, not_null]
      - name: order_status
        data_tests:
          - accepted_values:
              values: ['completed', 'pending', 'cancelled', 'refunded']
      - name: customer_id
        data_tests:
          - not_null:
              where: "order_status != 'draft'"
          - relationships:
              to: ref('dim_customers')
              field: customer_id
```

**Config options:** `severity: warn|error`, `where` filter, `store_failures: true`, `limit`, `tags`, `enabled: "{{ target.name != 'dev' }}"`.

**Compound uniqueness:** `dbt_utils.unique_combination_of_columns` with `combination_of_columns` list.

## Singular Tests

Standalone SQL files in `tests/`. Query must return zero rows to pass. Prefix with `assert_`.

Use for: business rules specific to one model, cross-table reconciliation, complex multi-step validation.

```sql
-- tests/assert_payment_revenue_matches_orders.sql
with order_totals as (
    select sum(total_amount) as total from {{ ref('fct_orders') }} where order_status = 'completed'
),
payment_totals as (
    select sum(amount_dollars) as total from {{ ref('stg_stripe__payments') }} where payment_status = 'completed'
)
select * from order_totals cross join payment_totals
where abs(order_totals.total - payment_totals.total) > 1.00
```

## Generic Tests

Reusable test macros in `tests/generic/`. Apply in YAML like built-in tests.

```sql
-- tests/generic/is_positive.sql
{% test is_positive(model, column_name) %}
select {{ column_name }} from {{ model }} where {{ column_name }} < 0
{% endtest %}
```

Use for: reusable patterns, parameterized checks, standard data quality.

## Unit Tests (dbt 1.8+)

Mock inputs, assert expected outputs. Validate transformation logic without querying the warehouse.

```yaml
unit_tests:
  - name: test_tiered_discount_logic
    model: int_orders_with_discount
    given:
      - input: ref('stg_shopify__orders')
        rows:
          - { order_id: 1, customer_id: 100, subtotal: 600.00 }
          - { order_id: 2, customer_id: 101, subtotal: 300.00 }
    expect:
      rows:
        - { order_id: 1, discount_amount: 60.00, total_after_discount: 540.00 }
        - { order_id: 2, discount_amount: 15.00, total_after_discount: 285.00 }
```

Use for: complex CASE/WHEN logic, multi-step calculations, Jinja conditional paths. Skip for: simple renames, incremental merge behavior, warehouse functions.

## dbt-expectations (Top Tests)

- `expect_column_values_to_be_between`: numeric range with `row_condition`
- `expect_table_row_count_to_be_between`: catch catastrophic data drops
- `expect_column_values_to_be_in_set`: accepted values with filtering
- `expect_column_distinct_count_to_equal`: catch silent schema drift
- `expect_column_values_to_match_regex`: string format validation
- `expect_column_mean_to_be_between`: statistical guardrail
- `expect_table_row_count_to_equal_other_table`: migration validation

## dbt-utils Testing Helpers

- `equal_rowcount`: assert same row count between two models
- `fewer_rows_than`: assert relational cardinality (customers < orders)
- `not_accepted_values`: ensure test data never leaks to prod
- `expression_is_true`: assert any SQL expression for all rows
- `recency`: assert most recent record within time window

## Testing Strategy by Layer

| Layer | Required | Recommended | Optional |
|-------|----------|-------------|----------|
| Sources | Freshness | `not_null` on PKs | `unique` on PKs |
| Staging | `unique` + `not_null` on PK | `accepted_values` on status cols | Relationships |
| Intermediate | None (tested downstream) | Tests if materialized | `expression_is_true` |
| Marts (facts) | PK tests, FK not_null, relationships | accepted_values, row count, recency | Statistical, reconciliation |
| Marts (dims) | PK tests | accepted_values on types, not_null on key attrs | Regex on formatted cols |

## Anti-patterns

- **Over-testing staging:** Keep staging tests focused on PK integrity. Statistical and row count tests belong on marts.
- **Skipping mart tests:** Joins introduce duplicates and nulls. Always re-test at mart layer.
- **All warnings:** Reserve `warn` for soft constraints, `error` for hard constraints. When everything warns, nothing warns.
- **No store_failures:** Enable `store_failures: true` to inspect actual failing rows instead of opaque error counts.
