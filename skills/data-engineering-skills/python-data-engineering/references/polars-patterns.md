## Contents

- [LazyFrame vs Eager](#lazyframe-vs-eager)
  - [When to Use LazyFrame](#when-to-use-lazyframe)
  - [Inspecting the Query Plan](#inspecting-the-query-plan)
  - [When to Use Eager](#when-to-use-eager)
- [Aggregations](#aggregations)
- [Joins](#joins)
- [Window Functions](#window-functions)
- [Expression Patterns](#expression-patterns)
  - [Conditional Logic](#conditional-logic)
  - [String Operations](#string-operations)
  - [Date/Time Operations](#datetime-operations)
  - [List Operations](#list-operations)
  - [Null Handling](#null-handling)
- [Streaming and Large Files](#streaming-and-large-files)
  - [Streaming Collect](#streaming-collect)
  - [Scan Multiple Files](#scan-multiple-files)
  - [Sink to File (Streaming Write)](#sink-to-file-streaming-write)
- [Arrow and DuckDB Interop](#arrow-and-duckdb-interop)
  - [Arrow Zero-Copy](#arrow-zero-copy)
  - [DuckDB SQL Bridge](#duckdb-sql-bridge)
- [Performance Tuning](#performance-tuning)
  - [Dtype Optimization](#dtype-optimization)
  - [Expression Optimization](#expression-optimization)
  - [Parallel Processing](#parallel-processing)
- [Testing Patterns](#testing-patterns)

---

# Polars Patterns Reference

> Advanced Polars patterns for data engineering. Part of the [Python Data Engineering Skill](../SKILL.md).

---

## LazyFrame vs Eager

### When to Use LazyFrame

Always prefer `LazyFrame` for multi-step pipelines. The query planner optimizes execution automatically.

```python
import polars as pl

# Lazy: query planner optimizes (predicate pushdown, projection pushdown)
result = (
    pl.scan_parquet("data/*.parquet")  # LazyFrame
    .filter(pl.col("date") >= "2024-01-01")  # Pushed down to file scan
    .select("customer_id", "amount")          # Only reads needed columns
    .group_by("customer_id")
    .agg(pl.col("amount").sum())
    .collect()  # Executes optimized plan
)

# Eager: no optimization
df = pl.read_parquet("data/*.parquet")  # Loads everything
df = df.filter(pl.col("date") >= "2024-01-01")
df = df.select("customer_id", "amount")
df = df.group_by("customer_id").agg(pl.col("amount").sum())
```

### Inspecting the Query Plan

```python
lazy = (
    pl.scan_parquet("data/*.parquet")
    .filter(pl.col("amount") > 100)
    .group_by("category")
    .agg(pl.col("amount").sum())
)

# View optimized plan
print(lazy.explain())
# Shows predicate pushdown, projection, and optimization steps

# View naive plan (before optimization)
print(lazy.explain(optimized=False))
```

### When to Use Eager

- Interactive exploration in notebooks (immediate feedback)
- Very small datasets where optimization overhead isn't worth it
- When you need random access to rows by index

---

## Aggregations

```python
customer_metrics = (
    orders.lazy()
    .group_by("customer_id")
    .agg(
        pl.col("order_id").count().alias("order_count"),
        pl.col("amount").sum().alias("total_revenue"),
        pl.col("amount").mean().alias("avg_order_value"),
        pl.col("order_date").min().alias("first_order_date"),
        pl.col("order_date").max().alias("last_order_date"),
        pl.col("product_category").n_unique().alias("unique_categories"),
    )
    .sort("total_revenue", descending=True)
    .collect()
)
```

## Joins

```python
enriched_orders = (
    orders.lazy()
    .join(customers.lazy(), on="customer_id", how="left")
    .join(products.lazy(), on="product_id", how="inner")
    .join(
        regions.lazy(),
        left_on="shipping_zip", right_on="zip_code",
        how="left", suffix="_region",
    )
    .collect()
)
```

## Window Functions

```python
ranked_orders = (
    orders.lazy()
    .with_columns(
        pl.col("amount").rank(method="dense", descending=True)
        .over("customer_id").alias("amount_rank"),
        pl.col("amount").cum_sum()
        .over("customer_id").alias("cumulative_revenue"),
        pl.col("order_date").shift(1)
        .over("customer_id").alias("prev_order_date"),
        (pl.col("amount") / pl.col("amount").sum().over("customer_id"))
        .alias("pct_of_customer_total"),
    )
    .collect()
)
```

---

## Expression Patterns

### Conditional Logic

```python
df.with_columns(
    # when/then/otherwise (like SQL CASE)
    pl.when(pl.col("amount") > 1000)
    .then(pl.lit("high"))
    .when(pl.col("amount") > 100)
    .then(pl.lit("medium"))
    .otherwise(pl.lit("low"))
    .alias("tier"),

    # Coalesce
    pl.coalesce("preferred_email", "backup_email", "contact_email").alias("email"),

    # Struct field access
    pl.col("address").struct.field("city").alias("city"),
)
```

### String Operations

```python
df.with_columns(
    pl.col("name").str.to_uppercase().alias("name_upper"),
    pl.col("email").str.split("@").list.last().alias("domain"),
    pl.col("phone").str.replace_all(r"[^0-9]", "").alias("phone_clean"),
    pl.col("description").str.contains("(?i)urgent").alias("is_urgent"),
    pl.col("code").str.extract(r"([A-Z]{2})-(\d+)", group_index=1).alias("prefix"),
    pl.col("tags").str.split(",").alias("tag_list"),  # String → List
)
```

### Date/Time Operations

```python
df.with_columns(
    pl.col("created_at").dt.date().alias("created_date"),
    pl.col("created_at").dt.year().alias("year"),
    pl.col("created_at").dt.month().alias("month"),
    pl.col("created_at").dt.weekday().alias("day_of_week"),
    pl.col("created_at").dt.truncate("1mo").alias("month_start"),
    (pl.col("updated_at") - pl.col("created_at")).dt.total_hours().alias("hours_elapsed"),
    pl.col("date_str").str.to_date("%Y-%m-%d").alias("parsed_date"),
)
```

### List Operations

```python
df.with_columns(
    pl.col("tags").list.len().alias("tag_count"),
    pl.col("tags").list.contains("priority").alias("is_priority"),
    pl.col("tags").list.first().alias("primary_tag"),
    pl.col("scores").list.mean().alias("avg_score"),
    pl.col("items").list.explode().alias("item"),  # Explode to rows
)
```

### Null Handling

```python
df.with_columns(
    pl.col("amount").fill_null(0).alias("amount_clean"),
    pl.col("name").fill_null(pl.lit("Unknown")).alias("name_clean"),
    pl.col("value").fill_null(strategy="forward").alias("value_ffill"),
    pl.col("amount").is_null().alias("is_missing"),
    pl.col("amount").drop_nulls(),  # Filter rows
)
```

---

## Streaming and Large Files

### Streaming Collect

```python
# Process datasets larger than memory
result = (
    pl.scan_csv("huge_file.csv")
    .filter(pl.col("amount") > 100)
    .group_by("region")
    .agg(pl.col("amount").sum())
    .collect(streaming=True)  # Constant memory usage
)
```

### Scan Multiple Files

```python
# Glob pattern for multiple files
df = pl.scan_parquet("data/year=2024/month=*/data.parquet")

# With hive partitioning
df = pl.scan_parquet(
    "data/",
    hive_partitioning=True,  # Reads year=, month= from path
)
```

### Sink to File (Streaming Write)

```python
# Stream results directly to file without collecting in memory
(
    pl.scan_csv("input.csv")
    .filter(pl.col("status") == "active")
    .with_columns(pl.col("amount").cast(pl.Float64))
    .sink_parquet("output.parquet")  # Streams — never loads full dataset
)
```

---

## Arrow and DuckDB Interop

### Arrow Zero-Copy

```python
import pyarrow as pa
import pyarrow.parquet as pq

# Read Arrow → Polars (zero-copy)
arrow_table = pq.read_table("data.parquet")
polars_df = pl.from_arrow(arrow_table)

# Polars → Arrow (zero-copy)
arrow_table = polars_df.to_arrow()

# Write Arrow from Polars efficiently
pq.write_table(polars_df.to_arrow(), "output.parquet")
```

### DuckDB SQL Bridge

```python
import duckdb
import polars as pl

# Register Polars DataFrame and query with SQL
orders = pl.read_parquet("orders.parquet")
customers = pl.read_parquet("customers.parquet")

result = duckdb.sql("""
    SELECT
        c.customer_id,
        c.name,
        SUM(o.amount) as total_spend,
        COUNT(*) as order_count
    FROM orders o
    JOIN customers c ON o.customer_id = c.customer_id
    WHERE o.status = 'completed'
    GROUP BY c.customer_id, c.name
    HAVING SUM(o.amount) > 1000
    ORDER BY total_spend DESC
""").pl()  # Returns Polars DataFrame

# Direct file query (no loading into memory)
result = duckdb.sql("""
    SELECT * FROM read_parquet('data/*.parquet')
    WHERE date >= '2024-01-01'
""").pl()
```

---

## Performance Tuning

### Dtype Optimization

```python
# Use smallest appropriate dtype
df = pl.read_csv(
    "data.csv",
    dtypes={
        "id": pl.Int32,          # Not Int64 (saves 50% memory)
        "amount": pl.Float32,    # Not Float64 (if precision allows)
        "status": pl.Categorical,  # Not Utf8 for repeated strings
        "flag": pl.Boolean,      # Not Int8 for true/false
    },
)
```

### Expression Optimization

```python
# Good: single select with multiple expressions
df.select(
    pl.col("a") + pl.col("b"),
    pl.col("c").str.to_uppercase(),
    pl.col("d").fill_null(0),
)

# Bad: chained with_columns (each creates intermediate)
df.with_columns(pl.col("a") + pl.col("b"))
  .with_columns(pl.col("c").str.to_uppercase())
  .with_columns(pl.col("d").fill_null(0))
```

### Parallel Processing

```python
# Polars auto-parallelizes across CPU cores
# Control thread count via environment variable:
# export POLARS_MAX_THREADS=8

# Or programmatically:
pl.Config.set_max_threads(8)
```

---

## Testing Patterns

```python
import polars as pl
from polars.testing import assert_frame_equal

def test_transform_produces_correct_output():
    input_df = pl.LazyFrame({
        "id": [1, 2, 3],
        "amount": [100.0, -50.0, 200.0],
        "status": ["active", "active", "inactive"],
    })

    result = my_transform(input_df).collect()

    expected = pl.DataFrame({
        "id": [1],
        "amount": [100.0],
        "status": ["active"],
    })

    assert_frame_equal(result, expected)

def test_schema_matches():
    result = my_transform(input_df).collect()
    assert result.schema == {
        "id": pl.Int64,
        "amount": pl.Float64,
        "status": pl.Utf8,
    }
```
