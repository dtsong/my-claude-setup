---
name: python-data-engineering
description: "Use this skill when writing Python code for data pipelines or transformations. Covers Polars, Pandas, PySpark DataFrames, dbt Python models, API extraction scripts, and data validation with Pydantic or Pandera. Common phrases: \"Polars vs Pandas\", \"PySpark DataFrame\", \"validate this data\", \"Python extraction script\". Do NOT use for SQL-based dbt models (use dbt-transforms) or integration architecture (use data-integration)."
model:
  preferred: sonnet
  acceptable: [sonnet, opus]
  minimum: sonnet
  allow_downgrade: false
  reasoning_demand: medium
version: 1.0.0
---

# Python Data Engineering Skill

Expert guidance for Python data engineering: DataFrame libraries (Polars, Pandas, PySpark), dbt Python models, API extraction, and data validation. Assumes Python proficiency.

## Scope Constraints

- SQL transforms in dbt: hand off to `dbt-transforms`
- DLT pipeline config: hand off to `data-integration`
- Kafka/Flink streaming: hand off to `event-streaming`
- Dagster/Airflow orchestration: hand off to `data-pipelines`
- General Python or web development: out of scope

## When to Use

Activate when: choosing between DataFrame libraries, writing Polars/Pandas/PySpark transforms, building dbt Python models, building API extraction scripts, implementing data validation (Pydantic/Pandera/GX), optimizing DataFrame memory, or converting between DataFrame formats.

## Model Routing

| reasoning_demand | preferred | acceptable | minimum |
|-----------------|-----------|------------|---------|
| medium | Sonnet | Sonnet, Opus | Sonnet |

## Core Principles

### 1. Type Safety First

Annotate all functions. Data pipelines process untrusted data — types catch errors before production.

```python
from pydantic import BaseModel
from datetime import date
from decimal import Decimal
import polars as pl

class Order(BaseModel):
    order_id: str
    customer_id: str
    amount: Decimal
    order_date: date

def transform_orders(raw: pl.LazyFrame) -> pl.LazyFrame:
    return (
        raw.filter(pl.col("amount") > 0)
        .with_columns(
            pl.col("order_date").str.to_date("%Y-%m-%d"),
            pl.col("amount").cast(pl.Decimal(10, 2)),
        )
        .unique(subset=["order_id"])
    )
```

### 2. Immutable Transforms

Never mutate DataFrames in place. Return new DataFrames from every transformation for reproducibility and testability.

### 3. Lazy Evaluation When Possible

Prefer lazy evaluation (Polars `LazyFrame`, Spark DataFrame).

### 4. Memory Efficiency

Use appropriate dtypes (`Int32` not `Int64` when range allows). Stream/scan instead of loading entire files. Prefer columnar formats (Parquet, Arrow) over CSV/JSON.

### 5. Test Data Pipelines

Test transforms with small, representative fixtures. Use `polars.testing.assert_frame_equal` or `pandas.testing.assert_frame_equal`.

---

## DataFrame Library Decision Matrix

| Factor | Polars | Pandas | PySpark | DuckDB (Python) |
|--------|--------|--------|---------|-----------------|
| **Data size** | Single machine (GB-TB via streaming) | Single machine (MB-GB) | Distributed cluster (TB-PB) | Single machine (GB-TB) |
| **Speed** | Very fast (Rust, multi-threaded) | Moderate (single-threaded) | Fast at scale (distributed) | Very fast (vectorized) |
| **Memory** | Efficient (Arrow-native, streaming) | Inefficient (copies, object dtype) | Efficient (distributed) | Efficient (out-of-core) |
| **API style** | Expression-based, method chaining | Index-based, mixed paradigms | SQL-like DataFrame API | SQL-first, DataFrame bridge |
| **Lazy eval** | Yes (LazyFrame) | No (eager only) | Yes (execution plan) | Yes (query plan) |
| **dbt support** | Via DataFrame return | Native (`dbt-core`) | Via `dbt-spark` | Via `dbt-duckdb` |
| **Best for** | New projects, performance-critical | Legacy code, ML integration | Big data, Databricks | Analytics, local dev |

---

## Polars (Primary)

```python
import polars as pl

orders = (
    pl.scan_parquet("raw/orders/*.parquet")
    .filter(
        (pl.col("status").is_in(["completed", "shipped"]))
        & (pl.col("amount") > 0)
    )
    .with_columns(
        pl.col("order_date").str.to_date("%Y-%m-%d").alias("order_date_parsed"),
        pl.col("amount").cast(pl.Decimal(10, 2)),
        (pl.col("amount") * pl.col("tax_rate")).round(2).alias("tax_amount"),
    )
    .rename({"order_date_parsed": "order_date"})
    .unique(subset=["order_id"])
    .sort("order_date")
    .collect()
)
```

For aggregations, joins, window functions, streaming, Arrow interop, DuckDB bridge, and performance tuning, see [Polars Patterns Reference](references/polars-patterns.md).

## Pandas (Legacy/Compatibility)

Use when integrating with ML libraries or maintaining existing codebases. Prefer method chaining and vectorized operations.

For method chaining, Arrow backend, memory optimization, chunked processing, and anti-patterns, see [Pandas Patterns Reference](references/pandas-patterns.md).

## PySpark (Distributed)

Use when data exceeds single-machine memory or running on Databricks/Spark infrastructure.

For DataFrame API, Pandas UDFs, Spark Connect, Delta Lake, partitioning, and caching, see [PySpark Patterns Reference](references/pyspark-patterns.md).

---

## dbt Python Models

Use Python models for transforms difficult in SQL: complex statistics, ML scoring, API calls, complex string parsing, or external library integration. Use SQL for joins, filters, aggregations, window functions, CTEs, and standard ELT.

```python
# models/intermediate/int_customer_rfm.py
def model(dbt, session):
    """RFM scoring — requires Pandas groupby + qcut."""
    dbt.config(materialized="table", packages=["scikit-learn==1.4.0"])
    orders = dbt.ref("stg_orders").to_pandas()
    # ... transform with Pandas/sklearn, return DataFrame
    return result  # dbt writes to warehouse automatically
```

On Snowflake, `session` is a Snowpark Session and `dbt.ref()` returns a Snowpark DataFrame (not Pandas).

---

## API Extraction

Build typed clients with Pydantic models, pagination, retry (tenacity), and rate limiting. Use `httpx` for sync/async HTTP.

For typed client patterns, pagination (cursor/offset/link-header), rate limiting, async extraction, and complete pipeline examples, see [Extraction Patterns Reference](references/extraction-patterns.md).

## Data Validation

- **Pydantic** for row-level validation (API responses, individual records)
- **Pandera** for DataFrame-level validation (column types, constraints)
- **Great Expectations** for suite-level validation (warehouse tables, CI gates)
- **dbt tests** for model-level assertions in dbt projects

For Pydantic v2 patterns, Pandera schemas, Great Expectations checkpoints, and contract testing, see [Data Validation Patterns Reference](references/data-validation-patterns.md).

---

## DataFrame Interoperability

| Conversion | Method | Notes |
|-----------|--------|-------|
| Polars -> Pandas | `polars_df.to_pandas()` | Copies data |
| Pandas -> Polars | `pl.from_pandas(df)` | Zero-copy when possible |
| Polars <-> Arrow | `to_arrow()` / `pl.from_arrow()` | Zero-copy |
| Polars <-> DuckDB | `duckdb.sql("SELECT ... FROM df").pl()` | Zero-copy via Arrow |
| Spark -> Pandas | `spark_df.toPandas()` | Pulls to driver; use `limit()` for large data |
| Pandas -> Spark | `spark.createDataFrame(df)` | Enable Arrow: `spark.sql.execution.arrow.pyspark.enabled=true` |

---

## Security

Credentials: always `os.environ["KEY"]`, never inline. Document required vars in `.env.example`. Use connection strings from env vars. Close httpx clients in `finally` blocks. Never store credentials in notebook cells.

See [Security & Compliance Patterns](../shared-references/data-engineering/security-compliance-patterns.md) for the full framework including security tiers.

---

## Reference Files

- [Polars Patterns](references/polars-patterns.md) — LazyFrame, expressions, aggregations, joins, windows, streaming, Arrow interop, performance
- [Pandas Patterns](references/pandas-patterns.md) — Arrow backend, method chaining, memory optimization, anti-patterns
- [PySpark Patterns](references/pyspark-patterns.md) — DataFrame API, Pandas UDFs, Spark Connect, Delta Lake, Databricks
- [Data Validation Patterns](references/data-validation-patterns.md) — Pydantic v2, Pandera, Great Expectations, contract testing
- [Extraction Patterns](references/extraction-patterns.md) — httpx clients, async extraction, pagination, rate limiting, retry
