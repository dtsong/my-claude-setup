## Contents

- [Pandas 2.0+ Arrow Backend](#pandas-20-arrow-backend)
- [Method Chaining (Preferred Style)](#method-chaining-preferred-style)
  - [Basic Chain](#basic-chain)
  - [Using pipe() for Custom Steps](#using-pipe-for-custom-steps)
  - [GroupBy with Named Aggregations](#groupby-with-named-aggregations)
- [Memory Optimization](#memory-optimization)
  - [Dtype Selection](#dtype-selection)
  - [Chunked Reading](#chunked-reading)
  - [Memory Profiling](#memory-profiling)
- [Anti-Patterns to Avoid](#anti-patterns-to-avoid)
  - [Iterating Over Rows](#iterating-over-rows)
  - [Chained Indexing](#chained-indexing)
  - [Growing DataFrames in Loops](#growing-dataframes-in-loops)
  - [Using apply() When Vectorized Options Exist](#using-apply-when-vectorized-options-exist)
- [Pandas / Polars Migration](#pandas--polars-migration)
- [Testing Patterns](#testing-patterns)

---

# Pandas Patterns Reference

> Modern Pandas patterns for data engineering. Part of the [Python Data Engineering Skill](../SKILL.md).

---

## Pandas 2.0+ Arrow Backend

Pandas 2.0 introduced an Apache Arrow backend that significantly improves performance and memory efficiency. Use it for new projects.

```python
import pandas as pd

# Read with Arrow backend (faster, better dtypes)
df = pd.read_parquet("data.parquet", dtype_backend="pyarrow")

# Convert existing DataFrame to Arrow-backed
df = df.convert_dtypes(dtype_backend="pyarrow")

# Check dtypes
print(df.dtypes)
# customer_id    string[pyarrow]
# amount         double[pyarrow]
# order_date     timestamp[ns][pyarrow]
```

**Benefits of Arrow backend:**

| Feature | Default (NumPy) | Arrow Backend |
|---------|-----------------|---------------|
| Null handling | NaN (float only) | Native NA (all types) |
| String dtype | object (slow) | string[pyarrow] (fast) |
| Memory usage | Higher (copies) | Lower (zero-copy) |
| Type consistency | Mixed nullability | Consistent nullable types |
| Interop with Polars/Arrow | Conversion needed | Near zero-copy |

---

## Method Chaining (Preferred Style)

Method chaining produces readable, functional-style pipelines.

### Basic Chain

```python
result = (
    pd.read_parquet("orders.parquet", dtype_backend="pyarrow")
    .query("status in ['completed', 'shipped'] and amount > 0")
    .assign(
        order_date=lambda df: pd.to_datetime(df["order_date"]),
        tax_amount=lambda df: (df["amount"] * df["tax_rate"]).round(2),
        year_month=lambda df: df["order_date"].dt.to_period("M"),
    )
    .drop(columns=["raw_timestamp", "internal_id"])
    .drop_duplicates(subset=["order_id"])
    .sort_values("order_date")
    .reset_index(drop=True)
)
```

### Using `pipe()` for Custom Steps

```python
def filter_active_customers(df: pd.DataFrame) -> pd.DataFrame:
    """Filter to customers with orders in the last 90 days."""
    cutoff = pd.Timestamp.now() - pd.Timedelta(days=90)
    return df.query("last_order_date >= @cutoff")

def add_customer_tier(df: pd.DataFrame) -> pd.DataFrame:
    """Assign customer tier based on total spend."""
    return df.assign(
        tier=pd.cut(
            df["total_spend"],
            bins=[0, 100, 1000, float("inf")],
            labels=["bronze", "silver", "gold"],
        )
    )

result = (
    customers
    .pipe(filter_active_customers)
    .pipe(add_customer_tier)
    .sort_values("total_spend", ascending=False)
)
```

### GroupBy with Named Aggregations

```python
customer_metrics = (
    orders
    .groupby("customer_id", as_index=False)
    .agg(
        order_count=("order_id", "nunique"),
        total_revenue=("amount", "sum"),
        avg_order=("amount", "mean"),
        first_order=("order_date", "min"),
        last_order=("order_date", "max"),
        unique_products=("product_id", "nunique"),
    )
)
```

---

## Memory Optimization

### Dtype Selection

```python
# Before: 1.2 GB
df = pd.read_csv("large_file.csv")
print(df.memory_usage(deep=True).sum() / 1e9)  # 1.2 GB

# After: 0.3 GB
optimized_dtypes = {
    "id": "int32",              # int64 → int32 (50% savings)
    "amount": "float32",        # float64 → float32 (50% savings)
    "status": "category",       # object → category (90%+ savings for repeated strings)
    "country_code": "category",
    "is_active": "bool",        # object → bool
}
df = pd.read_csv("large_file.csv", dtype=optimized_dtypes)
print(df.memory_usage(deep=True).sum() / 1e9)  # 0.3 GB
```

### Chunked Reading

```python
# Process large files in chunks
def process_large_csv(path: str, chunksize: int = 100_000) -> pd.DataFrame:
    """Process CSV file in chunks — constant memory usage."""
    chunks = []
    for chunk in pd.read_csv(path, chunksize=chunksize, dtype=optimized_dtypes):
        processed = (
            chunk
            .query("amount > 0")
            .groupby("category", as_index=False)
            .agg(total=("amount", "sum"), count=("id", "count"))
        )
        chunks.append(processed)

    return (
        pd.concat(chunks)
        .groupby("category", as_index=False)
        .agg(total=("total", "sum"), count=("count", "sum"))
    )
```

### Memory Profiling

```python
# Check memory usage per column
print(df.memory_usage(deep=True).sort_values(ascending=False))

# Find object columns (usually the biggest memory hogs)
object_cols = df.select_dtypes(include=["object"]).columns
for col in object_cols:
    n_unique = df[col].nunique()
    n_total = len(df)
    ratio = n_unique / n_total
    print(f"{col}: {n_unique} unique / {n_total} total ({ratio:.2%})")
    if ratio < 0.5:
        print(f"  → Convert to category (saves ~{(1 - ratio) * 100:.0f}% memory)")
```

---

## Anti-Patterns to Avoid

### Iterating Over Rows

```python
# BAD: iterrows (extremely slow)
for idx, row in df.iterrows():
    df.at[idx, "total"] = row["price"] * row["quantity"]

# GOOD: vectorized (100-1000x faster)
df["total"] = df["price"] * df["quantity"]
```

### Chained Indexing

```python
# BAD: chained indexing (SettingWithCopyWarning, unreliable)
df[df["status"] == "active"]["amount"] = 0

# GOOD: .loc accessor
df.loc[df["status"] == "active", "amount"] = 0
```

### Growing DataFrames in Loops

```python
# BAD: append in loop (quadratic complexity)
result = pd.DataFrame()
for item in items:
    row = process(item)
    result = pd.concat([result, pd.DataFrame([row])])

# GOOD: collect list, then create DataFrame
rows = [process(item) for item in items]
result = pd.DataFrame(rows)
```

### Using `apply()` When Vectorized Options Exist

```python
# BAD: apply with lambda (slow, row-by-row)
df["discount"] = df.apply(lambda row: row["amount"] * 0.1 if row["is_vip"] else 0, axis=1)

# GOOD: vectorized with np.where or pandas where
df["discount"] = np.where(df["is_vip"], df["amount"] * 0.1, 0)

# GOOD: vectorized with pandas
df["discount"] = df["amount"].where(df["is_vip"], 0) * 0.1
```

---

## Pandas ↔ Polars Migration

| Pandas | Polars |
|--------|--------|
| `df[df["col"] > 0]` | `df.filter(pl.col("col") > 0)` |
| `df["new"] = df["a"] + df["b"]` | `df.with_columns((pl.col("a") + pl.col("b")).alias("new"))` |
| `df.groupby("col").agg({"val": "sum"})` | `df.group_by("col").agg(pl.col("val").sum())` |
| `df.merge(other, on="id")` | `df.join(other, on="id")` |
| `df.sort_values("col")` | `df.sort("col")` |
| `df.drop_duplicates()` | `df.unique()` |
| `df.rename(columns={"a": "b"})` | `df.rename({"a": "b"})` |
| `df.apply(func, axis=1)` | `df.with_columns(pl.struct(...).map_elements(func))` |
| `pd.read_csv("f.csv")` | `pl.read_csv("f.csv")` or `pl.scan_csv("f.csv")` |

---

## Testing Patterns

```python
import pandas as pd
from pandas.testing import assert_frame_equal

def test_transform_output():
    input_df = pd.DataFrame({
        "id": [1, 2, 3],
        "amount": [100.0, -50.0, 200.0],
    })

    result = my_transform(input_df)

    expected = pd.DataFrame({
        "id": [1, 3],
        "amount": [100.0, 200.0],
    })

    assert_frame_equal(result.reset_index(drop=True), expected)

def test_dtypes_preserved():
    result = my_transform(input_df)
    assert result["amount"].dtype == "float64"
    assert result["id"].dtype == "int64"
```
