## Contents

- [Spark Session Configuration](#spark-session-configuration)
- [DataFrame API Patterns](#dataframe-api-patterns)
  - [Reading Data](#reading-data)
  - [Transforms](#transforms)
- [Pandas UDFs (Preferred Over Regular UDFs)](#pandas-udfs-preferred-over-regular-udfs)
  - [Scalar Pandas UDF](#scalar-pandas-udf)
  - [Grouped Map Pandas UDF](#grouped-map-pandas-udf)
- [Partitioning and Writing](#partitioning-and-writing)
  - [Write with Partitioning](#write-with-partitioning)
  - [File Size Control](#file-size-control)
- [Delta Lake Patterns (Databricks)](#delta-lake-patterns-databricks)
  - [MERGE (Upsert)](#merge-upsert)
  - [Time Travel](#time-travel)
  - [Optimize and Z-Order](#optimize-and-z-order)
- [Spark Connect (Remote Client)](#spark-connect-remote-client)
- [Caching Strategies](#caching-strategies)
- [Databricks Patterns](#databricks-patterns)
  - [Unity Catalog](#unity-catalog)
  - [Databricks Widgets (Parameterized Notebooks)](#databricks-widgets-parameterized-notebooks)
- [Testing PySpark](#testing-pyspark)
- [Troubleshooting](#troubleshooting)

---

# PySpark Patterns Reference

> Production PySpark patterns for distributed data engineering. Part of the [Python Data Engineering Skill](../SKILL.md).

---

## Spark Session Configuration

```python
from pyspark.sql import SparkSession

# ── Credential boundary ──────────────────────────────────────────────
# Spark reads credentials from environment or cluster configuration.
# For S3: configure via IAM role (preferred) or env vars.
# For warehouses: use JDBC connection strings from environment.
# Never inline credentials — use environment variables or secrets manager.
# ─────────────────────────────────────────────────────────────────────

spark = (
    SparkSession.builder
    .appName("orders_pipeline")
    .config("spark.sql.adaptive.enabled", "true")        # Adaptive query execution
    .config("spark.sql.adaptive.coalescePartitions.enabled", "true")
    .config("spark.sql.execution.arrow.pyspark.enabled", "true")  # Fast Pandas ↔ Spark
    .config("spark.serializer", "org.apache.spark.serializer.KryoSerializer")
    .getOrCreate()
)
```

---

## DataFrame API Patterns

### Reading Data

```python
# Parquet (preferred format)
orders = spark.read.parquet("s3://data-lake/raw/orders/")

# CSV with schema enforcement
from pyspark.sql.types import StructType, StructField, StringType, DoubleType, DateType

schema = StructType([
    StructField("order_id", StringType(), nullable=False),
    StructField("customer_id", StringType(), nullable=False),
    StructField("amount", DoubleType(), nullable=False),
    StructField("order_date", DateType(), nullable=True),
])

orders = spark.read.csv(
    "s3://data-lake/raw/orders.csv",
    header=True,
    schema=schema,  # Enforce schema (faster than inferSchema=True)
)

# Delta Lake (Databricks)
orders = spark.read.format("delta").load("s3://data-lake/delta/orders/")
```

### Transforms

```python
from pyspark.sql import functions as F
from pyspark.sql.window import Window

# Filter, transform, deduplicate
clean_orders = (
    orders
    .filter(F.col("amount") > 0)
    .filter(F.col("status").isin("completed", "shipped"))
    .withColumn("order_date", F.to_date("order_date_str", "yyyy-MM-dd"))
    .withColumn("year_month", F.date_format("order_date", "yyyy-MM"))
    .withColumn("tax_amount", F.round(F.col("amount") * F.col("tax_rate"), 2))
    .dropDuplicates(["order_id"])
)

# Window functions
window_spec = Window.partitionBy("customer_id").orderBy("order_date")

enriched = (
    clean_orders
    .withColumn("order_number", F.row_number().over(window_spec))
    .withColumn("cumulative_amount", F.sum("amount").over(window_spec))
    .withColumn("prev_order_date", F.lag("order_date", 1).over(window_spec))
    .withColumn(
        "days_since_prev",
        F.datediff("order_date", "prev_order_date"),
    )
)

# Aggregation
customer_metrics = (
    clean_orders
    .groupBy("customer_id")
    .agg(
        F.count("order_id").alias("order_count"),
        F.sum("amount").alias("total_revenue"),
        F.avg("amount").alias("avg_order_value"),
        F.min("order_date").alias("first_order"),
        F.max("order_date").alias("last_order"),
        F.countDistinct("product_id").alias("unique_products"),
    )
)
```

---

## Pandas UDFs (Preferred Over Regular UDFs)

Regular Python UDFs serialize row-by-row. Pandas UDFs process Arrow batches and are 10-100x faster.

### Scalar Pandas UDF

```python
from pyspark.sql.functions import pandas_udf
from pyspark.sql.types import DoubleType
import pandas as pd

@pandas_udf(DoubleType())
def normalize(values: pd.Series) -> pd.Series:
    """Normalize values to 0-1 range."""
    min_val, max_val = values.min(), values.max()
    if max_val == min_val:
        return pd.Series([0.5] * len(values))
    return (values - min_val) / (max_val - min_val)

df = df.withColumn("amount_normalized", normalize("amount"))
```

### Grouped Map Pandas UDF

```python
from pyspark.sql.functions import pandas_udf, PandasUDFType

@pandas_udf(schema, PandasUDFType.GROUPED_MAP)
def fit_model_per_group(pdf: pd.DataFrame) -> pd.DataFrame:
    """Fit a model per customer group."""
    from sklearn.linear_model import LinearRegression
    import numpy as np

    X = pdf[["days_active", "order_count"]].values
    y = pdf["total_spend"].values

    model = LinearRegression().fit(X, y)
    pdf["predicted_spend"] = model.predict(X)
    pdf["residual"] = y - pdf["predicted_spend"]

    return pdf

result = df.groupBy("segment").applyInPandas(fit_model_per_group, schema=df.schema)
```

---

## Partitioning and Writing

### Write with Partitioning

```python
# Partition by date for efficient reads
(
    clean_orders
    .repartition("order_date")      # Redistribute data by partition column
    .write
    .partitionBy("order_date")      # Physical directory partitioning
    .mode("overwrite")
    .parquet("s3://data-lake/processed/orders/")
)

# Partition by year/month for coarser granularity
(
    clean_orders
    .withColumn("year", F.year("order_date"))
    .withColumn("month", F.month("order_date"))
    .repartition("year", "month")
    .write
    .partitionBy("year", "month")
    .mode("overwrite")
    .parquet("s3://data-lake/processed/orders/")
)
```

### File Size Control

```python
# Control output file count (avoid small files problem)
(
    df
    .coalesce(10)  # Reduce to 10 output files (no shuffle)
    .write
    .parquet("s3://output/")
)

# Or repartition for even distribution (with shuffle)
(
    df
    .repartition(20)  # Exactly 20 output files
    .write
    .parquet("s3://output/")
)

# Target file size (Spark 3.x AQE)
spark.conf.set("spark.sql.adaptive.advisoryPartitionSizeInBytes", "128MB")
```

---

## Delta Lake Patterns (Databricks)

### MERGE (Upsert)

```python
from delta.tables import DeltaTable

target = DeltaTable.forPath(spark, "s3://data-lake/delta/customers/")

(
    target.alias("target")
    .merge(
        source=new_customers.alias("source"),
        condition="target.customer_id = source.customer_id",
    )
    .whenMatchedUpdate(set={
        "name": "source.name",
        "email": "source.email",
        "updated_at": "current_timestamp()",
    })
    .whenNotMatchedInsert(values={
        "customer_id": "source.customer_id",
        "name": "source.name",
        "email": "source.email",
        "created_at": "current_timestamp()",
        "updated_at": "current_timestamp()",
    })
    .execute()
)
```

### Time Travel

```python
# Read historical version
old_data = spark.read.format("delta").option("versionAsOf", 5).load(path)

# Read as of timestamp
snapshot = spark.read.format("delta").option("timestampAsOf", "2024-01-01").load(path)

# Show history
delta_table = DeltaTable.forPath(spark, path)
delta_table.history().show()
```

### Optimize and Z-Order

```python
# Compact small files
delta_table.optimize().executeCompaction()

# Z-order for multi-dimensional query efficiency
delta_table.optimize().executeZOrderBy("customer_id", "order_date")

# Vacuum old versions (retain 7 days by default)
delta_table.vacuum(retentionHours=168)
```

---

## Spark Connect (Remote Client)

Spark Connect (Spark 3.4+) lets you run Spark from a thin Python client without a local JVM.

```python
from pyspark.sql import SparkSession

# Connect to remote Spark cluster
spark = SparkSession.builder.remote("sc://cluster-host:15002").getOrCreate()

# Use normally — API is identical
df = spark.read.parquet("s3://data-lake/orders/")
result = df.groupBy("category").agg(F.sum("amount"))
result.show()
```

---

## Caching Strategies

```python
# Cache when DataFrame is used multiple times
orders = spark.read.parquet("s3://data-lake/orders/")
orders.cache()  # Cache in memory
orders.count()  # Trigger caching

# Use orders multiple times efficiently
high_value = orders.filter(F.col("amount") > 1000)
low_value = orders.filter(F.col("amount") <= 1000)

# Unpersist when done
orders.unpersist()

# Persist with storage level for large datasets
from pyspark import StorageLevel
orders.persist(StorageLevel.MEMORY_AND_DISK)  # Spill to disk if needed
```

---

## Databricks Patterns

### Unity Catalog

```python
# Read from Unity Catalog
df = spark.table("catalog.schema.table_name")

# Write to Unity Catalog
df.write.mode("overwrite").saveAsTable("catalog.schema.output_table")

# Create managed table
spark.sql("""
    CREATE TABLE IF NOT EXISTS catalog.schema.customers (
        customer_id STRING NOT NULL,
        name STRING,
        email STRING
    )
    USING DELTA
    COMMENT 'Customer dimension table'
""")
```

### Databricks Widgets (Parameterized Notebooks)

```python
# Define parameters
dbutils.widgets.text("start_date", "2024-01-01")
dbutils.widgets.dropdown("environment", "dev", ["dev", "staging", "prod"])

# Use parameters
start_date = dbutils.widgets.get("start_date")
env = dbutils.widgets.get("environment")

df = spark.read.parquet(f"s3://data-lake-{env}/orders/")
df = df.filter(F.col("order_date") >= start_date)
```

---

## Testing PySpark

```python
import pytest
from pyspark.sql import SparkSession

@pytest.fixture(scope="session")
def spark():
    """Create a test Spark session."""
    return (
        SparkSession.builder
        .master("local[2]")
        .appName("tests")
        .config("spark.sql.shuffle.partitions", "2")  # Faster for tests
        .getOrCreate()
    )

def test_order_transform(spark):
    input_data = [
        ("A", 100.0, "completed"),
        ("B", -50.0, "completed"),
        ("C", 200.0, "cancelled"),
    ]
    df = spark.createDataFrame(input_data, ["order_id", "amount", "status"])

    result = transform_orders(df)

    assert result.count() == 1  # Only A: positive + completed
    assert result.first()["order_id"] == "A"

def test_schema(spark):
    result = transform_orders(input_df)
    assert "order_id" in result.columns
    assert result.schema["amount"].dataType.typeName() == "double"
```

---

## Troubleshooting

| Issue | Cause | Fix |
|-------|-------|-----|
| OOM on driver | `toPandas()` on large DataFrame | Use `limit()` or write to storage instead |
| Slow UDFs | Row-by-row Python UDFs | Switch to Pandas UDFs |
| Small files problem | Too many partitions | `coalesce()` or AQE adaptive coalescing |
| Shuffle spill | Insufficient memory per executor | Increase `spark.executor.memory` or reduce shuffle |
| Skewed partitions | One key has most data | Salting: add random prefix to join key |
| Slow joins | Missing partition pruning | Filter before join, broadcast small tables |
