## Contents

- [Validation Strategy](#validation-strategy)
- [Pydantic v2 Patterns](#pydantic-v2-patterns)
- [Pandera Patterns](#pandera-patterns)
- [Great Expectations Patterns](#great-expectations-patterns)
- [Contract Testing](#contract-testing)
- [Validation Decision Tree](#validation-decision-tree)

---

# Data Validation Patterns Reference

> Production data validation with Pydantic, Pandera, and Great Expectations. Part of the [Python Data Engineering Skill](../SKILL.md).

---

## Validation Strategy

### Which Tool When

| Tool | Level | Best For | Overhead |
|------|-------|----------|----------|
| **Pydantic** | Row-level | API responses, config, individual records | Low |
| **Pandera** | DataFrame-level | Column types, constraints, statistical checks | Low-Medium |
| **Great Expectations** | Suite-level | Warehouse tables, cross-table checks, CI gates | Medium-High |
| **dbt tests** | Model-level | SQL-based assertions in dbt projects | Low |

**Rule of thumb:**
- Validating API responses or config → Pydantic
- Validating DataFrames in Python transforms → Pandera
- Validating warehouse tables in CI/CD → Great Expectations or dbt tests
- In a dbt project → dbt tests (native, no extra tooling)

---

## Pydantic v2 Patterns

### Strict vs Lax Mode

```python
from pydantic import BaseModel, ConfigDict

class StrictOrder(BaseModel):
    """Strict mode: no type coercion."""
    model_config = ConfigDict(strict=True)

    order_id: str
    amount: float  # "100" would FAIL (must be float)

class LaxOrder(BaseModel):
    """Lax mode (default): auto-coerce types."""
    order_id: str
    amount: float  # "100" → 100.0 (auto-coerced)
```

### Custom Validators

```python
from pydantic import BaseModel, field_validator, model_validator
from datetime import date
from typing import Optional

class CustomerRecord(BaseModel):
    customer_id: str
    email: str
    signup_date: date
    churn_date: Optional[date] = None
    lifetime_value: float

    @field_validator("email")
    @classmethod
    def email_valid(cls, v: str) -> str:
        if "@" not in v or "." not in v.split("@")[1]:
            raise ValueError("Invalid email format")
        return v.lower().strip()

    @field_validator("lifetime_value")
    @classmethod
    def ltv_non_negative(cls, v: float) -> float:
        if v < 0:
            raise ValueError("Lifetime value cannot be negative")
        return round(v, 2)

    @model_validator(mode="after")
    def churn_after_signup(self):
        if self.churn_date and self.churn_date < self.signup_date:
            raise ValueError("Churn date cannot be before signup date")
        return self
```

### Batch Validation with Error Collection

```python
from pydantic import BaseModel, ValidationError
from typing import TypeVar, Type
import polars as pl

T = TypeVar("T", bound=BaseModel)

def validate_batch(
    records: list[dict],
    model: Type[T],
) -> tuple[list[T], list[dict]]:
    """Validate a batch of records, collecting errors."""
    valid, errors = [], []
    for i, record in enumerate(records):
        try:
            valid.append(model.model_validate(record))
        except ValidationError as e:
            errors.append({
                "row_index": i,
                "record": record,
                "errors": e.errors(),
            })
    return valid, errors

def validate_and_report(
    records: list[dict],
    model: Type[T],
    error_threshold: float = 0.05,
) -> list[T]:
    """Validate batch, raise if error rate exceeds threshold."""
    valid, errors = validate_batch(records, model)
    error_rate = len(errors) / len(records) if records else 0

    if error_rate > error_threshold:
        raise ValueError(
            f"Error rate {error_rate:.1%} exceeds threshold {error_threshold:.1%}. "
            f"{len(errors)} of {len(records)} records failed validation."
        )

    if errors:
        # Log errors for investigation but continue
        save_to_dead_letter_queue(errors)

    return valid
```

### Pydantic for Config Validation

```python
from pydantic import BaseModel, Field
from pydantic_settings import BaseSettings

class PipelineConfig(BaseSettings):
    """Validate pipeline configuration from environment."""
    # ── Credential boundary ──────────────────────────────────────
    # These are read from environment variables automatically.
    # ─────────────────────────────────────────────────────────────
    snowflake_account: str
    snowflake_user: str
    snowflake_warehouse: str = "COMPUTE_WH"
    batch_size: int = Field(default=10000, ge=100, le=1000000)
    max_retries: int = Field(default=3, ge=1, le=10)
    log_level: str = Field(default="INFO", pattern="^(DEBUG|INFO|WARNING|ERROR)$")

    model_config = ConfigDict(env_prefix="PIPELINE_")
```

---

## Pandera Patterns

### DataFrame Schema

```python
import pandera as pa
from pandera.typing import DataFrame, Series
import pandas as pd

class OrderSchema(pa.DataFrameModel):
    """Schema for validated order DataFrames."""
    order_id: Series[str] = pa.Field(unique=True, nullable=False)
    customer_id: Series[str] = pa.Field(nullable=False, str_length={"min_value": 1})
    amount: Series[float] = pa.Field(gt=0, le=1_000_000)
    quantity: Series[int] = pa.Field(ge=1, le=10000)
    order_date: Series[pa.DateTime] = pa.Field(nullable=False)
    status: Series[str] = pa.Field(isin=["pending", "completed", "shipped", "cancelled"])

    class Config:
        strict = True    # Reject unexpected columns
        coerce = True    # Auto-cast types
        ordered = False  # Column order doesn't matter

# Use as type annotation for automatic validation
@pa.check_types
def process_orders(df: DataFrame[OrderSchema]) -> DataFrame[OrderSchema]:
    """Input and output are validated against OrderSchema."""
    return df.query("status == 'completed'")
```

### Custom Checks

```python
class TransactionSchema(pa.DataFrameModel):
    debit: Series[float] = pa.Field(ge=0)
    credit: Series[float] = pa.Field(ge=0)
    balance: Series[float]

    @pa.dataframe_check
    def balanced_transactions(cls, df: pd.DataFrame) -> bool:
        """Cross-column: balance must equal credit - debit."""
        expected = df["credit"] - df["debit"]
        return (df["balance"] - expected).abs().max() < 0.01
```

### Pandera with Polars

```python
import pandera.polars as pa
import polars as pl

schema = pa.DataFrameSchema({
    "order_id": pa.Column(str, pa.Check.str_length(min_value=1), unique=True),
    "amount": pa.Column(float, pa.Check.gt(0)),
    "status": pa.Column(str, pa.Check.isin(["completed", "pending", "cancelled"])),
})

# Validate Polars DataFrame
polars_df = pl.read_parquet("orders.parquet")
validated = schema.validate(polars_df)  # Returns validated Polars DataFrame
```

### Schema Inference

```python
# Auto-generate schema from sample data (starting point, then customize)
schema = pa.infer_schema(sample_df)
print(schema.to_script())  # Generates Python code for the schema
```

---

## Great Expectations Patterns

### Checkpoint-Based Validation

```python
import great_expectations as gx

# Initialize context
context = gx.get_context()

# Connect to data source
datasource = context.data_sources.add_snowflake(
    name="warehouse",
    connection_string=os.environ["SNOWFLAKE_CONNECTION_STRING"],
)

# Define data asset
data_asset = datasource.add_table_asset(
    name="orders",
    table_name="RAW.ORDERS",
)

# Create batch definition
batch_def = data_asset.add_batch_definition_whole_table("full_table")

# Build expectation suite
suite = context.suites.add(gx.ExpectationSuite(name="orders_quality"))

# Add expectations
suite.add_expectation(
    gx.expectations.ExpectColumnValuesToNotBeNull(column="order_id")
)
suite.add_expectation(
    gx.expectations.ExpectColumnValuesToBeUnique(column="order_id")
)
suite.add_expectation(
    gx.expectations.ExpectColumnValuesToBeBetween(
        column="amount", min_value=0, max_value=1_000_000
    )
)
suite.add_expectation(
    gx.expectations.ExpectColumnValuesToBeInSet(
        column="status",
        value_set=["pending", "completed", "shipped", "cancelled"],
    )
)
suite.add_expectation(
    gx.expectations.ExpectTableRowCountToBeBetween(min_value=1, max_value=10_000_000)
)

# Create and run checkpoint
checkpoint = context.checkpoints.add(
    gx.Checkpoint(
        name="orders_checkpoint",
        validation_definitions=[
            gx.ValidationDefinition(
                name="orders_validation",
                data=batch_def,
                suite=suite,
            )
        ],
    )
)

result = checkpoint.run()
if not result.success:
    raise ValueError("Data quality checkpoint failed")
```

### CI/CD Integration

```python
# In your CI pipeline or Dagster/Airflow task:
def run_quality_gate(table: str, suite_name: str) -> bool:
    """Run Great Expectations as a quality gate."""
    context = gx.get_context()
    checkpoint = context.checkpoints.get(f"{table}_checkpoint")
    result = checkpoint.run()

    # Log results
    for validation_result in result.run_results.values():
        stats = validation_result.statistics
        print(f"Evaluated: {stats['evaluated_expectations']}")
        print(f"Passed: {stats['successful_expectations']}")
        print(f"Failed: {stats['unsuccessful_expectations']}")

    return result.success
```

---

## Contract Testing

### Producer-Consumer Contract

```python
# Producer defines the contract (schema + quality guarantees)
class OrderContractV1(pa.DataFrameModel):
    """Contract: raw.orders table structure."""
    order_id: Series[str] = pa.Field(unique=True)
    customer_id: Series[str]
    amount: Series[float] = pa.Field(gt=0)
    order_date: Series[pa.DateTime]

    class Config:
        strict = True

# Consumer validates against the contract
def consumer_pipeline(df: pd.DataFrame) -> pd.DataFrame:
    """Consumer validates input matches expected contract."""
    try:
        OrderContractV1.validate(df)
    except pa.errors.SchemaError as e:
        raise ValueError(
            f"Upstream data contract violation: {e}. "
            f"Contact the orders team."
        )
    return transform(df)
```

### Schema Evolution Testing

```python
def test_schema_backward_compatible():
    """Verify new schema is backward compatible with old."""
    old_schema = OrderContractV1
    new_schema = OrderContractV2

    # New schema must accept all columns from old schema
    old_columns = set(old_schema.to_schema().columns.keys())
    new_columns = set(new_schema.to_schema().columns.keys())

    assert old_columns.issubset(new_columns), (
        f"Breaking change: columns {old_columns - new_columns} were removed"
    )
```

---

## Validation Decision Tree

```
Is the data from an external API or user input?
├── Yes → Pydantic (validate individual records at boundary)
│   └── Error rate tracking? → validate_and_report() pattern
└── No → Is it a DataFrame in a Python pipeline?
    ├── Yes → Pandera (validate DataFrame structure + values)
    │   └── Need cross-column checks? → @dataframe_check
    └── No → Is it a warehouse table?
        ├── dbt project? → dbt tests (native, zero overhead)
        └── Non-dbt? → Great Expectations (suite + checkpoint)
```
