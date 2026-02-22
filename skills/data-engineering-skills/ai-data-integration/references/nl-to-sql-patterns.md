## Contents

- [Schema Context Strategies](#schema-context-strategies)
  - [Strategy 1: Full Schema (Small Warehouses, < 50 tables)](#strategy-1-full-schema-small-warehouses--50-tables)
  - [Strategy 2: Relevant Tables (Medium Warehouses, 50-500 tables)](#strategy-2-relevant-tables-medium-warehouses-50-500-tables)
  - [Strategy 3: Two-Pass (Large Warehouses, 500+ tables)](#strategy-3-two-pass-large-warehouses-500-tables)
- [Few-Shot Examples](#few-shot-examples)
- [Query Validation with sqlglot](#query-validation-with-sqlglot)
- [Query Caching](#query-caching)
- [Evaluation Metrics](#evaluation-metrics)
- [Error Recovery](#error-recovery)

---

# NL-to-SQL Patterns Reference

> Natural language to SQL generation with guardrails, evaluation, and caching. Part of the [AI Data Integration Skill](../SKILL.md).

---

## Schema Context Strategies

The quality of NL-to-SQL depends heavily on schema context. Too little context produces inaccurate SQL; too much wastes the context window.

### Strategy 1: Full Schema (Small Warehouses, < 50 tables)

```python
def full_schema_context(allowed_schemas: list[str]) -> str:
    context = []
    for schema in allowed_schemas:
        for table in get_tables(schema):
            columns = get_columns(schema, table)
            col_lines = [f"  {c['name']} {c['type']}" for c in columns]
            context.append(f"-- {schema}.{table}\n" + "\n".join(col_lines))
    return "\n\n".join(context)
```

### Strategy 2: Relevant Tables (Medium Warehouses, 50-500 tables)

```python
def relevant_schema_context(question: str, table_embeddings: list[dict], top_k: int = 8) -> str:
    q_embedding = generate_embedding(question)
    scored = [(te, cosine_similarity(q_embedding, te["embedding"])) for te in table_embeddings]
    top_tables = sorted(scored, key=lambda x: x[1], reverse=True)[:top_k]
    return "\n\n".join(f"-- {t['fqn']} (relevance: {s:.2f})\n{t['ddl']}" for t, s in top_tables)
```

### Strategy 3: Two-Pass (Large Warehouses, 500+ tables)

```python
def two_pass_context(question: str) -> str:
    """Pass 1: LLM selects relevant tables from summaries. Pass 2: Full columns for selected tables."""
    table_summaries = "\n".join(get_all_table_summaries())
    client = anthropic.Anthropic()
    selection = client.messages.create(
        model="claude-haiku-4-5-20251001",
        max_tokens=256,
        system="Select the 3-8 most relevant tables. Return only table names, one per line.",
        messages=[{"role": "user", "content": f"Tables:\n{table_summaries}\n\nQuestion: {question}"}],
    )
    selected = selection.content[0].text.strip().split("\n")
    context = []
    for table_fqn in selected:
        schema, table = table_fqn.strip().split(".")
        columns = get_columns(schema, table)
        col_lines = [f"  {c['name']} {c['type']}" + (f" -- {c['comment']}" if c.get("comment") else "")
                     for c in columns]
        context.append(f"-- {table_fqn}\n" + "\n".join(col_lines))
    return "\n\n".join(context)
```

---

## Few-Shot Examples

Including example question-to-SQL pairs dramatically improves accuracy:

```python
FEW_SHOT_EXAMPLES = [
    {
        "question": "What are the top 10 customers by revenue this year?",
        "sql": """SELECT c.customer_id, c.name, SUM(o.amount) as total_revenue
FROM marts.dim_customers c JOIN marts.fct_orders o ON c.customer_id = o.customer_id
WHERE o.order_date >= DATE_TRUNC('year', CURRENT_DATE())
GROUP BY c.customer_id, c.name ORDER BY total_revenue DESC LIMIT 10"""
    },
]

def build_few_shot_prompt(question: str, schema_context: str) -> str:
    examples = "\n\n".join(f"Question: {ex['question']}\nSQL:\n{ex['sql']}" for ex in FEW_SHOT_EXAMPLES)
    return f"""You are a SQL expert. Generate a single SQL query.

Schema:
{schema_context}

Examples:
{examples}

Rules:
- Use only tables and columns from the schema
- Always include LIMIT (default 100, max 1000)
- Use explicit column names (never SELECT *)

Question: {question}

SQL:"""
```

---

## Query Validation with sqlglot

```python
import sqlglot
from sqlglot import exp

def validate_and_fix_sql(sql: str, dialect: str = "snowflake",
                         allowed_schemas: list[str] = None, max_limit: int = 1000) -> tuple[str, list[str]]:
    """Validate and auto-fix common issues in AI-generated SQL. Returns (fixed_sql, warnings)."""
    warnings = []
    parsed = sqlglot.parse_one(sql, dialect=dialect)

    if not isinstance(parsed, exp.Select):
        raise ValueError("Only SELECT statements are allowed")
    for node_type in [exp.Insert, exp.Update, exp.Delete, exp.Drop, exp.Create]:
        if parsed.find(node_type):
            raise ValueError(f"Blocked operation: {node_type.__name__}")

    limit_node = parsed.find(exp.Limit)
    if not limit_node:
        parsed = parsed.limit(max_limit)
        warnings.append(f"Added LIMIT {max_limit}")
    elif int(limit_node.expression.this) > max_limit:
        parsed = parsed.limit(max_limit)
        warnings.append(f"Reduced LIMIT to {max_limit}")

    if allowed_schemas:
        for table in parsed.find_all(exp.Table):
            db = str(table.db).upper() if table.db else None
            if db and db not in [s.upper() for s in allowed_schemas]:
                raise ValueError(f"Access to schema '{db}' is not allowed")

    return parsed.sql(dialect=dialect), warnings
```

---

## Query Caching

```python
import hashlib, json
from pathlib import Path

class NLSQLCache:
    def __init__(self, cache_dir: str = ".nlsql_cache"):
        self.cache_dir = Path(cache_dir)
        self.cache_dir.mkdir(exist_ok=True)

    def _key(self, question: str, schema_hash: str) -> str:
        return hashlib.sha256(f"{question.strip().lower()}:{schema_hash}".encode()).hexdigest()

    def get(self, question: str, schema_hash: str) -> str | None:
        path = self.cache_dir / f"{self._key(question, schema_hash)}.json"
        return json.loads(path.read_text())["sql"] if path.exists() else None

    def put(self, question: str, schema_hash: str, sql: str):
        path = self.cache_dir / f"{self._key(question, schema_hash)}.json"
        path.write_text(json.dumps({"question": question, "sql": sql, "schema_hash": schema_hash}))
```

---

## Evaluation Metrics

```python
def evaluate_nl_to_sql(test_cases: list[dict], generator_fn, executor_fn) -> dict:
    results = {"total": len(test_cases), "valid_sql": 0, "executes": 0, "correct_result": 0}
    for case in test_cases:
        sql = generator_fn(case["question"])
        try:
            sqlglot.parse_one(sql)
            results["valid_sql"] += 1
        except Exception:
            continue
        try:
            actual = executor_fn(sql)
            results["executes"] += 1
        except Exception:
            continue
        if compare_results(actual, case["expected_result"]):
            results["correct_result"] += 1
    results["accuracy"] = results["correct_result"] / results["total"]
    return results
```

---

## Error Recovery

```python
def generate_sql_with_retry(question: str, schema_context: str, executor_fn, max_attempts: int = 3):
    """Generate SQL with error-driven retry. Pass previous errors as feedback to the LLM."""
    attempts = []
    for _ in range(max_attempts):
        error_context = "\n".join(f"- {a['error']}" for a in attempts if a.get("error"))
        prompt = build_few_shot_prompt(question, schema_context)
        if error_context:
            prompt += f"\n\nPrevious attempts failed:\n{error_context}"
        sql = call_llm(prompt)
        try:
            sql, warnings = validate_and_fix_sql(sql)
            result = executor_fn(sql)
            return sql, attempts + [{"sql": sql, "status": "success"}]
        except Exception as e:
            attempts.append({"sql": sql, "error": str(e)})
    raise ValueError(f"Failed after {max_attempts} attempts")
```
