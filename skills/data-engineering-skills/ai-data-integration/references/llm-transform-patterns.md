## Contents

- [When LLM Transforms Make Sense](#when-llm-transforms-make-sense)
- [Batch Processing Pattern](#batch-processing-pattern)
- [Entity Extraction](#entity-extraction)
- [Structured Output with Tool Use](#structured-output-with-tool-use)
- [Caching and Deduplication](#caching-and-deduplication)
- [Cost Monitoring](#cost-monitoring)
- [Security Considerations](#security-considerations)

---

# LLM Transform Patterns Reference

> LLM-powered data enrichment, classification, and extraction with cost awareness. Part of the [AI Data Integration Skill](../SKILL.md).

---

## When LLM Transforms Make Sense

```
Is the transform on structured data with clear rules?
├── Yes → Use traditional code (regex, lookup tables, rules)
└── No → Does it require understanding natural language?
    ├── No → Use traditional ML (sklearn, etc.)
    └── Yes → Does it need world knowledge or reasoning?
        ├── No → Use fine-tuned small model or embeddings
        └── Yes → Use LLM transform (with cost guardrails)
```

| Operation | Traditional Cost | LLM Cost | LLM Worth It? |
|-----------|-----------------|----------|---------------|
| Categorize by keyword rules | ~$0 | ~$0.01/row | No |
| Classify free-text sentiment | ~$0.001/row (ML) | ~$0.005/row | Maybe |
| Extract entities from unstructured text | ~$0.01/row (NER) | ~$0.005/row | Yes |
| Summarize long text | Not possible | ~$0.01/row | Yes |
| Enrich with world knowledge | Not possible | ~$0.01/row | Yes |

---

## Batch Processing Pattern

Always process records in batches -- never one LLM call per row.

```python
import anthropic, json
from pydantic import BaseModel
from typing import Literal

class ClassifiedRecord(BaseModel):
    id: str
    category: Literal["bug", "feature", "question", "docs", "other"]
    confidence: float
    reasoning: str

def classify_batch(records: list[dict], batch_size: int = 25,
                   model: str = "claude-haiku-4-5-20251001") -> list[ClassifiedRecord]:
    """Batch classification -- one LLM call per batch, not per record. ~$0.01 per batch of 25."""
    client = anthropic.Anthropic()
    results = []
    for i in range(0, len(records), batch_size):
        batch = records[i:i + batch_size]
        items = "\n".join(f"[{r['id']}] {r['title']}: {r.get('description', '')[:150]}" for r in batch)
        response = client.messages.create(
            model=model, max_tokens=4096,
            system='Classify each item. Return JSON array: [{"id": "...", "category": "bug|feature|question|docs|other", "confidence": 0.0-1.0, "reasoning": "brief"}]',
            messages=[{"role": "user", "content": items}],
        )
        for r in json.loads(response.content[0].text):
            results.append(ClassifiedRecord.model_validate(r))
    return results
```

---

## Entity Extraction

```python
from pydantic import BaseModel
from typing import Optional

class ExtractedEntity(BaseModel):
    company_name: Optional[str] = None
    person_name: Optional[str] = None
    dollar_amount: Optional[float] = None
    date_reference: Optional[str] = None
    product_name: Optional[str] = None

def extract_entities_batch(texts: list[dict], batch_size: int = 20) -> list[dict]:
    client = anthropic.Anthropic()
    results = []
    for i in range(0, len(texts), batch_size):
        batch = texts[i:i + batch_size]
        items = "\n---\n".join(f"[{t['id']}] {t['text'][:500]}" for t in batch)
        response = client.messages.create(
            model="claude-haiku-4-5-20251001", max_tokens=4096,
            system='Extract entities. Return JSON array: [{"id": "...", "company_name": ..., "person_name": ..., "dollar_amount": ..., "date_reference": ..., "product_name": ...}] Use null for missing.',
            messages=[{"role": "user", "content": items}],
        )
        for r in json.loads(response.content[0].text):
            results.append({"id": r["id"], **ExtractedEntity.model_validate(r).model_dump()})
    return results
```

---

## Structured Output with Tool Use

Use Claude's tool use for guaranteed structured output:

```python
def classify_with_tools(text: str) -> dict:
    client = anthropic.Anthropic()
    response = client.messages.create(
        model="claude-haiku-4-5-20251001", max_tokens=1024,
        tools=[{
            "name": "classify_text",
            "description": "Classify the given text",
            "input_schema": {
                "type": "object",
                "properties": {
                    "category": {"type": "string", "enum": ["bug", "feature", "question", "docs", "other"]},
                    "confidence": {"type": "number", "minimum": 0, "maximum": 1},
                    "reasoning": {"type": "string", "maxLength": 200},
                },
                "required": ["category", "confidence", "reasoning"],
            },
        }],
        tool_choice={"type": "tool", "name": "classify_text"},
        messages=[{"role": "user", "content": f"Classify this text:\n\n{text}"}],
    )
    return response.content[0].input
```

---

## Caching and Deduplication

```python
import hashlib, json
from pathlib import Path

class LLMTransformCache:
    def __init__(self, cache_dir: str = ".llm_cache"):
        self.cache_dir = Path(cache_dir)
        self.cache_dir.mkdir(exist_ok=True)
        self.stats = {"hits": 0, "misses": 0}

    def _key(self, input_text: str, transform_type: str) -> str:
        return hashlib.sha256(f"{transform_type}:{input_text.strip()}".encode()).hexdigest()

    def get(self, input_text: str, transform_type: str) -> dict | None:
        path = self.cache_dir / f"{self._key(input_text, transform_type)}.json"
        if path.exists():
            self.stats["hits"] += 1
            return json.loads(path.read_text())
        self.stats["misses"] += 1
        return None

    def put(self, input_text: str, transform_type: str, result: dict):
        path = self.cache_dir / f"{self._key(input_text, transform_type)}.json"
        path.write_text(json.dumps(result))
```

---

## Cost Monitoring

```python
from dataclasses import dataclass

@dataclass
class CostTracker:
    input_tokens: int = 0
    output_tokens: int = 0
    calls: int = 0
    INPUT_COST_PER_1M: float = 0.80   # Claude Haiku 4.5
    OUTPUT_COST_PER_1M: float = 4.00

    @property
    def estimated_cost(self) -> float:
        return (self.input_tokens / 1e6) * self.INPUT_COST_PER_1M + (self.output_tokens / 1e6) * self.OUTPUT_COST_PER_1M

    def record(self, response):
        self.input_tokens += response.usage.input_tokens
        self.output_tokens += response.usage.output_tokens
        self.calls += 1
```

---

## Security Considerations

| Concern | Mitigation |
|---------|-----------|
| **Sending PII to LLM APIs** | Tier 2-3: Anonymize/mask PII before sending. Use local models for PII data. |
| **Data leakage via prompts** | Never include production data in system prompts. Use synthetic few-shot examples. |
| **LLM hallucination** | Validate output against expected schema (Pydantic). Log low-confidence results. |
| **Cost runaway** | Set per-pipeline cost budgets. Track costs per run. Alert on threshold breach. |
| **Non-determinism** | Cache results. Use `temperature=0`. Log all inputs/outputs for audit. |
