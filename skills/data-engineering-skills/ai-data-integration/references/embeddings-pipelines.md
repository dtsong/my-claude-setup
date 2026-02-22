## Contents

- [Embedding Providers](#embedding-providers)
- [Data Catalog Embedding Pipeline](#data-catalog-embedding-pipeline)
- [Vector Stores](#vector-stores)
- [RAG Over Data Documentation](#rag-over-data-documentation)
- [Semantic Column Matching](#semantic-column-matching)
- [Security Considerations](#security-considerations)

---

# Embeddings Pipelines Reference

> Vector embeddings for data catalog search, semantic matching, and RAG over data documentation. Part of the [AI Data Integration Skill](../SKILL.md).

---

## Embedding Providers

| Provider | Model | Dimensions | Cost (per 1M tokens) | Best For |
|----------|-------|-----------|----------------------|----------|
| Voyage AI | voyage-3 | 1024 | ~$0.06 | Code + technical text |
| OpenAI | text-embedding-3-small | 1536 | ~$0.02 | General purpose, low cost |
| OpenAI | text-embedding-3-large | 3072 | ~$0.13 | High accuracy |
| Cohere | embed-english-v3 | 1024 | ~$0.10 | Multilingual, search |
| Local | all-MiniLM-L6-v2 | 384 | Free (compute only) | Privacy-sensitive, Tier 2-3 |

**For Tier 2-3 (regulated/air-gapped):** Use local embedding models (Sentence Transformers) to keep data on-premises.

---

## Data Catalog Embedding Pipeline

### Step 1: Extract Metadata

```python
def extract_table_metadata(conn, schemas: list[str]) -> list[dict]:
    """Extract rich metadata for embedding."""
    tables = []
    for schema in schemas:
        cursor = conn.cursor()
        cursor.execute(f"""
            SELECT
                t.table_name,
                t.comment as table_comment,
                t.row_count
            FROM information_schema.tables t
            WHERE t.table_schema = '{schema}'
        """)

        for row in cursor.fetchall():
            table_name, comment, row_count = row

            # Get columns
            cursor.execute(f"""
                SELECT column_name, data_type, comment
                FROM information_schema.columns
                WHERE table_schema = '{schema}' AND table_name = '{table_name}'
                ORDER BY ordinal_position
            """)
            columns = [
                {"name": r[0], "type": r[1], "comment": r[2]}
                for r in cursor.fetchall()
            ]

            tables.append({
                "schema": schema,
                "name": table_name,
                "description": comment or "",
                "row_count": row_count,
                "columns": columns,
            })

    return tables
```

### Step 2: Build Text Representations

```python
def table_to_text(table: dict) -> str:
    """Convert table metadata to rich text for embedding."""
    col_descriptions = []
    for col in table["columns"]:
        desc = f"  - {col['name']} ({col['type']})"
        if col.get("comment"):
            desc += f": {col['comment']}"
        col_descriptions.append(desc)

    return (
        f"Table: {table['schema']}.{table['name']}\n"
        f"Description: {table.get('description', 'No description available')}\n"
        f"Row count: {table.get('row_count', 'unknown')}\n"
        f"Columns:\n" + "\n".join(col_descriptions)
    )

def column_to_text(table: dict, column: dict) -> str:
    """Convert column metadata to text for fine-grained search."""
    return (
        f"Column: {table['schema']}.{table['name']}.{column['name']}\n"
        f"Type: {column['type']}\n"
        f"Description: {column.get('comment', 'No description')}\n"
        f"Table description: {table.get('description', '')}"
    )
```

### Step 3: Generate and Store Embeddings

```python
import numpy as np
from typing import Callable

def embed_catalog(
    tables: list[dict],
    embed_fn: Callable[[list[str]], list[list[float]]],
    batch_size: int = 100,
) -> list[dict]:
    """Generate embeddings for all tables and columns."""
    # Table-level embeddings
    table_texts = [table_to_text(t) for t in tables]
    table_embeddings = []
    for i in range(0, len(table_texts), batch_size):
        batch = table_texts[i:i + batch_size]
        vectors = embed_fn(batch)
        table_embeddings.extend(vectors)

    results = []
    for table, text, embedding in zip(tables, table_texts, table_embeddings):
        results.append({
            "id": f"{table['schema']}.{table['name']}",
            "type": "table",
            "text": text,
            "embedding": embedding,
            "metadata": {
                "schema": table["schema"],
                "table": table["name"],
                "row_count": table.get("row_count"),
            },
        })

    return results
```

---

## Vector Stores

### ChromaDB (Local / Small Scale)

```python
import chromadb

def create_catalog_index(embeddings: list[dict]) -> chromadb.Collection:
    """Create a local ChromaDB collection for catalog search."""
    client = chromadb.PersistentClient(path=".catalog_index")
    collection = client.get_or_create_collection(
        name="data_catalog",
        metadata={"hnsw:space": "cosine"},
    )

    collection.upsert(
        ids=[e["id"] for e in embeddings],
        embeddings=[e["embedding"] for e in embeddings],
        documents=[e["text"] for e in embeddings],
        metadatas=[e["metadata"] for e in embeddings],
    )

    return collection

def search_catalog(collection, query: str, embed_fn, top_k: int = 5) -> list[dict]:
    """Search catalog by natural language query."""
    query_embedding = embed_fn([query])[0]

    results = collection.query(
        query_embeddings=[query_embedding],
        n_results=top_k,
        include=["documents", "metadatas", "distances"],
    )

    return [
        {
            "id": results["ids"][0][i],
            "text": results["documents"][0][i],
            "metadata": results["metadatas"][0][i],
            "similarity": 1 - results["distances"][0][i],  # Convert distance to similarity
        }
        for i in range(len(results["ids"][0]))
    ]
```

### pgvector (PostgreSQL)

```python
# For production deployments alongside existing PostgreSQL infrastructure

# Schema
CREATE_TABLE_SQL = """
CREATE TABLE IF NOT EXISTS catalog_embeddings (
    id TEXT PRIMARY KEY,
    type TEXT NOT NULL,           -- 'table' or 'column'
    text TEXT NOT NULL,
    embedding vector(1536),      -- Match your model's dimensions
    metadata JSONB,
    updated_at TIMESTAMP DEFAULT NOW()
);

CREATE INDEX IF NOT EXISTS catalog_embeddings_idx
ON catalog_embeddings USING ivfflat (embedding vector_cosine_ops)
WITH (lists = 100);
"""

# Search query
SEARCH_SQL = """
SELECT id, text, metadata,
       1 - (embedding <=> %s::vector) as similarity
FROM catalog_embeddings
ORDER BY embedding <=> %s::vector
LIMIT %s
"""
```

---

## RAG Over Data Documentation

Use RAG (Retrieval-Augmented Generation) to answer questions from dbt docs, data dictionaries, and runbooks.

### Document Chunking

```python
def chunk_markdown(text: str, max_chunk_size: int = 1000) -> list[dict]:
    """Chunk markdown by headers, respecting section boundaries."""
    chunks = []
    current_chunk = []
    current_header = ""
    current_size = 0

    for line in text.split("\n"):
        # Detect headers
        if line.startswith("#"):
            # Save current chunk
            if current_chunk:
                chunks.append({
                    "header": current_header,
                    "text": "\n".join(current_chunk),
                })
            current_header = line
            current_chunk = [line]
            current_size = len(line)
        else:
            if current_size + len(line) > max_chunk_size and current_chunk:
                chunks.append({
                    "header": current_header,
                    "text": "\n".join(current_chunk),
                })
                current_chunk = [line]
                current_size = len(line)
            else:
                current_chunk.append(line)
                current_size += len(line)

    if current_chunk:
        chunks.append({"header": current_header, "text": "\n".join(current_chunk)})

    return chunks
```

### RAG Pipeline

```python
def answer_question_from_docs(
    question: str,
    doc_collection,
    embed_fn,
    top_k: int = 5,
) -> str:
    """Answer a question using RAG over documentation."""
    # Retrieve relevant chunks
    results = search_catalog(doc_collection, question, embed_fn, top_k=top_k)
    context = "\n\n---\n\n".join(r["text"] for r in results)

    # Generate answer with retrieved context
    client = anthropic.Anthropic()
    response = client.messages.create(
        model="claude-sonnet-4-5-20250929",
        max_tokens=1024,
        system="""Answer the user's question based ONLY on the provided documentation context.
If the answer is not in the context, say "I don't have enough information to answer this."
Cite the relevant section when possible.""",
        messages=[{
            "role": "user",
            "content": f"Context:\n{context}\n\nQuestion: {question}",
        }],
    )

    return response.content[0].text
```

---

## Semantic Column Matching

Match columns across systems by meaning, not just name:

```python
def find_matching_columns(
    source_columns: list[dict],
    target_columns: list[dict],
    embed_fn,
    threshold: float = 0.8,
) -> list[dict]:
    """Find semantically matching columns between two systems."""
    source_texts = [column_to_text({"schema": "source", "name": "src"}, c) for c in source_columns]
    target_texts = [column_to_text({"schema": "target", "name": "tgt"}, c) for c in target_columns]

    source_embeddings = embed_fn(source_texts)
    target_embeddings = embed_fn(target_texts)

    matches = []
    for i, s_emb in enumerate(source_embeddings):
        best_score = 0
        best_match = None
        for j, t_emb in enumerate(target_embeddings):
            score = cosine_similarity(s_emb, t_emb)
            if score > best_score:
                best_score = score
                best_match = j

        if best_score >= threshold:
            matches.append({
                "source": source_columns[i]["name"],
                "target": target_columns[best_match]["name"],
                "similarity": best_score,
            })

    return matches

# Example output:
# [
#   {"source": "cust_id", "target": "customer_identifier", "similarity": 0.92},
#   {"source": "order_amt", "target": "total_amount", "similarity": 0.85},
# ]
```

---

## Security Considerations

| Concern | Mitigation |
|---------|-----------|
| **Embedding PII** | Only embed metadata (table/column names, descriptions). Never embed row data in Tier 2-3. |
| **Vector store access** | Scope access to the vector store. AI agents should only see embeddings for allowed schemas. |
| **Prompt injection via metadata** | Sanitize table/column descriptions before embedding. Malicious descriptions could influence RAG output. |
| **Local vs cloud embeddings** | Tier 2-3: Use local models (Sentence Transformers). Tier 1: Cloud providers are acceptable. |
