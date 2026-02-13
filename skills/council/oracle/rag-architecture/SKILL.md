---
name: "RAG Architecture"
department: "oracle"
description: "[Council] Chunking strategies, embedding pipelines, vector DB selection, and retrieval optimization. Used during council/academy deliberation only."
version: 1
triggers:
  - "RAG"
  - "retrieval"
  - "embedding"
  - "vector"
  - "chunking"
  - "semantic search"
  - "Pinecone"
  - "ChromaDB"
  - "Weaviate"
  - "reranking"
---

# RAG Architecture

## Purpose

Design a Retrieval-Augmented Generation pipeline, including document processing, chunking strategy, embedding pipeline, vector database selection, retrieval optimization, and context assembly.

## Inputs

- Source documents (type, volume, update frequency)
- Query patterns (user questions, search terms, structured queries)
- Quality requirements (relevance threshold, hallucination tolerance)
- Latency requirements (real-time, near-real-time, batch)
- Cost constraints (embedding costs, storage costs, query costs)

## Process

### Step 1: Analyze Source Documents

Understand what's being indexed:
- **Document types:** PDFs, web pages, code, structured data, conversations
- **Volume:** Number of documents, total size, growth rate
- **Update frequency:** Static corpus, daily updates, real-time
- **Structure:** Highly structured (tables, headers) vs unstructured (prose, transcripts)
- **Quality:** Clean text vs noisy (OCR artifacts, HTML remnants, duplicates)

### Step 2: Design Chunking Strategy

Choose how to split documents:
- **Fixed-size:** 500-1000 tokens with 100-200 token overlap. Simple but may split concepts.
- **Semantic:** Split on paragraph/section boundaries. Preserves meaning but variable size.
- **Hierarchical:** Parent-child chunks (section summary + detail chunks). Best for complex docs.
- **Recursive:** Start large, recursively split until chunks fit size target.
- **Metadata enrichment:** Attach source, section title, page number to each chunk.

### Step 3: Select Embedding Model

Choose the embedding approach:
- **OpenAI text-embedding-3-small/large:** Best general-purpose, 1536/3072 dimensions
- **Cohere embed-v3:** Strong multilingual, supports search and classification modes
- **Open source (BGE, E5):** Self-hosted, lower cost at scale, variable quality
- **Considerations:** Dimension size (storage), context length, multilingual support, cost per token

### Step 4: Select Vector Database

Choose storage and retrieval:

| Database | Hosted | Open Source | Hybrid Search | Best For |
|----------|--------|------------|---------------|----------|
| Pinecone | Yes | No | Yes (sparse+dense) | Production, managed |
| Weaviate | Yes | Yes | Yes (BM25+vector) | Self-hosted, rich filtering |
| ChromaDB | No | Yes | No | Prototyping, local dev |
| pgvector | Via Supabase | Yes | BM25 separate | Already using Postgres |
| Qdrant | Yes | Yes | Yes | High-performance, filtering |

### Step 5: Design Retrieval Pipeline

Build the query-time pipeline:
1. **Query preprocessing:** Expand abbreviations, detect intent, generate sub-queries
2. **Embedding:** Encode query with same model used for documents
3. **Initial retrieval:** Top-K vector search (K=20-50)
4. **Reranking:** Cross-encoder reranker to reorder by relevance (return top 5-10)
5. **Context assembly:** Combine retrieved chunks into a prompt, add metadata
6. **Generation:** LLM call with assembled context + user query

### Step 6: Design Quality Metrics

Define how to measure RAG quality:
- **Retrieval metrics:** Recall@K (are relevant docs in top K?), MRR (is the best doc ranked first?)
- **Generation metrics:** Faithfulness (does the answer stick to context?), relevance (does it answer the question?)
- **End-to-end:** Answer accuracy on golden dataset, hallucination rate
- **Monitoring:** Track retrieval scores over time, flag low-confidence answers

## Output Format

```markdown
# RAG Architecture

## Source Analysis
| Attribute | Value |
|-----------|-------|
| Document types | [Types] |
| Corpus size | [Size] |
| Update frequency | [Frequency] |

## Chunking Strategy
**Method:** [Fixed/Semantic/Hierarchical]
**Target chunk size:** [X tokens]
**Overlap:** [X tokens]
**Metadata:** [Fields attached to each chunk]

## Embedding Pipeline
**Model:** [Name]
**Dimensions:** [N]
**Cost:** [$X per 1M tokens]
**Batch processing:** [Strategy for initial load vs incremental updates]

## Vector Database
**Choice:** [Database]
**Rationale:** [Why this DB]
**Index configuration:** [HNSW params, quantization, etc.]
**Hybrid search:** [BM25 + vector approach]

## Retrieval Pipeline
```
Query → [Preprocess] → [Embed] → [Vector Search (top 20)] → [Rerank (top 5)] → [Assemble Context] → [LLM] → [Validate] → Response
```

| Stage | Latency | Cost |
|-------|---------|------|
| Embedding | Xms | $X |
| Vector search | Xms | $X |
| Reranking | Xms | $X |
| Generation | Xms | $X |
| **Total** | **Xms** | **$X** |

## Quality Metrics
| Metric | Target | Measurement |
|--------|--------|-------------|
| Recall@10 | >90% | Golden dataset |
| Faithfulness | >95% | Automated scoring |
| Hallucination rate | <5% | Reference checking |

## Cost Model
| Component | Monthly Cost (at X queries/day) |
|-----------|-------------------------------|
| Embeddings | $X |
| Vector DB | $X |
| Reranking | $X |
| Generation | $X |
| **Total** | **$X** |
```

## Quality Checks

- [ ] Chunking strategy is justified against document structure (not just default 500 tokens)
- [ ] Embedding model matches the query language and domain
- [ ] Retrieval pipeline includes reranking (not just raw vector similarity)
- [ ] Cost model accounts for both indexing and query costs
- [ ] Quality metrics have defined targets and measurement approach
- [ ] Update strategy handles incremental changes (not re-index everything)
- [ ] Latency budget is broken down by pipeline stage

## Evolution Notes
<!-- Observations appended after each use -->
