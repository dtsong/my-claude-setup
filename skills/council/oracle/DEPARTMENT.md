---
name: "Oracle Department"
executive: "Oracle"
color: "Violet"
description: "AI/LLM integration, RAG, prompt engineering"
---

# Oracle Department — Violet Lens

The Oracle's department of focused skills for prompt engineering, RAG pipeline architecture, and AI evaluation methodology.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [prompt-engineering](prompt-engineering/SKILL.md) | System prompt design, chain-of-thought, structured output, versioning | default | `prompt`, `system prompt`, `few-shot`, `chain-of-thought`, `structured output`, `function calling`, `tool use` |
| [rag-architecture](rag-architecture/SKILL.md) | Chunking strategies, embedding pipelines, vector DB, retrieval | default | `RAG`, `retrieval`, `embedding`, `vector`, `chunking`, `semantic search`, `Pinecone`, `ChromaDB`, `reranking` |
| [ai-evaluation](ai-evaluation/SKILL.md) | Golden datasets, automated scoring, hallucination detection | default | `eval`, `evaluation`, `hallucination`, `golden dataset`, `scoring`, `benchmark`, `regression`, `quality` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| System prompt design, few-shot examples, chain-of-thought, structured output, function calling, tool use | prompt-engineering | High |
| RAG pipeline, chunking strategy, embedding model, vector database, semantic search, reranking | rag-architecture | High |
| Evaluation framework, golden dataset, scoring rubric, hallucination detection, regression testing, benchmark | ai-evaluation | High |
| Model selection, temperature tuning, token optimization, prompt versioning | prompt-engineering | Medium |
| Retrieval quality metrics, context assembly, hybrid search configuration | rag-architecture | Medium |

## Load Directive

Load one specialist skill at a time using the Skill tool. Read the classification logic table to select the appropriate specialist, then invoke the skill. Do not pre-load multiple specialists simultaneously.

## Handoff Protocol

When the specialist skill output reveals issues in another department's domain:
1. Complete the current skill's output format.
2. Note the cross-domain findings in the output.
3. Recommend loading the appropriate department and skill (e.g., "Hand off data pipeline requirements for RAG to alchemist/pipeline-design for ingestion architecture").
