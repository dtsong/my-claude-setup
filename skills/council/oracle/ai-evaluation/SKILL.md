---
name: "AI Evaluation"
department: "oracle"
description: "[Council] Golden dataset creation, automated scoring rubrics, and hallucination detection. Used during council/academy deliberation only."
version: 1
triggers:
  - "eval"
  - "evaluation"
  - "hallucination"
  - "golden dataset"
  - "scoring"
  - "benchmark"
  - "regression"
  - "quality"
  - "accuracy"
---

# AI Evaluation

## Purpose

Design an evaluation framework for AI/LLM features, including golden dataset creation, automated scoring rubrics, hallucination detection, and regression testing infrastructure.

## Inputs

- AI feature being evaluated (what it does, expected behavior)
- Input data examples and edge cases
- Quality requirements (accuracy thresholds, hallucination tolerance)
- Existing evaluation infrastructure (if any)
- Production monitoring requirements

## Process

### Step 1: Define Evaluation Dimensions

Identify what "good" means for this feature:
- **Correctness:** Does the output match the expected answer?
- **Faithfulness:** Does the output only use information from the provided context?
- **Relevance:** Does the output answer the actual question asked?
- **Completeness:** Does the output cover all aspects of the question?
- **Format compliance:** Does the output match the expected structure?
- **Safety:** Does the output avoid harmful, biased, or inappropriate content?

### Step 2: Build Golden Dataset

Create a high-quality evaluation dataset:
- **Size:** Minimum 50 examples, ideally 200+ for statistical significance
- **Distribution:** Cover common cases (60%), edge cases (25%), adversarial cases (15%)
- **Labeling:** Each example has input, expected output, and scoring criteria
- **Source:** Real user queries (anonymized) + synthetically generated edge cases
- **Versioning:** Dataset is version-controlled alongside the code

### Step 3: Design Automated Scoring

Create scoring rubrics that can run without human review:
- **Exact match:** For classification, extraction, or structured output (score: 0 or 1)
- **Semantic similarity:** Embedding-based comparison of generated vs expected (score: 0-1)
- **LLM-as-judge:** Use a stronger model to evaluate the output (score: 1-5 rubric)
- **Rule-based checks:** Required fields present, format valid, no PII leaked
- **Composite score:** Weighted combination of individual dimensions

### Step 4: Design Hallucination Detection

Build specific checks for fabricated content:
- **Reference validation:** Every cited fact must trace back to a source document
- **Entity verification:** Named entities (people, dates, numbers) must appear in context
- **Confidence calibration:** When the model says "I'm not sure," is it actually uncertain?
- **Contradiction detection:** Does the output contradict the provided context?
- **Fabrication patterns:** Common hallucination patterns to flag (fake URLs, invented citations)

### Step 5: Design Regression Testing

Build a CI/CD-compatible evaluation pipeline:
- **Trigger:** Run on prompt changes, model upgrades, or code changes affecting AI features
- **Threshold enforcement:** Fail the build if eval score drops below threshold
- **Comparison reporting:** Show score delta vs previous version, highlight regressions
- **Fast vs full:** Quick smoke test (20 examples) for every commit, full eval (200+) for releases

### Step 6: Design Production Monitoring

Plan ongoing quality monitoring:
- **Sampling:** Evaluate X% of production requests against automated scoring
- **Feedback loop:** User thumbs-up/down, explicit corrections
- **Drift detection:** Score distribution shift over time (model degradation, data drift)
- **Alerting:** Score drops below threshold, hallucination rate spikes, latency increases

## Output Format

```markdown
# AI Evaluation Framework

## Evaluation Dimensions
| Dimension | Weight | Scoring Method | Threshold |
|-----------|--------|---------------|-----------|
| Correctness | 40% | LLM-as-judge (1-5) | ≥ 4.0 |
| Faithfulness | 30% | Reference validation | ≥ 95% |
| Relevance | 20% | Semantic similarity | ≥ 0.85 |
| Format compliance | 10% | Rule-based | 100% |

## Golden Dataset
**Size:** [N examples]
**Distribution:**
| Category | Count | Description |
|----------|-------|-------------|
| Common cases | N | [Description] |
| Edge cases | N | [Description] |
| Adversarial | N | [Description] |

**Storage:** [Location in repo]
**Versioning:** [Approach]

## Scoring Rubric
### Correctness (LLM-as-Judge)
| Score | Criteria |
|-------|---------|
| 5 | Perfect — matches expected output in all aspects |
| 4 | Good — minor differences that don't affect usefulness |
| 3 | Acceptable — correct core answer with some issues |
| 2 | Poor — partially correct but missing key information |
| 1 | Wrong — incorrect or misleading answer |

## Hallucination Detection
| Check | Method | Severity |
|-------|--------|----------|
| Reference validation | [Approach] | Critical |
| Entity verification | [Approach] | High |
| Contradiction detection | [Approach] | High |

## Regression Testing Pipeline
```
[Code change] → [Smoke test (20 examples)] → [Pass?] → [Merge]
[Release] → [Full eval (200+ examples)] → [Pass threshold?] → [Deploy]
```

**Threshold:** Composite score ≥ [X] to pass
**Reporting:** [Where results are published]

## Production Monitoring
| Metric | Sample Rate | Alert Threshold |
|--------|------------|-----------------|
| Composite score | 5% of requests | < [X] |
| Hallucination rate | 5% of requests | > [X%] |
| User satisfaction | All feedback | < [X] thumbs-up rate |
```

## Quality Checks

- [ ] Golden dataset has at least 50 examples covering common and edge cases
- [ ] Scoring rubric has clear criteria for each score level (not subjective)
- [ ] Hallucination detection checks references against source documents
- [ ] Regression testing is automated and blocks deploys on score drops
- [ ] Production monitoring includes both automated scoring and user feedback
- [ ] Eval dataset is version-controlled alongside the code

## Evolution Notes
<!-- Observations appended after each use -->
