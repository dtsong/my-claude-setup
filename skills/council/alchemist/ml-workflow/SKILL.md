---
name: ml-workflow
department: "alchemist"
description: "Use when designing end-to-end ML workflows. Covers experiment tracking, feature engineering and storage, model training pipelines, serving and deployment, A/B testing, and drift monitoring. Do not use for data warehouse schema design (use schema-evaluation) or ETL pipeline architecture (use pipeline-design)."
version: 1
triggers:
  - "ML"
  - "machine learning"
  - "model"
  - "training"
  - "feature store"
  - "MLflow"
  - "experiment"
  - "drift"
  - "serving"
  - "inference"
  - "W&B"
  - "Weights & Biases"
  - "model deployment"
---

# ML Workflow

## Purpose

Design end-to-end ML workflows covering experiment tracking, feature engineering and storage, model training pipelines, model serving and deployment, A/B testing for models, and monitoring for data and model drift. Produces a workflow architecture, tool selection rationale, and operational runbook.

## Scope Constraints

Reads ML code, configuration files, experiment logs, and infrastructure specs for analysis. Does not train models, execute experiments, or deploy to production.

## Inputs

- ML problem type (classification, regression, ranking, recommendation, NLP, CV)
- Data sources and feature candidates
- Model complexity range (linear/tree-based vs deep learning)
- Serving requirements (batch predictions, real-time inference, edge deployment)
- Team size and ML maturity (first model vs established ML platform)
- Infrastructure constraints (cloud provider, GPU availability, budget)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Define the ML problem
- [ ] Step 2: Design feature engineering pipeline
- [ ] Step 3: Design experiment tracking
- [ ] Step 4: Design training pipeline
- [ ] Step 5: Design model serving
- [ ] Step 6: Design A/B testing
- [ ] Step 7: Design monitoring and drift detection

### Step 1: Define the ML Problem Clearly

Before any tooling decisions, formalize:
- What is the prediction target? What does "correct" look like?
- What is the business metric this model optimizes? (Not just accuracy — revenue, conversion, engagement)
- What is the baseline? (Rule-based heuristic, current model, random chance)
- What is the minimum viable performance to ship?

Document the problem statement, target variable, evaluation metric, and success threshold.

### Step 2: Design the Feature Engineering Pipeline

Map raw data to model-ready features:
- **Feature identification:** Which raw fields become features? What transformations are needed (encoding, scaling, windowing, embedding)?
- **Temporal features:** Aggregations over time windows (last 7 days, last 30 days). Guard against leakage — never use future data to predict the past.
- **Feature store evaluation:** Does this project warrant a feature store (Feast, Tecton, Hopsworks)? Feature stores add value when: features are shared across models, real-time features are needed, or training-serving skew is a risk.
- **Feature documentation:** Each feature should have: name, description, data type, source, transformation logic, and expected distribution.

### Step 3: Design Experiment Tracking

Set up reproducible experiment management:
- **Tool selection:** MLflow (open-source, self-hosted), Weights & Biases (managed, rich visualization), Neptune, or ClearML.
- **What to track:** Hyperparameters, metrics (train/val/test), dataset version, code version (git SHA), environment (dependencies), artifacts (model files, plots).
- **Experiment organization:** Project → Experiment group → Individual runs. Name runs meaningfully (not "run_42").
- **Comparison workflow:** How does the team compare runs? Dashboard? Automated reports?

### Step 4: Design the Training Pipeline

Build a reproducible, automated training workflow:
- **Data split strategy:** Time-based splits for temporal data, stratified splits for imbalanced classes. Never random-split time-series data.
- **Training orchestration:** Single script, or DAG-based (Airflow, Kubeflow Pipelines, SageMaker Pipelines)?
- **Hyperparameter tuning:** Grid search, random search, Bayesian optimization (Optuna, Ray Tune)?
- **Validation strategy:** Cross-validation, holdout, or time-series walk-forward?
- **Model registry:** Where are trained models stored? How are they versioned? Who approves promotion to production?

### Step 5: Design Model Serving

Plan how predictions reach users:
- **Batch serving:** Run predictions on a schedule, store results in a table. Best for recommendations, risk scores, daily reports.
- **Real-time serving:** Model behind an API endpoint. Best for search ranking, fraud detection, dynamic pricing.
- **Streaming serving:** Model embedded in a stream processor. Best for event-driven predictions on Kafka/Kinesis streams.
- **Edge serving:** Model deployed to device/browser. Best for latency-critical or offline-capable applications.

For real-time serving, specify: latency SLA (p50/p99), throughput (requests/second), scaling strategy (auto-scale triggers), and fallback behavior (what happens if the model is unavailable?).

### Step 6: Design A/B Testing for Models

Plan controlled rollout of model changes:
- **Traffic splitting:** How is traffic divided between control (current model) and treatment (new model)?
- **Metric selection:** Primary metric (business KPI), guardrail metrics (latency, error rate), and minimum detectable effect.
- **Duration calculation:** How long must the test run to reach statistical significance?
- **Rollback criteria:** What triggers an automatic rollback?

### Step 7: Design Monitoring and Drift Detection

Plan ongoing model health monitoring:
- **Data drift:** Monitor input feature distributions for shifts. Tool options: Evidently, WhyLabs, Great Expectations.
- **Model drift:** Monitor prediction distribution and performance metrics over time. Alert when performance degrades below threshold.
- **Concept drift:** Monitor the relationship between features and target. Retrain triggers when the world changes (seasonality, market shifts).
- **Operational monitoring:** Latency, error rates, throughput, GPU utilization for serving infrastructure.

Define retraining policy: scheduled (weekly/monthly), triggered (drift detected), or continuous (online learning).

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Handoff

- Hand off to pipeline-design if the workflow reveals data ingestion or ETL orchestration needs.
- Hand off to operator/deployment-plan if model serving surfaces deployment or infrastructure architecture concerns.

## Output Format

```markdown
# ML Workflow: [Project/Model Name]

## Problem Definition

| Aspect | Detail |
|--------|--------|
| Problem type | ... |
| Target variable | ... |
| Business metric | ... |
| Evaluation metric | ... |
| Baseline performance | ... |
| Success threshold | ... |

## Feature Engineering

| Feature | Source | Transformation | Type | Leakage Risk |
|---------|--------|---------------|------|-------------|
| ...     | ...    | ...           | ...  | Low/Med/High |

**Feature store:** [Yes/No — tool choice and rationale]

## Experiment Tracking

| Aspect | Choice | Rationale |
|--------|--------|-----------|
| Tool | ... | ... |
| What's tracked | ... | ... |
| Organization | ... | ... |

## Training Pipeline

```
[ASCII diagram showing data → features → train → evaluate → register]
```

| Stage | Tool/Method | Notes |
|-------|------------|-------|
| Data split | ... | ... |
| Training | ... | ... |
| Tuning | ... | ... |
| Validation | ... | ... |
| Registry | ... | ... |

## Model Serving

| Aspect | Detail |
|--------|--------|
| Serving mode | Batch / Real-time / Streaming / Edge |
| Latency SLA | ... |
| Throughput | ... |
| Scaling | ... |
| Fallback | ... |

## A/B Testing

| Aspect | Detail |
|--------|--------|
| Traffic split | ... |
| Primary metric | ... |
| Guardrail metrics | ... |
| Min duration | ... |
| Rollback criteria | ... |

## Monitoring and Drift

| Monitor | Tool | Threshold | Action |
|---------|------|-----------|--------|
| Data drift | ... | ... | ... |
| Model drift | ... | ... | ... |
| Concept drift | ... | ... | ... |
| Operational | ... | ... | ... |

**Retraining policy:** [Scheduled / Triggered / Continuous — details]
```

## Quality Checks

- [ ] Problem definition includes a clear business metric, not just an ML metric
- [ ] Feature engineering documents leakage risk for every temporal feature
- [ ] Experiment tracking captures enough metadata to reproduce any run
- [ ] Training pipeline uses appropriate split strategy (time-based for temporal data)
- [ ] Model registry has a clear promotion workflow (dev → staging → production)
- [ ] Serving architecture matches latency and throughput requirements
- [ ] A/B testing plan includes statistical power calculation and guardrail metrics
- [ ] Drift monitoring covers data, model, and concept drift with defined thresholds
- [ ] Retraining policy is documented with clear triggers and automation level
- [ ] Fallback behavior is defined for model unavailability

## Evolution Notes
<!-- Observations appended after each use -->
