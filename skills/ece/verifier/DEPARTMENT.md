---
name: "Verifier Department"
executive: "Verifier"
color: "Pearl"
description: "Verification and validation — DVT protocols, measurement system analysis, statistical test methods"
---

# Verifier Department — Pearl Lens

The Verifier department owns verification and validation methodology, from DVT protocol authoring through measurement system analysis to statistical test design. All test plans must demonstrate traceability to requirements and quantified measurement uncertainty.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [dvt-protocol](dvt-protocol/SKILL.md) | Design verification test protocol | default | `DVT`, `verification test`, `test protocol`, `acceptance criteria`, `pass/fail`, `test report` |
| [measurement-uncertainty](measurement-uncertainty/SKILL.md) | GR&R and measurement system analysis | default | `GR&R`, `measurement uncertainty`, `MSA`, `gage`, `repeatability`, `reproducibility` |
| [statistical-methods](statistical-methods/SKILL.md) | Sample size, confidence intervals, DOE | default | `sample size`, `confidence interval`, `DOE`, `statistics`, `hypothesis test`, `Cpk` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Request involves writing DVT protocols, defining acceptance criteria, or structuring verification test reports | dvt-protocol | High |
| Request involves measurement system analysis, GR&R studies, or quantifying measurement uncertainty | measurement-uncertainty | High |
| Request involves sample size calculation, DOE planning, confidence interval estimation, or process capability | statistical-methods | High |
| Request mentions test method validation, environmental conditioning for DVT, or test fixture qualification | dvt-protocol | Medium |
| Request mentions calibration requirements, instrument selection, or measurement correlation studies | measurement-uncertainty | Medium |
| Request mentions reliability demonstration testing, Weibull analysis, or accelerated life test sample sizing | statistical-methods | Medium |

## Shared Directives

Load Directive, Handoff Protocol, EE-Specific Standards, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
