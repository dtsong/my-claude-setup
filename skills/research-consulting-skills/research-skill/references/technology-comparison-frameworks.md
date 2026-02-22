# Technology Comparison Frameworks

## Framework Selection

| Framework | Use When | Key Input |
|---|---|---|
| Build-vs-Buy | Custom dev vs. commercial/OSS | Cost, capability reqs, risk tolerance |
| Vendor Scorecard | Evaluating vendor proposals | Vendor docs, references, analyst reports |
| Feature Matrix | Comparing functional/non-functional caps | Product docs, demos, technical evals |
| Maturity Comparison | Options at different maturity stages | TRL assessments, adoption data |
| Multi-Criteria Scoring | Ranking 3+ options with priorities | Evidence from prior frameworks |
| Side-by-Side Template | Final comparison for decision-makers | All preceding analysis |

---

## 1. Build-vs-Buy Decision Matrix

**Seven dimensions:** TCO, Time to Value, Fit to Requirements, Maintenance & Evolution, Risk Profile, Strategic Alignment, Organizational Capacity.

**Scoring:** 1-5 per dimension (1 = strongly favors the other option; 3 = neutral; 5 = strongly favors this option). Weights must sum to 100%.

**Decision rules:**

| Scenario | Recommendation |
|---|---|
| Buy exceeds Build by >20% | Buy. |
| Scores within 20% | Further investigation -- run sensitivity analysis on highest-weighted dimensions. |
| Build exceeds Buy by >20% | Build. |
| Build wins Fit+Strategy, Buy wins TCO+Risk | Investigate hybrid: buy the platform, build the differentiating layer. |

**Government adjustment:** Add 8th dimension "Procurement Process Compatibility" -- custom builds may bypass lengthy procurement cycles via existing contracting vehicles.

**Open-source:** Split "Buy" into "Adopt Open-Source" and "Buy Commercial" -- distinct risk and cost profiles.

---

## 2. Vendor Evaluation Scorecard

**Five dimensions with default weights:**

| Dimension | Weight | 1 (Poor) | 3 (Adequate) | 5 (Strong) |
|---|---|---|---|---|
| Org Stability | 20% | Pre-revenue, <20 staff | Series B+, 20-100, growing | Profitable, 100+, diversified |
| Product Maturity | 20% | Beta/<1yr GA | GA 1-3yr, quarterly releases | GA 3+yr, stable APIs |
| Support Quality | 15% | Email-only, no SLA | Tiered with SLAs | 24/7 with escalation paths |
| Security & Compliance | 25% | No certifications | SOC 2 Type I in progress | SOC 2 II + FedRAMP/ISO 27001 |
| Commercial Terms | 20% | Lock-in, opaque pricing | Annual, published tiers | Month-to-month, full portability |

**Output:** Per-vendor weighted total + confidence per dimension + disqualifying flags.

**Categories:** Advance / Advance with conditions / Do not advance.

**Gov adjustment:** Security & Compliance to 30-35%. Add "Continuity and Escrow" for startup vendors.

---

## 3. Feature Comparison Matrix

**Three-layer structure:** Functional (what it does), Non-Functional (how well), Operational (what it takes to run).

**Functional ratings:** Yes / Partial (document gap) / No / Roadmap (date + confidence).

**Requirement priority:** Must / Should / Could. Summarize: "Must Haves met: [A: N/N] [B: N/N]".

**Non-functional:** Source tier per cell. Vendor claims = Tier C. Independent benchmarks = Tier A/B.

**Operational:** Deployment model, complexity, infra reqs, monitoring, backup/recovery, upgrade process, skills, timeline.

---

## 4. Technology Maturity Comparison

Use when comparing options at different TRL levels (e.g., TRL 8-9 vs TRL 5-6).

**Factors:** TRL score, production track record, ecosystem maturity, talent availability, innovation, architecture modernity, community momentum.

**Risk overlay:** Delivery, support, roadmap, talent, innovation, lock-in per option.

**TRL minimums by risk tolerance:**

| Client Risk Tolerance | Production Min | Pilot Min |
|---|---|---|
| Conservative (gov, healthcare, critical infra) | TRL 8+ | TRL 6+ |
| Moderate (enterprise, financial services) | TRL 7+ | TRL 5+ |
| Aggressive (startups, innovation labs) | TRL 5+ | TRL 3+ |

---

## 5. Weighted Multi-Criteria Scoring

**Weight rules:**
- Sum to 100%
- No single criterion >30%
- No criterion <5% (remove if that unimportant)
- Weights must reflect engagement brief priorities

**Scale:** 5=Excellent, 4=Good, 3=Adequate, 2=Below expectations, 1=Poor, 0=Disqualifying.

**Per score:** Numeric value, one-line rationale, confidence (H/M/L), evidence source + tier.

**Sensitivity analysis (mandatory):**
1. Top-weighted criterion +10% -- ranking change?
2. Any M/L confidence score -1 -- ranking change?
3. Remove lowest-weighted criterion -- ranking change?

Flag as sensitive if ranking unstable under any test.

---

## 6. Side-by-Side Output Template

```
# Technology Comparison: [Technology Area]
Engagement: [ID] | Date: [YYYY-MM-DD]
Candidates: [Count] shortlisted from [count] in landscape scan

## Executive Summary
[3-5 sentences: leader, why, key trade-off, what remains uncertain]

## Comparison at a Glance
| Dimension | [Leader] | [Alt 1] | [Alt 2] |
|---|---|---|---|
| Recommendation | **Recommended** | Viable alternative | Conditional |
| Weighted score | [N.NN] | [N.NN] | [N.NN] |
| Strongest dimension | | | |
| Weakest dimension | | | |
| Key risk | | | |
| Estimated TCO (N-yr) | [$range] | [$range] | [$range] |
| TRL | [N] | [N] | [N] |

## Detailed Comparison
[Per dimension: 2-3 sentences per candidate with source citations and tier tags]
[Dimension winner + confidence]

## Trade-Off Analysis
[Key trade-offs the scoring cannot fully capture]

## Sensitivity Analysis
[What would change the ranking and under what conditions]

## Gaps and Uncertainties
[Unresolved items requiring consultant or client action]
```

**Audience:** Executive = glance table, top 3-4 dimensions. Technical = expanded comparison with raw evidence. Procurement = align with RFP eval criteria.
