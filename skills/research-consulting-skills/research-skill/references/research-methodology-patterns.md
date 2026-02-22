# Research Methodology Patterns

## Methodology Selection

| Methodology | Use When | Output |
|---|---|---|
| Systematic Review Lite | Defensible evidence base for procurement/policy decisions | Evidence synthesis with inclusion/exclusion audit trail |
| Landscape Analysis | Scanning a domain to identify all relevant options | Market map with categorized candidates |
| Competitive Intelligence | Comparing 2-5 specific technologies head-to-head | Capability comparison matrix |
| MECE Decomposition | Structuring any research question before investigation | Question tree with evidence requirements |

---

## 1. Systematic Review Lite

Adapted PRISMA for consulting. Retains search discipline and audit trail; compresses to hours.

**Protocol (define before searching):** Research question (PICO), inclusion/exclusion criteria (tech type, date range, sector, TRL min), search strategy (databases, terms, date range).

**Execution log:** Databases, exact queries, results found/screened/included, exclusion reasons.

**Screening:** Title/abstract pass (generous) then full-text (strict). Document exclusion reason per rejected source. Apply source tier to all included.

**Extraction per source:** Key claims, supporting data, methodology, limitations, biases.

---

## 2. Landscape Analysis

**Boundaries:** Technology domain, geographic scope, segments (enterprise/SMB/gov), deployment models, TRL floor, exclusions.

**Dimension pairs:**

| Pair | Use When |
|---|---|
| Maturity vs. Capability breadth | Maturing market |
| Enterprise vs. Developer focus | Enterprise vs. dev tools |
| Open-source vs. Proprietary | Build-vs-buy research |
| Specialization vs. Platform breadth | Best-of-breed vs. platform |
| Market penetration vs. Innovation | Established vs. emerging |

**Scan sequence:** Advisory (Gartner MQ, Forrester Wave, ThoughtWorks Radar) first, then standards/academic, then industry-specific, then vendor/community for emerging options.

**Output:** Per-category table (candidate, TRL, differentiator, source, tier) + Notable Absences + Landscape Observations.

---

## 3. Competitive Intelligence

**Setup:** Define framework before gathering -- dimensions, candidates, weighting, scale, minimum evidence threshold.

**Symmetric gathering (critical):** Gather evidence on ALL candidates per dimension before moving to next. Prevents deep-diving one while skimming others.

**Flag asymmetries:** Information advantage (one has more public evidence), tier imbalance (one Tier A, others Tier C), recency gaps.

---

## 4. MECE Decomposition Patterns

Apply at Phase 1 start. Five patterns by research type:

**Pattern 1 -- Evaluation Dimension:** "Should we adopt X?" Decompose by: security, vendor viability, compliance, integration, org capacity, exit strategy, TCO.

**Pattern 2 -- Stakeholder:** "What platform best serves us?" Decompose by: technical users, business users, IT ops, security/compliance, procurement, executive leadership.

**Pattern 3 -- Lifecycle:** "Is X feasible?" Decompose by: acquisition, implementation, operation, evolution, exit.

**Pattern 4 -- Market Structure:** "What does the landscape look like?" Decompose by: market leaders (TRL 8-9), challengers (TRL 6-7), niche/specialized, emerging (TRL 4-6), open-source, market trajectory.

**Pattern 5 -- Risk-First:** "What are the risks of adopting X?" Decompose by: security/sovereignty, operational/continuity, regulatory/compliance, integration/migration, organizational/change, lock-in/reversibility, sector-specific.

**Quality test:** (1) No single evidence piece answers two sub-questions (mutual exclusivity). (2) All sub-questions together fully answer the primary question (exhaustive). (3) Each sub-question has a known evidence source (actionable). (4) Sub-questions are comparable in scope (proportionate).

---

## 5. Search Strategy Templates

**Academic/Standards (Tier A):** Google Scholar, IEEE Xplore, ACM DL, NIST, ISO, arXiv. Terms: "[tech]" AND [evaluation/comparison/assessment]. Filter: last N months.

**Advisory/Analyst (Tier B):** Gartner (MQ, Hype Cycle), Forrester (Wave, TechRadar), IDC (MarketScape), ThoughtWorks Radar. Note paywalled access.

**Government/Regulatory (Tier A):** NIST CSRC, FedRAMP, GAO Reports, ENISA, UK NCSC, sector regulators (FDA, FCC, CFTC).

**Industry/Trade (Tier B/C):** Sector publications (GovTech/FedScoop, HIMSS, AgFunder/CGIAR). Check for sponsored content.

**Vendor (Tier C):** Product site, docs, API refs, pricing, compliance center, changelog, repos. Flag non-spec claims as [VENDOR-AUTHORED].

---

## 6. Evidence Synthesis Patterns

**Narrative synthesis:** Group by theme, order strongest-to-weakest tier, identify agreement/disagreement, synthesize consensus with caveats, assign confidence.

**Matrix synthesis:** Define dimensions (rows) x candidates (columns). Rate each cell with confidence. Attach tier mix. Identify pattern and sensitivity.

**Convergence synthesis:** Gather evidence from 3+ independent source types. Assess convergence:
- Strong (3+ types agree) = supports High confidence
- Moderate (2 agree, 1 absent) = supports Medium
- Divergence (types disagree) = forces Low, investigate
- Insufficient (<2 types) = forces Low

**Gap-centered synthesis:** Start with what evidence should exist for the technology's maturity/category. Document found vs. expected. Analyze gap pattern (random, systematic, informative). Absence of expected evidence is a signal.

---

## 7. Special Research Modes

**Delta mode** (prior art <18 months): Load prior as baseline. Focus on changes. Re-evaluate only dimensions with new evidence. Flag classification changes. Document unchanged items. Output: "Delta from [prior ID] dated [date]."

**Rapid assessment** (<30 min): Skip prior art. Priority 2-3 sources only. Top 3 candidates, top 4 dimensions. Narrative comparison. Disclosure: "Rapid assessment, abbreviated process, limited coverage, preliminary confidence."

**Regulatory focus:** Elevate standards/industry to co-primary. Add regulatory websites, enforcement DBs, certification registries. Structure around regulatory requirements. Include mapping table. Flag pending regulation within timeline.
