# Architect Position -- Roster Gap Analysis

**Core recommendation:** Add 2 new agents (Distributed Systems, API Consumer/DevRel), add skills to 3 existing agents (i18n to Advocate, FinOps to Operator, a11y depth to Advocate+Artisan), defer 1 (EE fundamentals), take no action on 1 (QA/E2E). Consolidate Skeptic+Guardian but not Herald+Strategist.

---

## Per-Gap Analysis

### Gap 1: i18n / Localization

**Recommendation: Skill Addition to Advocate**

i18n is fundamentally a user-experience concern with data-model implications. The core questions -- "How do we store translations? How do we detect locale? How do we handle pluralization rules?" -- decompose into two layers:

1. **Data layer** (my domain): string tables, locale-keyed content models, database collation, right-to-left text storage. These are schema-level decisions I already handle.
2. **UX layer** (Advocate's domain): text expansion/contraction, cultural adaptation, layout mirroring for RTL, date/number formatting display.

A standalone i18n agent would be idle in most sessions. The scoring system would rarely select it. Better to add an `i18n-strategy` skill to Advocate's department, with a reference file covering the data-model patterns I would normally advise on (locale columns, translation table schemas, content fallback chains).

**Justification:** i18n spans two existing bounded contexts (UX + data) rather than forming its own. A skill gives Advocate the checklists without inflating the roster.

### Gap 2: Distributed Systems

**Recommendation: New Agent**

This is the gap I feel most strongly about. Current roster coverage:

| Concept | Closest Agent | Coverage Depth |
|---------|--------------|----------------|
| Consensus (Raft, Paxos) | Prover (formal) | Theoretical only |
| Partitioning / sharding | Architect (me) | Schema-level, not protocol-level |
| Event sourcing / CQRS | Architect (me) | Pattern-level, not failure-mode-level |
| CAP theorem trade-offs | None | Gap |
| Distributed transactions (2PC, sagas) | None | Gap |
| Service mesh / circuit breakers | Operator (partial) | Deployment, not design |
| Idempotency at scale | Craftsman (partial) | Pattern, not protocol |

No single existing agent can absorb this. I cover data-model boundaries (DDD, bounded contexts), but I do not deeply reason about network partitions, vector clocks, CRDTs, or saga orchestration failure modes. Prover covers formal properties but not practical distributed systems engineering. Operator covers deployment topology but not distributed protocol design.

A "Weaver" or "Nexus" agent -- focused on distributed systems design, consistency models, inter-service communication patterns, and partition tolerance -- fills a genuine seam in the roster.

**Trigger keywords:** `distributed`, `microservice`, `saga`, `CQRS`, `event sourcing`, `partition`, `CAP`, `consistency`, `eventual consistency`, `strong consistency`, `Raft`, `Paxos`, `CRDT`, `idempotency`, `circuit breaker`, `service mesh`, `gRPC`, `message queue`, `dead letter`, `outbox pattern`, `two-phase commit`

### Gap 3: FinOps / Cost Engineering

**Recommendation: Skill Addition to Operator**

Operator already owns infrastructure and has a `cost-analysis` skill in the registry. The gap is not agent-level -- it is skill-depth. Operator's current framing is "operational burden" which naturally extends to "operational cost."

What to add:
- Expand `cost-analysis` skill with cloud cost modeling (reserved vs on-demand, spot instances, data transfer costs)
- Add `finops-review` skill: cost tagging strategy, budget alerts, right-sizing, cost attribution to features
- Reference file with provider-specific pricing heuristics (Vercel, AWS, Supabase tiers)

This does NOT warrant a new agent. FinOps is infrastructure governance -- it belongs in the same bounded context as deployment and monitoring.

### Gap 4: Accessibility (a11y) Depth

**Recommendation: Skill Addition to Advocate + Artisan (shared reference file)**

Advocate already lists `a11y` in trigger keywords. Artisan lists `WCAG` and `contrast`. The gap is depth, not presence. Neither agent has deep skills for:
- Screen reader testing workflows
- ARIA pattern libraries
- Keyboard navigation matrices
- WCAG 2.2 AAA compliance checklists
- Cognitive accessibility (COGA)

Solution: Create a shared `a11y-deep-review` reference file in `skills/council/references/` that both Advocate and Artisan can load. Add an `a11y-audit` skill to Advocate's department that loads this reference and walks through WCAG criteria systematically.

A dedicated a11y agent would duplicate too much of Advocate's UX reasoning and Artisan's visual design reasoning. The knowledge gap is narrow (checklists and patterns), not a whole cognitive framework.

### Gap 5: API Consumer / DevRel

**Recommendation: New Agent**

This surprised me on reflection. I own API *design* (server-side contracts, resource naming, versioning). But API *consumption* -- the developer experience of using an API -- is a distinct bounded context:

| Concern | Architect (me) | Missing |
|---------|---------------|---------|
| Endpoint design | Yes | -- |
| SDK generation / design | No | Yes |
| Developer portal UX | No | Yes |
| API versioning strategy (consumer side) | Partial | Migration guides, deprecation DX |
| Rate limit communication | Contract | Client-side retry/backoff patterns |
| Webhook consumer patterns | No | Idempotent receivers, retry handling |
| API changelog / breaking change communication | No | Yes |
| Authentication DX (API keys, OAuth flows) | No | Yes |

Herald covers "growth" but not developer-facing growth. Chronicler covers docs but not interactive API documentation (playground, sandbox). This is a distinct persona: someone who thinks "I am a developer integrating with this API -- is this experience good?"

Name suggestion: **Envoy** -- the API consumer and developer relations lens. Trigger keywords: `SDK`, `developer portal`, `API key`, `OAuth`, `developer experience`, `integration guide`, `sandbox`, `playground`, `API changelog`, `deprecation`, `webhook consumer`, `client library`, `rate limit`, `backoff`, `retry`.

### Gap 6: QA / E2E Testing

**Recommendation: No Action**

Current coverage analysis:

- **Craftsman** owns testing strategy, test pyramid, e2e (in trigger keywords)
- **Advocate** covers interaction flows (which define what e2e tests validate)
- **Artisan** covers visual design (which defines visual regression baselines)
- **Operator** covers CI/CD pipelines (which run the tests)

The missing pieces -- visual regression tooling (Chromatic, Percy), cross-browser matrices, test data management -- are tool-level concerns, not cognitive-framework-level concerns. Craftsman's `testing-strategy` skill can be enriched with an `e2e-testing` reference file covering:
- Visual regression tool selection
- Cross-browser test matrix design
- Test data factory patterns
- Flaky test triage workflow

This is a skill enhancement to Craftsman, not even a new skill -- it is a reference file addition.

### Gap 7: EE Fundamentals + Chip-Level Flows

**Recommendation: No Action (defer)**

Current hardware coverage:

| Agent | Domain |
|-------|--------|
| Forge | Microarchitecture, RTL, silicon design, timing, physical implementation |
| Sentinel | IoT, embedded firmware, device protocols, fleet management |
| Warden | Kernel security, privilege boundaries, HW/SW interface |
| Cipher | Cryptographic protocols, key management, hardware security modules |

What is missing: analog/mixed-signal, power delivery networks, signal integrity, package-level design, semiconductor manufacturing flows (fab, test, packaging), EDA tool workflows. These are genuine gaps, but:

1. The user stated this is a *future* consideration and they are *unfamiliar* with the domain.
2. An agent in an unfamiliar domain must be self-sufficient, meaning the persona definition must encode deep domain knowledge. Building this well requires domain validation the user cannot yet provide.
3. Forge already covers digital design; extending Forge with an `ee-fundamentals` skill set is possible but risks overloading a focused persona.

**Defer until the user's semiconductor work generates concrete use cases.** At that point, consider a dedicated "Circuit" or "Silicon" agent focused on the analog/physical layer that Forge does not cover.

---

## Consolidation Analysis

### Skeptic + Guardian: CONSOLIDATE

**Recommendation: Merge into a single agent**

Boundary analysis:

| Dimension | Skeptic | Guardian |
|-----------|---------|----------|
| Core lens | Risk, failure modes, attack surface | Compliance, privacy, governance |
| Mental model | Pre-mortem, Swiss cheese, attack surface | Regulatory awareness, privacy by design |
| Output type | Risk register, edge cases | Compliance map, data classification |
| Trigger overlap | `security`, `auth*`, `encryption`, `production`, `incident` | `compliance`, `privacy`, `audit`, `data retention` |

The overlap is significant. Both agents fundamentally ask: "What could go wrong, and what rules/constraints prevent it?" Guardian's compliance lens is a *specialization* of Skeptic's risk lens -- regulatory risk is a category of risk.

**Proposed merge: "Sentinel" name is taken. Use "Guardian" as the merged name with expanded scope.**

Merged trigger domains combine both keyword sets. Merged cognitive framework:
- Pre-mortem analysis (from Skeptic)
- Attack surface thinking (from Skeptic)
- Regulatory awareness (from Guardian)
- Privacy by design (from Guardian)
- Swiss cheese model (from Skeptic -- applies to both compliance and security)
- Data lifecycle thinking (from Guardian)

Skills from both departments merge: `threat-model`, `failure-mode-analysis`, `edge-case-enumeration` (Skeptic) + `compliance-review`, `data-classification`, `audit-trail-design` (Guardian) = 6 skills, which is reasonable.

**Risk of NOT merging:** In deliberations, Skeptic and Guardian frequently argue the same side with slightly different vocabulary. This wastes deliberation rounds. A merged agent says it once, covering both the security and compliance angles.

### Herald + Strategist: DO NOT CONSOLIDATE

**Recommendation: Keep separate**

These agents have superficial overlap (both talk about "business") but fundamentally different bounded contexts:

| Dimension | Herald | Strategist |
|-----------|--------|------------|
| Core question | "How does this grow?" | "What should we build?" |
| Time horizon | Post-launch (acquisition, retention, monetization) | Pre-launch (scoping, prioritization, sequencing) |
| Output type | Growth loops, pricing models, funnel optimization | MVP scope, RICE scores, roadmap phases |
| Data dependency | User behavior data, cohort analysis, funnel metrics | Requirements, stakeholder input, effort estimates |
| Trigger overlap | Only `metric` overlaps | Only `metric` overlaps |

Herald optimizes for distribution and monetization after the product exists. Strategist optimizes for what to build and in what order. These are distinct decision-making frameworks that apply at different lifecycle stages.

Merging them would create a bloated agent that is summoned too often (any "business" keyword) and whose cognitive framework tries to serve two masters -- the "should we build it?" question and the "how do we spread it?" question.

**Keep them separate. The scoring system already handles selection.**

---

## Risks If Ignored

- **Distributed systems gap produces architectural blind spots.** As the user builds services that communicate over networks, no agent will catch saga failure modes, partition tolerance issues, or consistency model mismatches. I can identify the data boundaries, but I cannot deeply reason about what happens when the network between those boundaries fails.
- **API consumer experience degrades silently.** Without an agent thinking from the consumer side, APIs will be well-designed internally but frustrating to integrate with. SDK ergonomics, authentication DX, and deprecation communication will be afterthoughts.
- **Unconsolidated Skeptic+Guardian wastes deliberation bandwidth.** Two agents making overlapping risk arguments consume round capacity that could go to agents with genuinely distinct perspectives.

---

## Dependencies on Other Domains

- **Advocate** must accept i18n skill addition and shared a11y reference file -- this expands their department scope.
- **Operator** must accept FinOps skill expansion -- this requires updating their cognitive framework to include cost optimization, not just cost awareness.
- **Craftsman** must accept that QA/E2E is their domain, not a new agent's. Their testing-strategy skill needs enrichment.
- **Artisan** must participate in the shared a11y reference file, contributing visual-specific criteria (contrast ratios, focus indicators, color-blind-safe palettes).
- **Skeptic and Guardian agents** must agree on merged identity, keyword set, and skill consolidation. The merged agent's cognitive framework must not lose either perspective's unique heuristics.

---

## Summary Table

| Gap | Recommendation | Target | Justification |
|-----|---------------|--------|---------------|
| i18n | Skill Addition | Advocate | Spans UX + data; too narrow for standalone agent |
| Distributed Systems | **New Agent** | -- | No existing agent covers protocols, consistency, partitions |
| FinOps | Skill Addition | Operator | Natural extension of infrastructure ownership |
| a11y Depth | Skill Addition | Advocate + Artisan | Depth gap, not framework gap; shared reference file |
| API Consumer/DevRel | **New Agent** | -- | Distinct bounded context from API design |
| QA/E2E | No Action | Craftsman (enrich) | Tool-level gap, not cognitive-framework gap |
| EE Fundamentals | No Action (defer) | -- | User unfamiliar; needs concrete use cases first |
| Skeptic+Guardian | **Consolidate** | Merged "Guardian" | Overlapping risk lens wastes deliberation rounds |
| Herald+Strategist | **Keep Separate** | -- | Different lifecycle stages, different core questions |
