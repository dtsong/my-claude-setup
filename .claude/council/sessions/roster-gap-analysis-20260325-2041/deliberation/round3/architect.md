# Architect Final Position -- Roster Gap Analysis

## Revised Recommendation

Add 1 new agent (Distributed Systems), add skills to 3 existing agents (i18n, a11y, FinOps), distribute API/DevRel across existing agents, keep all consolidation candidates separate, and support Forge+Strategist's emerging hardware boundary proposal as a deferred new agent with a concrete trigger condition.

---

## Concessions Made

1. **API Consumer/DevRel -- withdrawn as new agent.** Skeptic correctly identified that this bounded context dissolves under scrutiny. SDK ergonomics is Craftsman's domain (developer experience), API documentation is Chronicler's domain, and API versioning contracts are mine. Three skill additions cover the gap without a 21st agent. I was over-indexing on the consumer/producer distinction when the actual work product (good docs, good types, good deprecation paths) maps cleanly to existing frameworks.

2. **Skeptic+Guardian merge -- withdrawn.** Five of six agents oppose. Skeptic's argument that technical risk and regulatory risk have different remediation playbooks is correct at the operational level. A SQL injection triggers an incident response; a GDPR violation triggers a legal response. These are different escalation paths even if both agents ask "what could go wrong?" My deliberation-bandwidth concern is addressed by a shared `risk-register` reference file rather than a merge.

3. **EE Fundamentals -- shifted from "no action" to "conditional new agent."** Forge and Strategist's Round 2 convergence produced a cleaner boundary than I had considered. Forge keeps security analysis (side-channels, timing, speculation). A future agent handles constructive chip design (verification, synthesis, SoC integration, EDA flows). This is a natural seam -- "design teams build, security teams audit" -- and I endorse the boundary. But I add a trigger condition: defer creation until the user has run 3+ council sessions involving hardware topics. That gives empirical data on what Forge can and cannot handle alone.

---

## Non-Negotiables

**Distributed Systems must be a new agent, not a skill addition to Architect.**

This is the hill I will defend. Here is the structural argument:

Every agent on this council is defined by a *cognitive framework* -- a set of mental models that determine how they decompose problems. My framework is: C4 Model, Domain-Driven Design, Data Gravity, Mechanical Sympathy. These models answer the question: **"Where should boundaries be, and how should data flow between them?"**

Distributed systems reasoning answers a fundamentally different question: **"What happens when those boundaries cannot communicate reliably?"** The mental models required are:

| Mental Model | Purpose | Overlap with Architect |
|---|---|---|
| CAP theorem reasoning | Trade-off analysis under partition | None -- I design assuming connectivity |
| Failure detector design | Distinguishing slow from dead | None -- I design assuming liveness |
| Consistency model selection | Linearizable vs eventual vs causal | Partial -- I pick isolation levels, not consistency protocols |
| Saga/compensation design | Multi-service transaction recovery | None -- I design single-boundary transactions |
| Backpressure and flow control | System stability under load | None -- Tuner handles performance, not protocol stability |

Absorbing this into my persona would require adding 4-5 new mental models, 25+ trigger keywords, and 3+ new skills. The result would be an agent with 8-9 mental models spanning two distinct reasoning disciplines. That violates the design principle this entire roster is built on: each agent has a focused cognitive frame that produces clear, non-overlapping analysis.

Skeptic calls this "empire-building." I call it boundary integrity -- the same principle I apply to every system I design. You do not put your order service and your payment service in the same bounded context just because they are related. They have different invariants, different failure modes, and different scaling characteristics. So do "system design" and "distributed systems design."

**Practical trigger test:** When the user asks "Should I use Kafka or a REST callback for this integration?" -- that question requires reasoning about delivery guarantees, ordering semantics, consumer group rebalancing, and dead-letter handling. None of those concepts exist in my cognitive framework. Today, no agent on the roster can answer that question with depth.

---

## Implementation Notes

### Immediate actions (unanimous consensus)

1. **i18n skill to Advocate**
   - New skill: `skills/council/advocate/i18n-strategy/SKILL.md`
   - New reference: `skills/council/references/i18n-data-patterns.md` (locale column schemas, translation table designs, content fallback chains -- contributed by Architect)
   - Add trigger keywords to Advocate: `i18n`, `localization`, `locale`, `translation`, `RTL`, `internationalization`, `pluralization`, `ICU`

2. **a11y depth to Advocate + Artisan**
   - New skill: `skills/council/advocate/a11y-audit/SKILL.md`
   - New shared reference: `skills/council/references/a11y-deep-review.md` (WCAG 2.2 checklist, ARIA patterns, keyboard nav matrix, screen reader testing)
   - Artisan loads the same reference when visual accessibility criteria are relevant
   - Add trigger keywords to Advocate: `screen reader`, `ARIA`, `keyboard navigation`, `WCAG 2.2`, `cognitive accessibility`

3. **FinOps skill to Operator**
   - Enrich existing `skills/council/operator/cost-analysis/SKILL.md` with cloud cost modeling
   - New skill: `skills/council/operator/finops-review/SKILL.md` (cost tagging, budget alerts, right-sizing, cost attribution)
   - New reference: `skills/council/references/cloud-pricing-heuristics.md`
   - Add trigger keywords to Operator: `cost`, `pricing`, `budget`, `FinOps`, `reserved instance`, `spot instance`, `right-sizing`

4. **API Consumer/DevRel distributed across existing agents**
   - Craftsman: new `sdk-design` skill (type safety, error handling ergonomics, client generation)
   - Chronicler: new `api-documentation` skill (interactive docs, playground, migration guides)
   - Architect: expand `api-design` skill to include consumer-side concerns (deprecation strategy, versioning communication, webhook receiver patterns)

5. **Shared risk-register reference**
   - New reference: `skills/council/references/risk-register-template.md`
   - Used by both Skeptic (technical risks) and Guardian (compliance risks) to structure outputs consistently without merging their personas

### Deferred actions (conditional)

6. **Distributed Systems agent**
   - Trigger condition: user approval in this deliberation
   - Working name: open for discussion (Weaver, Nexus, or other)
   - Department: `skills/council/<name>/` with skills: `consistency-modeling`, `saga-design`, `integration-patterns`
   - Trigger keywords listed in Round 1 position

7. **Constructive EE / Chip Design agent**
   - Trigger condition: 3+ council sessions involving hardware topics where Forge identifies out-of-scope questions
   - Boundary: constructive design (verification, synthesis, SoC integration, EDA flows) -- Forge retains security analysis
   - Not scoped yet -- requires domain validation from the user

### Governance compliance

All new skills and references must comply with the Skill Governance Spec:
- Skill SKILL.md files: 2,000 tokens max
- Reference files: 1,500 tokens max
- Maximum simultaneous context load: 5,000 tokens
- No cross-references between specialist skills
- Run `pre-commit run --all-files` after creation

---

## Final Summary Table

| Gap | Round 1 | Round 3 | Change Reason |
|-----|---------|---------|---------------|
| i18n | Skill to Advocate | Skill to Advocate | No change -- unanimous |
| Distributed Systems | New Agent | **New Agent** | Maintained -- cognitive frame argument |
| FinOps | Skill to Operator | Skill to Operator | No change -- unanimous |
| a11y Depth | Skill to Advocate+Artisan | Skill to Advocate+Artisan | No change -- unanimous |
| API Consumer/DevRel | New Agent | **Skill additions x3** | Conceded to Skeptic -- distributes cleanly |
| QA/E2E | No Action | No Action | No change |
| EE Fundamentals | No Action (defer) | **Conditional new agent** | Adopted Forge+Strategist boundary proposal |
| Skeptic+Guardian | Consolidate | **Keep separate** | Conceded -- different remediation domains |
| Herald+Strategist | Keep separate | Keep separate | No change -- unanimous |
