# Scout Position -- Roster Gap Analysis

**Core recommendation:** Prioritize 3 new agents (i18n, FinOps, EE), convert 2 gaps into skill additions (a11y, QA/E2E), assign 1 to an existing agent via skills (Distributed Systems to Architect), and treat API/DevRel as a skill on Craftsman. Keep both consolidation pairs separate -- the organizational precedent strongly favors distinct risk vs. compliance roles and distinct growth vs. strategy roles.

## External Precedent Summary

Three bodies of evidence inform this analysis:

1. **Multi-agent framework patterns (CrewAI, AutoGen, LangGraph).** The 2025-2026 ecosystem consensus is that specialist agents outperform generalists by roughly 60% on accuracy in complex workflows. However, practical implementations cap at 3-5 agents per task. The key principle: specialists per task, not specialists per roster. A large standing roster is fine if the orchestrator selects a small subset per invocation. This validates the user's existing scoring-based selection approach.

2. **Consulting firm practice areas (McKinsey, BCG, Bain).** All three firms maintain both a generalist track and a specialist/expert track. McKinsey's "subject matter expert" track exists alongside generalist consultants. BCG has Expert Consulting, BCG Gamma, and BCG Platinion as parallel specialist tracks. The pattern: core generalists handle most engagements, but deep domain expertise lives in dedicated practice areas that are pulled in when needed. Critically, these firms never merge their risk/compliance practice with their strategy practice -- they serve fundamentally different clients and mental models.

3. **Architecture Review Boards (TOGAF, NASA ERB).** The recommended ARB size is 4-5 members, never exceeding 10 per review. This is the per-session constraint, not the total pool constraint. NASA's ERB draws from a larger pool of domain experts but convenes small panels. This matches the council's scoring system -- 20+ agents in the pool, 4-6 selected per deliberation.

4. **T-shaped expertise model.** The consensus is that teams should mix deep specialists with T-shaped generalists. The vertical bar (depth) justifies standalone agents; the horizontal bar (breadth) justifies skills added to existing agents. The deciding factor: does the domain require its own cognitive framework and mental models, or is it a technique that enhances an existing framework?

## Per-Gap Analysis

### Gap 1: i18n/Localization -- NEW AGENT

**Recommendation:** New Agent

**Precedent:** Localization is a standalone practice area at every major consulting firm and tech company. Google, Microsoft, and Apple all have dedicated L10n teams separate from UX. The W3C maintains i18n as a distinct working group from accessibility (WAI). The cognitive model is unique: text expansion ratios, BiDi layout, CLDR data, ICU message syntax, locale negotiation, cultural adaptation. None of this overlaps with any existing agent's mental framework.

**Why not a skill on Advocate?** Advocate's cognitive framework is "jobs to be done" and emotional journey mapping. i18n requires thinking in locale fallback chains, plural rules, and character encoding. These are orthogonal mental models. Adding i18n as a skill to Advocate would be like McKinsey asking a customer experience consultant to also handle translation management -- the domain knowledge does not transfer.

### Gap 2: Distributed Systems -- SKILL ADDITION (Architect)

**Recommendation:** Skill addition to Architect

**Precedent:** Distributed systems is an architectural concern, not a separate domain. Martin Fowler's architecture practice at ThoughtWorks treats distributed systems patterns (saga, CQRS, event sourcing, circuit breakers) as part of the architecture discipline. The TOGAF framework includes distributed computing patterns within its architecture continuum, not as a separate board. Architect already covers "system decomposition, integration patterns, scaling strategies" per its description. Consensus protocols, partitioning, and CAP theorem reasoning are extensions of architectural thinking, not a separate cognitive framework.

**What the skill should cover:** CAP theorem trade-offs, consensus protocols (Raft, Paxos), saga patterns, event sourcing, CQRS, circuit breakers, partition tolerance strategies, eventual consistency patterns.

### Gap 3: FinOps / Cost Engineering -- NEW AGENT

**Recommendation:** New Agent

**Precedent:** FinOps is a recognized, distinct discipline with its own foundation (FinOps Foundation, part of the Linux Foundation since 2022), certification program, and practitioner community. It sits at the intersection of finance, engineering, and operations but is not reducible to any of them. The FinOps Framework defines its own lifecycle (Inform, Optimize, Operate) and its own personas (FinOps Practitioner, Engineering, Finance, Procurement). Neither Strategist (business value focus) nor Operator (infrastructure focus) has the cost-modeling mental framework: unit economics, showback/chargeback, committed use discounts, spot instance strategies, resource right-sizing.

**Why not a skill on Operator or Strategist?** Operator thinks in uptime and blast radius. Strategist thinks in RICE scores and MVPs. FinOps thinks in cost-per-unit, amortization schedules, and reservation coverage. These are three distinct optimization targets that sometimes conflict (e.g., Operator wants redundancy, FinOps wants consolidation). Having them as separate voices creates productive tension in deliberation.

### Gap 4: Accessibility (a11y) Depth -- SKILL ADDITION (Advocate)

**Recommendation:** Skill addition to Advocate

**Precedent:** While large companies (Microsoft, Apple) have dedicated accessibility teams, the expertise model in consulting and review boards typically embeds a11y within UX. The W3C WAI guidelines are designed to be applied by designers and developers, not a separate discipline. Nielsen Norman Group treats accessibility as a core UX competency, not a separate practice. Advocate already lists "accessibility" in its description and its cognitive framework (user journey, progressive disclosure) naturally accommodates a11y concerns like screen reader flow and keyboard navigation.

**What the skill should cover:** WCAG 2.2 AA compliance checklist, ARIA pattern library, screen reader testing flows, color contrast requirements, keyboard navigation patterns, focus management, reduced motion preferences. This is a reference-heavy skill -- the mental model is already in Advocate, but the technical checklists need to be loadable.

### Gap 5: API Consumer / DevRel -- SKILL ADDITION (Craftsman)

**Recommendation:** Skill addition to Craftsman

**Precedent:** API design is a craft discipline. Stripe, Twilio, and other API-first companies embed API design review within their engineering quality process, not as a separate org. Google's API Design Guide is maintained by their developer infrastructure team. The cognitive model -- "pit of success" design, developer experience, clear error messages -- already exists in Craftsman's framework. SDK design, versioning strategy, and developer portal structure are extensions of DX thinking.

**What the skill should cover:** REST/GraphQL API design conventions, semantic versioning strategy, SDK design patterns, OpenAPI spec generation, developer portal structure, API changelog practices, breaking change policies.

### Gap 6: QA / E2E Testing -- SKILL ADDITION (Craftsman)

**Recommendation:** Skill addition to Craftsman

**Precedent:** Craftsman already covers "Testing strategy design (unit, integration, e2e, contract, snapshot, property-based)" in its trained skills. The test pyramid mental model is already there. Visual regression testing (Percy, Chromatic), cross-browser testing (Playwright, BrowserStack), and test design patterns are tactical extensions, not a new cognitive framework. In consulting, QA is typically part of the engineering excellence practice, not a separate practice area. ThoughtWorks, for example, includes testing strategy within their software delivery practice.

**What the skill should cover:** Visual regression testing tools and workflows, cross-browser test matrix design, E2E test architecture (page object model, fixtures), flaky test detection and quarantine, test data management, accessibility testing automation (axe-core integration).

### Gap 7: EE Fundamentals + Chip-Level Flows -- NEW AGENT

**Recommendation:** New Agent

**Precedent:** Electrical engineering is a fundamentally different discipline from computer architecture (Forge) and embedded systems (Sentinel). In semiconductor companies (Intel, TSMC, AMD), circuit design, analog/mixed-signal, power integrity, and signal integrity are separate engineering groups from microarchitecture teams. IEEE organizes these as distinct societies (Circuits and Systems Society vs. Computer Society). The user explicitly noted being unfamiliar with hardware domains and needing self-sufficient agents here. Forge covers RTL and silicon design at the microarchitecture level; EE covers the physical layer below that -- SPICE simulation, parasitic extraction, power delivery networks, clock distribution, IO standards, package design.

**Why not a skill on Forge?** Forge's mental model is "microarchitecture, silicon design, RTL security, timing closure, physical implementation." EE fundamentals operate at a different abstraction layer -- analog circuit theory, electromagnetics, semiconductor physics, power supply design. These are as different as backend engineering and database administration. A chip architect thinks in pipeline stages and cache hierarchies; an EE thinks in voltage domains and impedance matching.

## Consolidation Analysis

### Skeptic + Guardian: KEEP SEPARATE

**Precedent:** In every organizational model I surveyed, risk assessment and compliance governance are distinct functions:

- **Consulting firms:** McKinsey has separate Risk and Regulatory & Compliance practices. BCG maintains distinct Risk Management and Regulatory practices. Deloitte separates Risk Advisory from Regulatory Services.
- **Engineering orgs:** Google has a Security team (red team, threat modeling) separate from Privacy/Compliance (GDPR, data governance). AWS has Security Engineering separate from Compliance Programs.
- **TOGAF:** The Architecture Review Board (compliance, standards alignment) is a different body from the Risk Committee (threat assessment, failure analysis).

The cognitive distinction is clear: Skeptic asks "What could go wrong?" (pre-mortem, attack surface, devil's advocacy). Guardian asks "What rules apply?" (GDPR, HIPAA, SOC2, licensing). These are different questions with different knowledge bases and different outputs. Merging them would create an agent that is neither a good risk analyst nor a good compliance reviewer -- the "jack of all trades" anti-pattern that T-shaped expertise research warns against.

### Herald + Strategist: KEEP SEPARATE

**Precedent:** Growth/marketing and business strategy are distinct functions in every organization above startup stage:

- **Consulting firms:** McKinsey has separate Marketing & Sales and Strategy & Corporate Finance practices. BCG has separate Marketing, Sales & Pricing and Corporate Finance & Strategy practices.
- **Tech companies:** Growth teams (A/B testing, funnel optimization, viral loops) report separately from Product Strategy (roadmap, prioritization, market positioning).
- **The "growth vs. value" tension:** Herald optimizes for acquisition and engagement metrics (AARRR). Strategist optimizes for value delivered per unit effort (RICE, Pareto). These sometimes conflict -- Herald might want a viral sharing feature while Strategist argues it is low-impact relative to effort. This productive tension is valuable in deliberation.

Merging them would lose the ability for growth concerns to challenge strategy concerns and vice versa. The scoring system already handles the case where only one is relevant to a given deliberation.

## Risks If Ignored

- **Reinventing solved problems in i18n and FinOps.** Both domains have mature frameworks (ICU/CLDR for i18n, FinOps Foundation framework for cost engineering) that require dedicated cognitive models to apply correctly. Without dedicated agents, the council will give superficial advice in these areas, potentially worse than no advice at all.
- **Losing productive tension in consolidation.** Merging Skeptic+Guardian or Herald+Strategist removes dialectic value. The whole point of a council is diverse perspectives challenging each other. Research on Architecture Review Boards specifically recommends diverse representation over efficiency of smaller boards.
- **Hardware coverage gap persists.** The user works in semiconductor and explicitly flagged being unfamiliar with the domain. Forge covers microarchitecture but not EE fundamentals. Without a dedicated EE agent, the user has no council voice for circuit-level concerns -- the layer where their industry actually differentiates.

## Dependencies on Other Domains

- **Architect** must define how new agents integrate with the existing roster's trigger domains and skill loading patterns. New agents need clear boundaries to avoid overlap with Forge (for EE) and Operator (for FinOps).
- **Strategist** should prioritize which new agents to build first based on the user's most frequent workflow needs. My research suggests i18n and FinOps are the most mature external frameworks to draw from, making them easier to implement well.
- **Chronicler** needs to ensure new agent files follow the established structural patterns (frontmatter, cognitive framework, trained skills, communication style, decision heuristics, trigger domains).
- **Forge** should validate whether the EE gap is real from a domain perspective -- my assessment is based on organizational precedent, but Forge has the technical knowledge to confirm or refine the boundary between microarchitecture and EE fundamentals.

## Summary Table

| Gap | Recommendation | Rationale |
|-----|---------------|-----------|
| i18n/Localization | New Agent | Unique cognitive model, distinct discipline everywhere |
| Distributed Systems | Skill on Architect | Extension of architectural thinking, not separate domain |
| FinOps / Cost Engineering | New Agent | Recognized distinct discipline with own framework and lifecycle |
| Accessibility (a11y) | Skill on Advocate | Embedded in UX practice, mental model already present |
| API Consumer / DevRel | Skill on Craftsman | DX extension, not separate cognitive framework |
| QA / E2E Testing | Skill on Craftsman | Already partially covered, tactical extension only |
| EE Fundamentals | New Agent | Different abstraction layer from Forge, distinct IEEE societies |
| Skeptic + Guardian | Keep Separate | Different questions (risk vs. rules), distinct in all org models |
| Herald + Strategist | Keep Separate | Different optimization targets (growth vs. value), productive tension |

---

Sources:
- [AI Agent Selection Guide: Specialist vs General (2026)](https://www.shareuhack.com/en/posts/ai-agent-specialist-vs-general-selection-guide-2026)
- [Specialist vs Generalist AI Agents -- Expert Opinions](https://rossum.ai/blog/specialist-vs-generalist-ai-agents-expert-opinions/)
- [Multi-Agent Systems Complete 2026 Guide -- DEV Community](https://dev.to/eira-wexford/how-to-build-multi-agent-systems-complete-2026-guide-1io6)
- [Single AI Agent vs Multi-Agent Teams (2026) -- Taskade](https://www.taskade.com/blog/single-agent-systems-versus-multi-agent-ai-teams)
- [McKinsey vs BCG Comparison -- Career in Consulting](https://careerinconsulting.com/mckinsey-vs-bcg/)
- [BCG vs McKinsey 10 Key Differences](https://www.casebasix.com/pages/10-differences-between-mckinsey-bcg)
- [T-Shaped Skills -- Wikipedia](https://en.wikipedia.org/wiki/T-shaped_skills)
- [Specialists vs Generalists vs T-Shaped -- Hybrid Hacker](https://hybridhacker.email/p/specialists-vs-generalists-vs-t-shaped)
- [T-Shaped Engineers and Hardware Development -- Quilter](https://www.quilter.ai/blog/on-t-shaped-engineers-and-hardware-development-transparency-and-the-generalist-path)
- [Architecture Review Board Structure -- LeanIX](https://www.leanix.net/en/wiki/ea/architecture-review-board)
- [TOGAF Architecture Review Board](https://pubs.opengroup.org/architecture/togaf8-doc/arch/chap23.html)
- [NASA Engineering Review Board Procedure](https://www.nasa.gov/wp-content/uploads/2025/04/glpr-7123-36c.pdf)
- [Architecture Review Board Roles -- Manifestly](https://www.manifest.ly/blog/architecture-review-board-arb-roles/)
