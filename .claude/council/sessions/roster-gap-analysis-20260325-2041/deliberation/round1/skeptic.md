# Skeptic Position -- Roster Gap Analysis

## Core Recommendation

**Do not expand the roster.** With 20 agents, 60 skills, and ZERO usage across every single department, the council has a utilization crisis, not a coverage crisis. Adding agents to a system that has never been stress-tested is premature optimization of the worst kind -- you are designing a building you have never occupied.

## The Elephant in the Room: Zero Usage

Before analyzing any gap, I need to state the obvious. The registry shows `"uses": 0` for all 60 skills across all 20 departments. Not a single agent has been battle-tested. We have no empirical data on:

- Which agents actually get invoked in real deliberations
- Whether the existing agent boundaries are drawn correctly
- Whether skills are discoverable and useful in practice
- Whether the current roster already covers these "gaps" adequately via general reasoning

**Any gap analysis conducted without usage data is speculative.** We are pattern-matching against theoretical coverage maps, not actual failures. The correct first move is to USE the council, identify real coverage failures from real sessions, and then fill gaps based on evidence.

## Per-Gap Analysis

### Gap 1: i18n/Localization -- NO ACTION

**Severity: Low | Recommendation: No Action**

This is a real domain but not a real gap for this user. The interview context lists: fullstack web, CLI/dev-infra, AI/ML, semiconductor. None of these scream "multi-language consumer product." i18n matters when you are shipping a product to international markets. A CLI tool for a single developer does not need RTL support.

If this need materializes, Advocate can carry a `localization-checklist` skill. Creating an entire agent persona for i18n is like hiring a full-time translator for a team that only writes English.

**Challenge question:** When was the last time the user actually needed i18n guidance? If the answer is "never," this gap is imaginary.

### Gap 2: Distributed Systems -- SKILL ADDITION (to Architect)

**Severity: Medium | Recommendation: Skill Addition to Architect**

Distributed systems thinking (consensus, partitioning, CAP theorem) is genuinely useful for backend architecture decisions. But it does not warrant a new agent. Architect already covers system design. Adding a `distributed-systems` skill with reference material on consensus protocols, partition tolerance patterns, and eventual consistency trade-offs extends Architect naturally.

A standalone Distributed Systems agent would overlap heavily with Architect (system boundaries), Operator (deployment topology), and Tuner (performance under partition). The coordination cost of yet another agent in deliberations outweighs the specialization benefit.

**Risk of a new agent:** Architect and a hypothetical "Distributor" would argue over system design decisions in every session, wasting deliberation rounds on turf disputes.

### Gap 3: FinOps / Cost Engineering -- NO ACTION (already covered)

**Severity: Low | Recommendation: No Action**

Look at the registry. Operator already has a `cost-analysis` skill. Strategist has `impact-estimation`. The gap description says this "falls between Strategist and Operator" -- but that is exactly where it should live. Cost is both an operational concern (infrastructure spend) and a strategic concern (ROI). Having both agents weigh in during deliberation IS the design working correctly.

Creating a FinOps agent for a single developer's projects is overhead theater. This agent would sit idle in 95% of deliberations. If the cost-analysis skill in Operator is insufficient, improve the skill, do not create an agent.

**Challenge question:** What specific cost engineering question has gone unanswered because Operator and Strategist could not handle it?

### Gap 4: Accessibility (a11y) Depth -- SKILL ADDITION (to Advocate)

**Severity: Medium | Recommendation: Skill Addition to Advocate**

Advocate's description explicitly includes accessibility. The real question is whether Advocate's a11y coverage is deep enough. The answer is: we do not know, because Advocate has never been used (0 invocations).

The correct action is to add an `a11y-audit` skill to Advocate's department with WCAG 2.2 reference material, ARIA pattern guides, and screen reader testing checklists. This gives Advocate the depth without the overhead of a new agent.

A dedicated a11y agent would be invoked only on frontend tasks, sitting idle during CLI, AI/ML, and semiconductor work. That is 3 out of 4 of the user's domains where it contributes nothing.

**Critical caveat:** If the user starts building consumer-facing products at scale, revisit this. For now, a skill is sufficient.

### Gap 5: API Consumer / DevRel -- NO ACTION

**Severity: Low | Recommendation: No Action**

Architect already has an `api-design` skill. Herald covers developer experience from a growth perspective. The gap description mentions "SDK design, developer portal, API versioning" -- but SDK design is architecture, developer portals are documentation (Chronicler), and API versioning is already in Architect's wheelhouse.

This gap is three existing agents' responsibilities dressed up as a new role. Unless the user is building a public API platform business, this is a solution looking for a problem.

**Challenge question:** Is the user shipping public APIs that external developers consume? If not, DevRel is irrelevant.

### Gap 6: QA / E2E Testing -- SKILL ADDITION (to Craftsman)

**Severity: Medium | Recommendation: Skill Addition to Craftsman**

Craftsman has a `testing-strategy` skill. The gap identifies visual regression, cross-browser, and test design as missing. These are testing concerns -- they belong in Craftsman's department.

Adding an `e2e-testing` skill to Craftsman with visual regression patterns, cross-browser matrices, and test design heuristics is the right move. A standalone QA agent would duplicate Craftsman's testing-strategy skill and create confusion about which agent owns "testing."

However, I want to flag a real risk: Craftsman's current scope (code quality + testing + patterns) may be too broad. If Craftsman becomes a dumping ground for every quality concern, the agent's focus dilutes. Watch for this.

### Gap 7: EE Fundamentals + Chip-Level Flows -- REQUIRES INVESTIGATION

**Severity: High (if real) | Recommendation: Investigate before acting**

This is the only gap I take seriously as potentially requiring a new agent, and also the one I am most suspicious of.

The roster already has THREE hardware-adjacent agents: Forge (microarchitecture, RTL, silicon), Sentinel (IoT, embedded, edge), and Warden (hw-sw boundary, isolation, kernel hardening). Plus Cipher for cryptographic protocol security.

The gap description says "EE fundamentals + chip-level flows" and notes the user is "UNFAMILIAR with hardware domains." This raises critical questions:

1. **What specifically is missing?** "EE fundamentals" is enormously broad -- analog design? power integrity? signal integrity? PCB layout? FPGA? ASIC verification? Each of these is its own discipline.
2. **Can an LLM-based agent meaningfully cover hardware domains where the user lacks the background to evaluate the output?** This is a safety concern. If Forge tells the user something about RTL timing closure and the user cannot validate it, the agent could produce plausible-sounding nonsense. Adding MORE agents in this domain compounds the risk.
3. **Do Forge, Sentinel, and Warden already cover "chip-level flows"?** Forge explicitly covers "pipeline stages, cache hierarchies, physical implementation." Warden covers "hw-sw boundary." What flow falls between these?

**My position:** Before creating anything, the user needs to articulate 3-5 specific semiconductor questions that went unanswered. If Forge/Sentinel/Warden can answer them, the gap is illusory. If they cannot, we need to understand exactly what domain to fill before creating an agent with a vague mandate.

**Risk of premature action:** A vaguely-scoped "EE agent" becomes a junk drawer for hardware questions, producing low-quality answers because its persona tries to cover too much.

## Consolidation Analysis

### Skeptic + Guardian: DO NOT MERGE -- Critical

**What gets lost:**

These agents have fundamentally different cognitive frameworks and different failure modes.

- **Skeptic** thinks in attack surfaces, failure modes, and pre-mortems. I ask "what could go wrong?" at a technical level. My outputs are risk registers, threat models, and edge case lists.
- **Guardian** thinks in regulatory frameworks, data lifecycles, and compliance regimes. Guardian asks "are we legally allowed to do this?" and "what audit trail do we need?" Guardian's outputs are compliance maps, data classification schemas, and audit trail designs.

Merging them conflates two distinct failure domains: **technical risk** and **regulatory risk**. A system can be technically robust but legally non-compliant (storing EU user data in a US-only region). A system can be fully compliant but technically fragile (passes SOC2 audit but has race conditions in the auth flow).

In deliberation, a merged agent would have to context-switch between "does this have a SQL injection vulnerability?" and "does this data processing have a GDPR lawful basis?" These are not related analyses. They require different mental models, different checklists, and different reference materials.

**The real risk of merging:** Compliance concerns get subordinated to security concerns (or vice versa) because a single agent cannot hold both frames simultaneously with equal weight. You end up with a security agent that occasionally remembers to mention GDPR, or a compliance agent that occasionally mentions XSS. Neither is acceptable.

**Verdict: Non-negotiable. Do not merge.**

### Herald + Strategist: CONDITIONALLY ACCEPTABLE -- Medium

**What gets lost:**

Less than the Skeptic+Guardian merge, but still meaningful.

- **Herald** thinks in funnels, viral loops, and user lifecycle (AARRR). Herald designs for growth and engagement.
- **Strategist** thinks in value per effort, MVP scoping, and prioritization (RICE). Strategist designs for business impact and scope control.

The overlap: both care about "is this worth building?" But they answer from different angles. Strategist says "this is highest ROI for engineering time." Herald says "this drives the most acquisition/retention." These can conflict -- the highest ROI feature might not be the best growth lever.

**What makes this conditionally acceptable:** For a single developer (not a product team), the distinction between "business value" and "growth strategy" is academic. The user is not running A/B tests on pricing tiers or optimizing viral coefficients. A merged "Value + Growth" agent could work IF the persona carefully preserves both the scope-cutting discipline of Strategist and the user-lifecycle thinking of Herald.

**What makes me nervous:** Strategist's core value is saying NO -- cutting scope, killing features, enforcing MVP discipline. Herald's core value is saying YES -- more features, more engagement hooks, more growth loops. Merging an agent whose job is "build less" with an agent whose job is "build more to grow" creates internal tension that could neutralize both perspectives.

**Verdict: Acceptable only if the merged persona explicitly preserves Strategist's scope-cutting authority as the dominant frame, with Herald's growth lens as a secondary consideration.**

## Risks If Ignored

- **Roster bloat without validation (Critical):** Adding agents to an untested system creates maintenance burden (skill files, eval cases, department directories) with zero proven value. Every new agent adds ~5 files and increases deliberation token cost. At 20 agents we are already near the practical limit for meaningful multi-agent deliberation.
- **Speculative engineering over empirical improvement (High):** Time spent designing new agents is time NOT spent actually using the existing ones. The opportunity cost is real -- the council needs battle-testing, not more members.
- **Hardware domain false confidence (High):** Adding more hardware agents for a user who self-identifies as unfamiliar with the domain increases the risk of plausible-sounding but unvalidated outputs. More agents does not equal more accuracy -- it can mean more unchecked outputs.

## Dependencies on Other Domains

- **Architect:** If distributed-systems skill is added, Architect must own it clearly and not defer to a hypothetical new agent. Architect should confirm this fits their cognitive framework.
- **Craftsman:** If e2e-testing skill is added, Craftsman needs to confirm the testing-strategy skill boundary -- what is unit/integration (current) vs. e2e/visual (new).
- **Advocate:** If a11y-audit skill is added, Advocate must confirm this is primary enough to warrant deep coverage, not just a checkbox.
- **Forge/Sentinel/Warden:** These three need to map their actual coverage boundaries before we can evaluate Gap 7. What semiconductor questions can each answer? Where are the real seams?

## Summary Table

| Gap | Recommendation | Severity | Rationale |
|-----|---------------|----------|-----------|
| i18n/Localization | No Action | Low | No evidence of need in user's domains |
| Distributed Systems | Skill (Architect) | Medium | Natural extension, not a new role |
| FinOps / Cost Engineering | No Action | Low | Already covered by Operator + Strategist |
| Accessibility depth | Skill (Advocate) | Medium | Deepen existing coverage, do not split |
| API Consumer / DevRel | No Action | Low | Three existing agents already cover this |
| QA / E2E Testing | Skill (Craftsman) | Medium | Testing belongs in Craftsman's department |
| EE fundamentals | Investigate | High | Define scope before acting; 3 HW agents exist |

| Consolidation | Verdict | Severity |
|---------------|---------|----------|
| Skeptic + Guardian | Do Not Merge | Critical |
| Herald + Strategist | Conditionally Acceptable | Medium |
