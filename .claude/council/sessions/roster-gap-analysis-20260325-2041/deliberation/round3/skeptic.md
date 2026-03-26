# Skeptic Final Position -- Roster Gap Analysis

## Revised Recommendation

Accept the three unanimous skill additions. Conditionally accept ONE new hardware agent (not two). Continue to oppose a Distributed Systems agent. No consolidation mergers. Gate all additions behind a usage validation checkpoint.

## Concessions Made

**Hardware agent -- Conditionally accepted.** I entered this deliberation saying "investigate before acting" on the EE fundamentals gap, and the investigation happened during deliberation. Forge's concession is the evidence I asked for: Forge itself acknowledges that constructive chip design (synthesis flows, PPA optimization, design-for-test, verification methodology) requires a fundamentally different cognitive frame from its security-focused RTL review lens. When the domain expert says "this is outside my scope," I take that seriously. Four of six agents supporting this, including the one closest to the domain, crosses my evidentiary threshold.

However, I accept this with conditions (see Non-negotiables below). My Round 1 concern remains valid: the user self-identifies as unfamiliar with hardware domains. More agents in a domain the user cannot validate means more surface area for plausible-sounding but incorrect guidance. This risk is manageable with the right safeguards, but it is real.

**Herald + Strategist -- Fully accepted as separate.** I initially called this merge "conditionally acceptable." Architect's lifecycle-stage argument and my own defense of analytical independence for Skeptic + Guardian made it intellectually dishonest to keep the Herald + Strategist merge on the table. Same principle, same conclusion: distinct analytical modes deserve distinct agents.

## Non-Negotiables

**1. No Distributed Systems agent.** Architect dropped the API/DevRel agent and the Skeptic + Guardian merge -- credit where due, those were the right calls. But the Distributed Systems agent remains unjustified. Architect's own trained skills cover system integration patterns, DDD bounded contexts, and mechanical sympathy. The gap is a skill gap in Architect's department, not an agent gap on the roster. Add a `distributed-patterns` skill to Architect with reference material on consensus protocols, saga orchestration, CRDTs, and partition tolerance. If -- after actual usage -- Architect's skill proves insufficient for real deliberations, revisit with evidence. I will not block a well-scoped skill addition, but I will block a new agent that overlaps with an existing agent's core domain.

**2. No consolidation mergers.** This appears to be consensus now. Preserving it as a non-negotiable ensures it does not resurface in implementation.

**3. Usage validation gate for the new hardware agent.** The new agent must not be created as a permanent roster addition on day one. Implementation should follow this sequence: (a) define the agent's scope document with 5-10 concrete semiconductor questions it must answer well, (b) build the agent persona and 2-3 initial skills, (c) run it through at least 3 real deliberation sessions where the user has actual hardware questions, (d) evaluate whether its outputs were useful and accurate, (e) only then grant permanent roster status. If the agent cannot demonstrate value in 3 sessions, it gets archived, not expanded.

**4. Skill additions must be scoped before implementation.** "Add i18n to Advocate" is a direction, not a spec. Each skill needs: a SKILL.md with clear triggers, a reference file with the relevant checklist or standard (e.g., WCAG 2.2 for a11y, ICU message format patterns for i18n), and at least 2 eval cases. No skill ships without eval cases -- otherwise we are adding untested code to an untested system.

## Implementation Notes

### Skill additions (unanimous -- implement first)

| Skill | Owner | Scope boundary | Key reference material |
|-------|-------|---------------|----------------------|
| `i18n-review` | Advocate | String externalization, locale-aware formatting, RTL layout, cultural adaptation. Does NOT cover translation management platforms or CI pipeline integration (those are Operator). | ICU MessageFormat, CLDR, Unicode BiDi algorithm basics |
| `a11y-audit` | Advocate | WCAG 2.2 conformance (A/AA), ARIA patterns, keyboard navigation, screen reader compatibility. Does NOT cover visual design decisions (those stay with Artisan's `visual-audit`). | WCAG 2.2 quick reference, WAI-ARIA Authoring Practices |
| `finops-review` | Operator | Cloud cost modeling, right-sizing, reserved vs. on-demand analysis, cost anomaly detection. Does NOT cover business ROI or revenue modeling (those are Strategist's `impact-estimation`). | FinOps Foundation principles, cloud provider pricing models |
| `distributed-patterns` | Architect | Consensus protocols (Raft, Paxos), saga orchestration, CRDTs, eventual consistency, partition tolerance patterns, distributed transactions. Does NOT own deployment topology (Operator) or performance under partition (Tuner). | CAP theorem, Designing Data-Intensive Applications patterns |

### New hardware agent (conditional -- implement second)

- **Scope:** Constructive semiconductor design -- synthesis flows, PPA (power/performance/area) optimization, design-for-test (DFT), functional verification methodology, timing closure from a design perspective (not security perspective).
- **Boundary with Forge:** Forge retains RTL security review, side-channel analysis, microarchitectural attack surfaces. The new agent owns design correctness and implementation quality. The dividing question: "Is this a security property?" goes to Forge. "Is this a design quality property?" goes to the new agent.
- **Boundary with Sentinel:** Sentinel retains IoT/embedded/edge systems. The new agent operates below Sentinel's abstraction level -- silicon, not firmware.
- **Boundary with Warden:** Warden retains hw-sw boundary and isolation. The new agent stays within the hardware domain; anything crossing into kernel/OS goes to Warden.
- **Validation requirement:** 3 real deliberation sessions with user hardware questions before permanent roster status. The user's self-identified unfamiliarity with hardware means outputs MUST include confidence levels and explicit "verify this with a domain expert" caveats on any guidance that could lead to silicon respin risk.

### Sequencing

1. Implement the 4 skill additions first. These are low-risk, low-effort, and immediately useful.
2. Run 5-10 real deliberations using the existing 20-agent roster with the new skills.
3. Review usage data from the registry. Which agents get invoked? Which skills get used? Which deliberations surface unanswered questions?
4. Only then implement the new hardware agent, informed by actual usage patterns.
5. After 3 hardware-focused sessions, evaluate and decide on permanent status.

This sequencing ensures we are building on evidence, not speculation. The council's most critical need right now is not more members -- it is its first real session.
