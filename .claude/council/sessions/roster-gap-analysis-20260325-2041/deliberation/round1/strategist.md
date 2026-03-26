# Strategist Position -- Roster Gap Analysis

## Core Recommendation

Fill 2 gaps with new agents (EE Fundamentals, QA/E2E Testing), address 3 as skill additions to existing agents (i18n, FinOps, a11y), defer 2 entirely (Distributed Systems, API/DevRel). Do NOT consolidate Skeptic+Guardian. Consolidate Herald into Strategist only if token pressure demands it later -- not now.

## Per-Gap Analysis

### 1. i18n / Localization -- SKILL ADDITION to Advocate

**Value:** Moderate. Relevant to fullstack web work but not to CLI, AI/ML, or semiconductor projects. Maybe 25-30% of the user's work touches it.
**Effort (new agent):** High. Full persona + department + 3 skills for a narrow domain.
**Effort (skill addition):** Low. One skill under Advocate (who already owns UX and product thinking). i18n is fundamentally a user experience concern -- RTL, cultural adaptation, string extraction are UX decisions with engineering consequences.
**Verdict:** Skill addition to Advocate. One skill covering i18n strategy, locale architecture, and RTL checklist. ~1 day of work vs ~3 days for a full agent.

### 2. Distributed Systems -- NO ACTION

**Value:** Low for this user. The project types listed (fullstack web, CLI/dev-infra, AI/ML, semiconductor) do not center on consensus protocols or partition tolerance. When distributed concerns arise, Architect already covers system design, data models, and integration patterns. Operator covers deployment topology.
**Effort:** High for a new agent; moderate for a skill.
**Verdict:** No action now. If a specific project demands Raft/Paxos/CRDT expertise, add a skill to Architect at that point. Building ahead of need is waste.

### 3. FinOps / Cost Engineering -- SKILL ADDITION to Operator

**Value:** Moderate-high. Operator already has a `cost-analysis` skill. The gap is that it focuses on infrastructure cost, not broader FinOps (cloud spend governance, unit economics of compute, reserved instance strategy, cost attribution). This is a deepening, not a new domain.
**Effort:** Very low. Extend or add a second skill to Operator's existing department. The persona already thinks in operational terms.
**Verdict:** Skill addition to Operator. Rename/expand `cost-analysis` into a FinOps skill covering cloud cost governance, tagging strategy, and budget alerting. Half a day of work.

### 4. Accessibility (a11y) depth -- SKILL ADDITION to Advocate

**Value:** Moderate. Important for web projects, irrelevant to CLI/semiconductor. Advocate already lists accessibility in its description. The gap is depth -- WCAG audit checklists, screen reader testing strategy, ARIA pattern selection.
**Effort:** Low. One skill under Advocate with a reference file for WCAG criteria.
**Verdict:** Skill addition to Advocate. One `a11y-audit` skill with a conditionally-loaded WCAG checklist reference. ~1 day of work.

### 5. API Consumer / DevRel -- NO ACTION

**Value:** Low. SDK design and developer portals are relevant when building public APIs, which is not a primary activity for this user. API versioning is already within Architect's domain (API contracts, integration patterns). Developer portal/documentation concerns are covered by Chronicler.
**Effort:** High for a new agent.
**Verdict:** No action. The existing roster covers the constituent parts. If the user starts shipping public SDKs, revisit. Do not build for hypothetical futures.

### 6. QA / E2E Testing -- NEW AGENT

**Value:** High. Every project type benefits from structured test design. The user has `frontend-qa` and `tdd` skills already, but no agent owns testing strategy holistically -- visual regression, cross-browser, integration test architecture, test data management, flaky test diagnosis. Prover handles formal verification and correctness proofs, which is a different concern.
**Effort:** High (full agent), but justified by cross-cutting relevance.
**Verdict:** New agent. Call it "Assayer" or similar. Owns: test strategy, E2E architecture, visual regression, cross-browser matrix, test data, coverage analysis. Relevant across web, CLI, and AI/ML (model evaluation has testing parallels). Priority: second after EE Fundamentals because the user at least has partial coverage via existing skills.

### 7. EE Fundamentals + Chip-Level Flows -- NEW AGENT

**Value:** High AND unique. The user explicitly works in semiconductor and is explicitly unfamiliar with the domain. Forge covers microarchitecture/RTL/physical design. Sentinel covers IoT/embedded. Neither covers the EE fundamentals layer: circuit analysis, signal integrity, power delivery networks, analog/mixed-signal, SPICE simulation, PCB-level concerns, chip packaging, test (ATE/DFT). This is the connective tissue between Forge's silicon and Sentinel's embedded systems.
**Effort:** High (full agent + department), but irreplaceable. No existing agent can absorb this without distorting their identity.
**Verdict:** New agent. Call it "Volt" or "Ohm" -- something that signals electrical engineering. Must be self-sufficient (the user said they are unfamiliar). Needs skills for: circuit analysis, signal integrity, DFT/ATE flows, power analysis. Priority: FIRST, because the user has zero coverage here and cannot compensate with personal knowledge.

## Consolidation Candidates

### Skeptic + Guardian -- DO NOT CONSOLIDATE

These look similar from a distance (both "risk") but serve fundamentally different functions:
- Skeptic is a *reasoning mode* -- adversarial stress-testing of any proposal. Domain-agnostic.
- Guardian is a *compliance domain* -- privacy, legal, regulatory, governance. Domain-specific.

Merging them would either weaken the adversarial challenge function (Skeptic becomes compliance-focused) or dilute compliance depth (Guardian becomes a generic risk agent). The value of Skeptic is precisely that it challenges everyone, including Guardian. Keep separate.

### Herald + Strategist -- DO NOT CONSOLIDATE (yet)

Herald (growth, monetization, retention) and Strategist (scope, MVP, prioritization) both operate in "business" territory, but at different altitudes:
- Strategist optimizes *what to build* and *when*.
- Herald optimizes *how it spreads* and *how it earns*.

There is genuine overlap in stakeholder alignment and business framing. If token budget pressure forces a reduction, Herald is the one to absorb into Strategist (add a `growth-strategy` skill to my department). But the current 20-agent roster is not at a ceiling, so this consolidation saves effort without adding value. Defer.

## Priority Ordering

| Priority | Gap | Action | Effort | Rationale |
|----------|-----|--------|--------|-----------|
| P1 | EE Fundamentals | New agent | ~3 days | Zero coverage, user cannot self-serve, semiconductor is active domain |
| P2 | QA / E2E Testing | New agent | ~3 days | Cross-cutting value, partial coverage exists but no owner |
| P3 | FinOps | Skill to Operator | ~0.5 days | Quick win, extends existing skill |
| P4 | a11y depth | Skill to Advocate | ~1 day | Deepens existing coverage for web projects |
| P5 | i18n | Skill to Advocate | ~1 day | Moderate value, clean fit with Advocate |
| P6-P7 | Distributed Systems, API/DevRel | No action | 0 | Insufficient value for current project mix |

**Total investment for P1-P5:** ~8.5 days of effort for meaningful coverage improvement.
**Total if we built all 7 as agents:** ~21 days. The skill-addition approach saves 60% of the effort while capturing 80%+ of the value. Classic Pareto.

## Risks If Ignored

- **Semiconductor blind spot persists.** The user is working in hardware without an agent that covers the EE layer between RTL (Forge) and embedded (Sentinel). Decisions about signal integrity, power delivery, and testability will lack expert challenge. This is the highest-risk gap because the user explicitly cannot compensate.
- **Testing remains orphaned.** Without a dedicated testing strategist, test architecture decisions get made ad hoc by whatever agent is in the room. This leads to inconsistent coverage, flaky suites, and gaps that only surface in production.
- **Premature agent proliferation.** If we build all 7 as full agents, we hit 27 agents. The scoring system handles selection, but the maintenance burden (persona + department + skills + evals per agent) grows linearly. Skill additions to existing agents are cheaper to maintain.

## Dependencies on Other Domains

- **Architect:** Need validation that Distributed Systems is adequately covered by existing Architect skills, or if a skill gap exists within Architect's department.
- **Forge + Sentinel:** Need input on where exactly EE Fundamentals sits relative to their domains. What do they explicitly NOT cover that the new agent must own?
- **Advocate:** Need confirmation that i18n and a11y skills fit Advocate's identity without distorting the persona. Two new skills is significant scope for one department.
- **Prover:** Need clarity on Prover's testing-adjacent responsibilities. Does Prover own any E2E or integration testing, or is it purely formal verification? This defines the boundary with the proposed QA agent.
