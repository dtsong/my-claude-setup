# Design Document: Council Roster Gap Resolution

## Overview

The council deliberated on 7 coverage gaps and 2 consolidation candidates across 3 rounds with 6 agents (Architect, Strategist, Skeptic, Scout, Chronicler, Forge). The result is a measured expansion: **1 new agent, 5 skill additions to existing agents, 0 consolidations**, with a conditional path for a second new agent (Distributed Systems).

The council adopted a **"skill-first, agent-second"** expansion policy: default to skill additions unless the gap requires a fundamentally different cognitive framework that no existing agent can absorb without identity distortion.

## Decisions

### 1. New Agent: Foundry (Copper Lens) — Constructive Chip & EE Design

**Unanimous (5/6 with 1 conditional).** Forge itself conceded that its adversarial cognitive framework (attack surfaces, side channels) cannot provide constructive design guidance. The user works in the semiconductor space and is unfamiliar with hardware domains — this agent must be self-sufficient.

- **Scope:** RTL authoring, verification methodology (UVM, coverage-driven), synthesis, SoC integration, DFT, EDA tool flows, analog/mixed-signal fundamentals, board-level integration, power delivery
- **Boundary with Forge:** "Design teams build, security teams audit." Foundry owns constructive design flows. Forge retains hardware security analysis, microarchitectural attacks, side-channel assessment. A bridging skill (`hw-security-signoff`) on Forge defines the handoff interface.
- **Founding skills (3-5):** `chip-design-flow`, `verification-methodology`, `soc-integration`, `analog-mixed-signal`, `board-integration`
- **Color:** Copper
- **Trigger domains:** `RTL`, `Verilog`, `SystemVerilog`, `UVM`, `synthesis`, `tape-out`, `SoC`, `ASIC`, `FPGA`, `verification`, `DFT`, `EDA`, `analog`, `mixed-signal`, `PCB`, `power integrity`, `signal integrity`

### 2. Skill Additions (5 packages)

All **unanimous (6/6).**

| Skill | Parent Agent | Rationale |
|-------|-------------|-----------|
| `i18n-review` | Advocate | Localization is a UX concern — RTL layouts, locale handling, translation workflows. Advocate's journey-mapping framework naturally extends to multi-language user flows. |
| `a11y-audit` | Advocate | Accessibility deepens Advocate's existing UX lens. WCAG compliance, screen reader patterns, keyboard navigation, reduced motion. |
| `finops-analysis` | Operator | Expands existing `cost-analysis` skill with FinOps-specific methodology: cloud cost attribution, reserved capacity, right-sizing, unit economics. |
| `distributed-patterns` | Architect | Consensus protocols, partition tolerance, saga orchestration, CRDTs, event sourcing. Resolves the Architect/Skeptic tension — Architect wanted a new agent, Skeptic said skill. The council sided 5:1 with skill-first, with a trigger to revisit if the skill proves insufficient after 5+ sessions. |
| `e2e-testing` | Craftsman | End-to-end test design, visual regression, cross-browser testing, Playwright/Cypress patterns. Shifted from Strategist's "new agent" proposal after Skeptic's zero-usage argument convinced the majority. |

### 3. API/DevRel — No Action (Distributed Across Existing Agents)

**Unanimous (6/6).** Architect conceded in Round 2 that this gap distributes cleanly:
- SDK ergonomics → Craftsman (developer experience)
- API documentation → Chronicler (documentation-plan skill)
- API versioning/deprecation → Architect (api-design skill)
- Developer portal UX → Advocate (interaction-design skill)

### 4. No Consolidations

**5/6 consensus.** Both proposed merges rejected:

| Candidate | Reason to Keep Separate |
|-----------|------------------------|
| **Skeptic + Guardian** | Technical risk (STRIDE, attack trees) and regulatory risk (GDPR, SOX) require different analytical toolkits and remediation playbooks. Merging creates a 12-mental-model, 6-skill bloated agent. Skeptic's "non-negotiable no" was backed by 5 of 6 agents. |
| **Herald + Strategist** | Operate at different lifecycle stages: Strategist asks "what to build?" (scope, MVP, prioritization), Herald asks "how does it spread?" (onboarding, retention, monetization). Different core questions, different value. |

**Mitigation for overlap:** Add a shared `risk-register` reference file (not a skill) to coordinate Skeptic/Guardian during deliberations and reduce duplicated arguments.

### 5. Conditional: Distributed Systems Agent (Deferred)

Architect held firm across all 3 rounds that distributed systems requires a fundamentally different cognitive frame from system architecture ("where should boundaries be?" vs. "what happens when boundaries fail?"). The council disagreed 5:1, recommending a skill on Architect first.

**Trigger to revisit:** If the `distributed-patterns` skill proves insufficient in 5+ sessions involving microservices, event-driven architecture, or consensus protocols, escalate to a full agent discussion.

## Tension Resolutions

| Tension | Agents | Resolution | Reasoning |
|---------|--------|------------|-----------|
| Expand roster vs. validate first | Architect vs. Skeptic | Compromise: 1 agent + 5 skills | Skeptic's zero-usage argument earned skill-first default; Forge's self-disqualification from constructive design justified 1 agent exception |
| Hardware: new agent vs. Forge expansion | Strategist vs. Forge | New agent (Foundry) | Forge conceded its adversarial cognitive frame distorts constructive guidance — different mental model required |
| Hardware scope: digital vs. analog vs. both | Strategist vs. Forge vs. Scout | Broad single agent | Forge argued digital/analog boundary is artificial in real SoC design; one chip, one agent |
| Distributed Systems: agent vs. skill | Architect vs. Skeptic | Skill first, agent conditional | 5:1 majority; Architect's boundary argument has merit but lacks empirical evidence |
| QA/E2E: agent vs. skill | Strategist vs. Skeptic | Skill on Craftsman | Zero-usage argument: no evidence Craftsman's testing-strategy is insufficient yet |
| Skeptic+Guardian merge | Architect vs. Skeptic | Keep separate | 5:1; distinct analytical toolkits, different failure domains |

## Decision Log

| Decision | Options Considered | Chosen | Reasoning |
|----------|-------------------|--------|-----------|
| Expansion policy | Add agents freely / Skill-first / Freeze roster | Skill-first, agent-second | Zero usage means unvalidated boundaries; default to cheaper, reversible changes |
| Hardware coverage | Expand Forge / New digital agent / New analog agent / Broad new agent | Broad new agent (Foundry) | Forge's adversarial frame can't guide; digital/analog split is artificial |
| Distributed systems | New agent / Skill on Architect / No action | Skill on Architect | 5:1 consensus; revisit after 5+ relevant sessions |
| i18n coverage | New agent / Skill on Advocate / No action | Skill on Advocate | UX concern, not distinct cognitive framework |
| Consolidation approach | Merge pairs / Keep all / Shared references | Keep all + shared reference file | Merging loses distinct analytical modes |

## Quality Strategy

Per Chronicler's non-negotiables:
- Every new skill must ship with a scoped SKILL.md following the existing template
- Department skill count stays within 2-4 per agent (prevent skill sprawl)
- New agent files must follow the 9-section template exactly
- Roster README and council.md roster table updated before any new agent ships
- Token budgets from Skill Governance Spec enforced (agent persona ≤2,000 tokens, skills ≤2,000 tokens)

Per Skeptic's validation gate:
- Foundry must demonstrate value in 3 real sessions before considered permanent
- `distributed-patterns` skill must be revisited after 5+ relevant sessions

## Implementation Priority

| Phase | Items | Effort | Dependency |
|-------|-------|--------|------------|
| **Phase 1: Quick wins** | 5 skill additions (i18n, a11y, finops, distributed-patterns, e2e-testing) | ~3-4 days | None |
| **Phase 2: New agent** | Foundry agent (persona + department + 3-5 skills + Forge bridging skill) | ~4-5 days | Phase 1 complete |
| **Phase 3: Validate** | Run 5-10 real council sessions, collect usage data, evaluate boundaries | Ongoing | Phase 2 complete |
| **Conditional** | Distributed Systems agent (if skill proves insufficient) | ~3 days | Phase 3 evidence |
