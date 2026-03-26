# Scout Final Position -- Roster Gap Analysis

**Revised recommendation:** Add 1 new agent (EE/analog/RF/PCB, scoped per Strategist-Forge consensus), deliver 5 skill additions (i18n on Advocate, a11y on Advocate, FinOps on Operator, Distributed Systems on Architect, QA/E2E on Craftsman), take no action on API/DevRel. No consolidation of either pair.

## How I Got Here

My Round 1 position called for 3 new agents (i18n, FinOps, EE). The challenge round shifted the landscape significantly. I am updating based on the emerging consensus and re-evaluating my original precedent research against the actual arguments made.

## Concessions Made

### i18n: New Agent --> Skill on Advocate

I concede this. My Round 1 argument cited Google, Microsoft, and Apple having dedicated L10n teams -- but those are organizations with billions of users across hundreds of locales. The Skeptic's challenge question ("When was the last time the user needed i18n guidance?") is fair. The consulting firm precedent still holds (i18n is a distinct practice area), but the T-shaped model actually supports the skill approach here: Advocate's UX cognitive framework provides the horizontal bar, and an i18n skill provides targeted vertical depth when needed. The user's project mix (CLI, dev-infra, AI/ML, semiconductor) does not generate enough i18n demand to justify a standalone agent's maintenance cost.

What the skill must include to be adequate: ICU message syntax patterns, CLDR locale data usage, BiDi/RTL layout checklist, text expansion ratios for UI planning, locale fallback chain design, and cultural adaptation heuristics (date/number/currency formatting). Without these specifics, the skill will be too shallow to catch real i18n issues.

### FinOps: New Agent --> Skill on Operator

I concede this. My Round 1 argument cited the FinOps Foundation as a distinct discipline with its own lifecycle. That remains true at the organizational level, but the council is not an organization -- it is a review panel for a single developer. The Skeptic and Strategist both correctly noted that Operator already has a `cost-analysis` skill, and Strategist's framing of this as a "deepening, not a new domain" is accurate. The FinOps Foundation's Inform/Optimize/Operate lifecycle maps cleanly onto Operator's existing operational thinking.

What the expanded skill must include: unit economics modeling, reserved/spot instance strategy, cost tagging and attribution, right-sizing methodology, budget alerting thresholds, and provider-specific pricing heuristics (AWS, Vercel, Supabase). The current `cost-analysis` skill should be renamed to `finops-review` to signal the broader scope.

### EE Scope: Narrowed from "EE Fundamentals" to Analog/RF/PCB

I accept the Strategist-Forge boundary consensus. My Round 1 position framed EE broadly (everything below microarchitecture). The challenge round produced a cleaner cut: Forge expands to cover the constructive digital chip design flow (verification, DFT, SoC integration), while the new EE agent owns the domains that require fundamentally different physics -- analog/mixed-signal, RF, PCB, and power management IC design. This aligns with how IEEE organizes its societies: the Circuits and Systems Society (analog, mixed-signal) is distinct from the Computer Society (digital design). Forge itself conceded that analog/mixed-signal and RF are "fundamentally different disciplines (continuous-time vs. discrete-time, electromagnetic theory vs. digital logic)."

## Non-Negotiables

### 1. The new EE agent must exist as a standalone agent, not a skill on Forge

External evidence is unambiguous here. Analog circuit design and digital microarchitecture are as different as structural engineering and interior design -- they operate on the same physical artifact but use entirely different physics, tools, and mental models. Every semiconductor company (Intel, AMD, Qualcomm, TI, Analog Devices) maintains separate analog and digital engineering teams. IEEE maintains separate societies. EDA vendors sell separate tool suites (Cadence Virtuoso for analog vs. Cadence Genus/Innovus for digital). The user is unfamiliar with hardware and needs a self-sufficient agent here -- overloading Forge's digital-first cognitive framework with analog reasoning would produce confused outputs in both domains.

### 2. No consolidation of either Skeptic+Guardian or Herald+Strategist

The Round 2 consensus is near-unanimous on this, and the external evidence I presented in Round 1 holds without revision. Every consulting firm, every engineering org, and every standards body I surveyed maintains risk assessment and compliance governance as separate functions. The Skeptic's own argument was compelling: "A system can be technically robust but legally non-compliant. A system can be fully compliant but technically fragile." These are orthogonal failure modes requiring orthogonal mental models.

Herald+Strategist likewise survive. The "growth vs. value" tension is not just theoretical -- it is how product organizations actually discover blind spots. The scoring system handles session selection; keeping both preserves dialectic value at zero runtime cost when only one is relevant.

### 3. Distributed Systems belongs on Architect as a skill, not a new agent

Architect argues strongly for a new agent here. I maintain my Round 1 position. The external evidence is clear: ThoughtWorks, TOGAF, and every architecture practice I surveyed treat distributed systems patterns as part of the architecture discipline, not a separate one. Martin Fowler does not have a "distributed systems" practice separate from his architecture practice. The mental models (CAP theorem, consensus, partitioning) extend Architect's existing system-decomposition framework rather than replacing it.

The Skeptic's concern about "turf disputes" between Architect and a hypothetical Distributed Systems agent is well-founded. In Architecture Review Board literature, adding a second systems-level voice creates coordination overhead that typically degrades review quality. A skill gives Architect the vocabulary and checklists without the jurisdictional cost.

## Implementation Notes

### New Agent: EE/Analog Agent

- **Suggested name:** Research suggests names that signal the physical/analog domain. "Ohm" or "Volt" (per Strategist) work. I would also consider "Faraday" -- it signals electromagnetics and circuit theory without being too narrow.
- **Scope:** Analog/mixed-signal design (PLL, ADC, DAC, SerDes PHY), RF/antenna design, PCB layout and signal integrity, power management IC design (PMIC, LDO, DCDC), semiconductor physics fundamentals, SPICE simulation methodology.
- **Explicit boundary with Forge:** Forge owns digital design flow (RTL through tapeout), verification methodology, DFT, SoC integration. The new agent owns continuous-time/analog domains. The handoff point is the analog-digital interface (ADC/DAC boundaries, mixed-signal verification).
- **Cognitive framework:** Should center on continuous-time thinking -- impedance, frequency response, noise analysis, stability margins, power supply rejection. This is fundamentally different from Forge's discrete-time, clock-edge thinking.
- **Priority:** P1 per Strategist's ordering. The user has zero coverage and cannot self-compensate.

### Skill Additions (Priority Order)

| Priority | Skill | Host Agent | Key Contents | Effort |
|----------|-------|------------|-------------- |--------|
| P2 | `finops-review` | Operator | Unit economics, reserved/spot strategy, cost tagging, right-sizing, provider pricing | ~0.5 days |
| P3 | `a11y-audit` | Advocate | WCAG 2.2 AA checklist, ARIA patterns, screen reader flows, keyboard nav, focus management | ~1 day |
| P4 | `i18n-strategy` | Advocate | ICU/CLDR usage, BiDi/RTL checklist, text expansion, locale fallback, cultural formatting | ~1 day |
| P5 | `distributed-systems` | Architect | CAP trade-offs, consensus protocols, saga patterns, CQRS, circuit breakers, CRDTs | ~1 day |
| P6 | `e2e-testing` | Craftsman | Visual regression (Percy/Chromatic), cross-browser matrix, page object model, flaky test triage | ~0.5 days |

### Forge Department Expansion

Per the Strategist-Forge consensus, Forge should add 2-3 skills covering the constructive digital design flow:
- `chip-design-flow` -- RTL-to-tapeout flow, synthesis, P&R, signoff, EDA tool guidance
- `verification-methodology` -- UVM, coverage-driven verification, assertion-based verification
- `soc-integration` -- AMBA/AXI, IP qualification, register maps, DFT insertion

This expansion should happen in parallel with the new EE agent creation, as they define each other's boundaries.

### No Action Items

- **API Consumer/DevRel** -- Architect dropped this in Round 2. The constituent parts (API design on Architect, docs on Chronicler, DX on Craftsman) cover it adequately. Revisit only if the user starts shipping public API platforms.
- **Herald+Strategist consolidation** -- Keep separate. No action needed.
- **Skeptic+Guardian consolidation** -- Keep separate. No action needed.

## Final Summary

| Item | Round 1 | Round 3 | Shift Reason |
|------|---------|---------|-------------|
| i18n | New Agent | Skill on Advocate | User's project mix does not justify standalone; T-shaped model supports skill approach |
| Distributed Systems | Skill on Architect | Skill on Architect | No change; external evidence consistent |
| FinOps | New Agent | Skill on Operator | Single-developer context; Operator already has cost-analysis foundation |
| a11y | Skill on Advocate | Skill on Advocate | No change |
| API/DevRel | Skill on Craftsman | No Action | Covered by existing agent composition |
| QA/E2E | Skill on Craftsman | Skill on Craftsman | No change |
| EE Fundamentals | New Agent (broad) | New Agent (scoped to analog/RF/PCB) | Forge absorbs digital design flow; clean physics-based boundary |
| Skeptic+Guardian | Keep Separate | Keep Separate | No change; near-unanimous consensus |
| Herald+Strategist | Keep Separate | Keep Separate | No change; near-unanimous consensus |

Net result: 1 new agent + Forge expansion + 5 skill additions. Total roster moves from 20 to 21 agents.

---

Sources (from Round 1 research, still applicable):
- [Specialist vs Generalist AI Agents -- Expert Opinions](https://rossum.ai/blog/specialist-vs-generalist-ai-agents-expert-opinions/)
- [T-Shaped Engineers and Hardware Development -- Quilter](https://www.quilter.ai/blog/on-t-shaped-engineers-and-hardware-development-transparency-and-the-generalist-path)
- [Architecture Review Board Structure -- LeanIX](https://www.leanix.net/en/wiki/ea/architecture-review-board)
- [TOGAF Architecture Review Board](https://pubs.opengroup.org/architecture/togaf8-doc/arch/chap23.html)
- [McKinsey vs BCG Comparison -- Career in Consulting](https://careerinconsulting.com/mckinsey-vs-bcg/)
- [Specialists vs Generalists vs T-Shaped -- Hybrid Hacker](https://hybridhacker.email/p/specialists-vs-generalists-vs-t-shaped)
