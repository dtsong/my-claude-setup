# PRD: Council Roster Gap Resolution

## Overview
Expand the council roster to close identified coverage gaps through 1 new agent (Foundry), 5 skill additions to existing agents, and 1 bridging skill, following the council-approved "skill-first, agent-second" expansion policy.

## Goals
- Close the hardware/EE coverage gap with a constructive chip design agent (Foundry)
- Add i18n, accessibility, FinOps, distributed systems, and E2E testing capabilities to existing agents
- Maintain roster structural integrity (no consolidations, consistent templates, token budgets)

## Non-Goals
- Consolidating any existing agent pairs (explicitly rejected by council)
- Creating a Distributed Systems agent (deferred; skill-first approach)
- Creating QA/E2E or API/DevRel agents (covered by skill additions)
- Adding accounting or electrical engineering (analog-only) agents (tabled/future)

## Quality Gates
```bash
pre-commit run --all-files          # Token budgets, frontmatter, reference integrity
wc -w agents/council-foundry.md     # Agent persona ≤ ~1,500 words
wc -w skills/council/*/SKILL.md     # Each skill ≤ ~1,500 words
```

## User Stories

### US-001: Create Foundry Agent Persona
**As** a council user working on semiconductor projects, **I want** a Foundry agent with a constructive chip design cognitive framework **so that** I get guidance on verification, synthesis, SoC integration, and EDA flows without an adversarial security bias.

**Acceptance Criteria:**
- [ ] `agents/council-foundry.md` exists with all 9 required sections
- [ ] Cognitive framework emphasizes constructive design (not adversarial/security)
- [ ] Trigger domains include: RTL, Verilog, SystemVerilog, UVM, synthesis, tape-out, SoC, ASIC, FPGA, verification, DFT, EDA, analog, mixed-signal, PCB, power integrity, signal integrity
- [ ] Color is Copper, lens description clearly differentiates from Forge
- [ ] Token budget ≤ 2,000 tokens

### US-002: Create Foundry Department & Skills
**As** a council user, **I want** Foundry to have a department with 3-5 structured skills **so that** deliberations produce structured, methodology-driven hardware design guidance.

**Acceptance Criteria:**
- [ ] `skills/council/foundry/DEPARTMENT.md` exists with skill routing table
- [ ] `skills/council/foundry/chip-design-flow/SKILL.md` — RTL→synthesis→place-route→tape-out
- [ ] `skills/council/foundry/verification-methodology/SKILL.md` — UVM, coverage-driven, formal
- [ ] `skills/council/foundry/soc-integration/SKILL.md` — AMBA/AXI, IP qualification, DFT
- [ ] Each skill follows the standard SKILL.md template with frontmatter, procedure, output format, quality checks
- [ ] Each skill ≤ 2,000 tokens

### US-003: Register Foundry in Council Roster
**As** the council engine, **I want** Foundry registered in the roster table and registry **so that** it's automatically scored and selectable during assembly.

**Acceptance Criteria:**
- [ ] Row added to Agent Roster table in `commands/council.md` (agent #21)
- [ ] Entry added to `skills/council/registry.json` with all skills at 0 uses
- [ ] Mandatory bonus rule added: Foundry +2 for any chip design, verification, or EDA work
- [ ] Anti-redundancy penalty rule added: Forge vs Foundry (security review → penalize Foundry, constructive design → penalize Forge)
- [ ] Subagent type `Foundry` matches Agent tool definition

### US-004: Add Forge Bridging Skill
**As** a council session conductor, **I want** a `hw-security-signoff` skill on Forge **so that** the Forge↔Foundry handoff interface is explicit and structured.

**Acceptance Criteria:**
- [ ] `skills/council/forge/hw-security-signoff/SKILL.md` exists
- [ ] Defines the builder→auditor handoff contract
- [ ] Trigger domains include: `security signoff`, `hardware review`, `tape-out security`
- [ ] Registry entry added in `skills/council/registry.json`

### US-005: Add i18n-review Skill to Advocate
**As** a council user building multi-language products, **I want** Advocate to have an i18n-review skill **so that** localization concerns (RTL, locale handling, translation workflows, cultural adaptation) are surfaced during deliberations.

**Acceptance Criteria:**
- [ ] `skills/council/advocate/i18n-review/SKILL.md` exists
- [ ] Covers: locale strategy, RTL layout, string externalization, pluralization, date/number formatting, cultural UX adaptation
- [ ] Trigger domains added to Advocate's persona: `i18n`, `localization`, `translation`, `RTL`, `locale`, `multi-language`
- [ ] Registry entry added

### US-006: Add a11y-audit Skill to Advocate
**As** a council user building accessible products, **I want** Advocate to have an a11y-audit skill **so that** WCAG compliance, screen reader patterns, and keyboard navigation are methodically evaluated.

**Acceptance Criteria:**
- [ ] `skills/council/advocate/a11y-audit/SKILL.md` exists
- [ ] Covers: WCAG 2.2 AA compliance, screen reader compatibility, keyboard navigation, focus management, color contrast, reduced motion, ARIA patterns
- [ ] Trigger domains added to Advocate's persona: `accessibility`, `a11y`, `WCAG`, `screen reader`, `ARIA`
- [ ] Registry entry added

### US-007: Add finops-analysis Skill to Operator
**As** a council user managing cloud costs, **I want** Operator to have a finops-analysis skill **so that** cloud cost optimization, capacity planning, and unit economics are covered in deliberations.

**Acceptance Criteria:**
- [ ] `skills/council/operator/finops-analysis/SKILL.md` exists
- [ ] Covers: cloud cost attribution, reserved capacity planning, right-sizing, spot/preemptible usage, unit economics, cost anomaly detection
- [ ] Trigger domains added to Operator's persona: `FinOps`, `cloud cost`, `cost optimization`, `unit economics`, `reserved instances`
- [ ] Registry entry added

### US-008: Add distributed-patterns Skill to Architect
**As** a council user building distributed systems, **I want** Architect to have a distributed-patterns skill **so that** consensus protocols, partition tolerance, and saga orchestration are covered without needing a separate agent.

**Acceptance Criteria:**
- [ ] `skills/council/architect/distributed-patterns/SKILL.md` exists
- [ ] Covers: CAP theorem trade-offs, consensus protocols (Raft, Paxos), saga orchestration, CRDTs, event sourcing, partition handling, distributed transactions, failure detectors
- [ ] Trigger domains added to Architect's persona: `distributed`, `consensus`, `partition`, `saga`, `CRDT`, `event sourcing`, `microservices`
- [ ] Registry entry added
- [ ] Validation gate: revisit after 5+ sessions — if skill proves insufficient, escalate to full agent

### US-009: Add e2e-testing Skill to Craftsman
**As** a council user needing end-to-end test strategy, **I want** Craftsman to have an e2e-testing skill **so that** visual regression, cross-browser testing, and E2E test design are methodically planned.

**Acceptance Criteria:**
- [ ] `skills/council/craftsman/e2e-testing/SKILL.md` exists
- [ ] Covers: E2E test design patterns, visual regression testing, cross-browser strategy, Playwright/Cypress patterns, test data management, CI integration for E2E
- [ ] Trigger domains added to Craftsman's persona: `e2e`, `end-to-end`, `visual regression`, `cross-browser`, `Playwright`, `Cypress`
- [ ] Registry entry added

## Technical Notes
- All new files must pass `pre-commit run --all-files` (token budgets, frontmatter validation)
- Foundry agent file follows the 9-section template: title+color, cognitive framework, trained skills, communication style, decision heuristics, blind spots, trigger domains, department skills, deliberation formats
- Advocate's department will grow from 2 to 4 skills (within the 2-4 guideline)
- Operator's department will grow from 3 to 4 skills (within guideline)
- Architect's department will grow from 3 to 4 skills (within guideline)
- Craftsman's department will grow from 2 to 3 skills (within guideline)
- Forge's department will grow from 3 to 4 skills (within guideline)

## Dependencies
- US-003 depends on US-001 and US-002 (can't register without files)
- US-004 depends on US-001 (bridging skill references Foundry's scope)
- US-005 through US-009 are independent of each other and of US-001-004
