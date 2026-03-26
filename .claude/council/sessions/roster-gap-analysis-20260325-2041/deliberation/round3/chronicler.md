# Chronicler Final Position -- Roster Gap Analysis

## Revised Recommendation

Add 1 new agent for constructive chip/EE design (the domain Forge itself conceded it cannot serve without identity distortion). Defer QA/E2E to a skill addition on Craftsman. Address 5 remaining gaps as skill additions. No consolidations. Document the roster's scaling constraints before any additions ship.

---

## What Shifted and Why

The challenge round produced three outcomes that changed my calculus:

1. **Forge conceded the cognitive-posture problem.** Forge acknowledged that its adversarial frame ("what can go wrong with this silicon?") distorts constructive design guidance ("how do I build this chip correctly?"). This was the strongest possible validation that Gap 7 needs a new agent -- not because the domain knowledge differs, but because the *reasoning posture* differs. The "new agent builds, Forge audits" boundary mirrors real industry practice and is clean enough to document.

2. **Architect dropped the API/DevRel agent and the Skeptic+Guardian merge.** Both concessions reduce roster churn. The API/DevRel gap is adequately covered by enriching Architect (api-design), Chronicler (changelog-design, integration docs), and Craftsman (SDK ergonomics). The no-merge consensus eliminates the most disruptive documentation reorganization I was worried about.

3. **QA/E2E Testing lacks consensus for a new agent.** Architect said No Action. Skeptic said Skill Addition to Craftsman. Strategist said New Agent. Forge said Skill on Prover. With no agreement and Skeptic's zero-usage argument still standing, the conservative knowledge-architecture move is a skill addition to Craftsman, not a new agent. If Craftsman's `testing-strategy` skill proves insufficient after real usage, we revisit with evidence.

---

## Concessions Made

**I concede on Inspector (QA/E2E agent).** In Round 1, I argued this was the strongest case for a new agent because visual regression, cross-browser testing, and test environment management require a different cognitive framework than unit test design. I still believe that is true in the abstract. But Skeptic's zero-usage argument is dispositive for this specific gap: we have never tested whether Craftsman's `testing-strategy` skill is inadequate. Adding a skill is cheaper, reversible, and evidence-generating. If 10 real sessions reveal that Craftsman consistently drops E2E concerns, the Inspector agent case writes itself -- with data.

**I concede on the name "Foundry."** In Round 1, I flagged the naming collision risk with Forge. The challenge round confirmed this concern. Two industrial-metallurgical names in the same domain cluster creates exactly the kind of discoverability problem I exist to prevent. The new EE/chip agent needs a name that signals *construction* without echoing Forge's *metallurgy*. I defer to the council on naming, but offer alternatives below.

---

## Non-Negotiables

### 1. No consolidations ship without a migration document

If any future deliberation revisits Skeptic+Guardian or Herald+Strategist merging, the following must be produced BEFORE the merge executes:

- Redirect map: every reference to the old agent name (in README, roster table, registry.json, DEPARTMENT.md, scoring keywords in council.md) with the new location
- Skill migration plan: which skills move, which merge, which are deprecated
- Session artifact compatibility: how old deliberation files referencing the deprecated agent name remain readable

This deliberation reached near-unanimous consensus against merging. That consensus must be recorded as an ADR so future deliberations do not re-litigate without new evidence.

### 2. The roster README must be updated before any new agent ships

The README at `/Users/danielsong/Development/my-claude-setup/skills/council/README.md` is the single source of truth for the roster. It contains the agent table, the department skill matrix, and the "Adding a New Agent" instructions. Any new agent that ships without updating this file creates immediate documentation drift -- the most dangerous kind, because the README is the first thing a new user reads.

Specific updates required:
- Agent roster table (new row with number, name, color, description, selection trigger)
- Skills by Department table (new row with department, skills, output types)
- Project Structure section (new entry in the agents/ and skills/council/ file trees)
- registry.json (new department entry with skill tracking)

### 3. Department skill count must stay within 2-4 per agent

The current norm is 2-3 skills per department. This deliberation proposes adding skills to Advocate (i18n + a11y = 4 total), Architect (distributed-systems = 4 total), Operator (FinOps expansion = 3 total), and Craftsman (e2e-testing = 3 total). All of these are within bounds.

The threshold I will enforce: if any single department exceeds 4 skills, it must either split into a new agent or consolidate skills. The 6-skill department argument that killed the consolidation proposals applies equally to skill sprawl on existing agents. This constraint should be documented in the "Adding a Skill" section of the README.

### 4. New agent file must follow the 9-section template exactly

The current agent files have a consistent structure: Frontmatter, Intro, Cognitive Framework, Trained Skills, Communication Style, Decision Heuristics (5 items), Known Blind Spots, Trigger Domains, Department Skills, Deliberation Formats (Position/Challenge/Converge templates). The new EE/chip agent must follow this structure without deviation. Inconsistent agent files break the pattern-matching that lets someone who has read one agent file navigate all of them.

---

## Implementation Notes

### New Agent: Constructive Chip/EE Design

**Scope:** The constructive complement to Forge's adversarial security lens. Owns RTL authoring methodology, verification (UVM, coverage-driven, formal for functional correctness), synthesis and place-and-route flow, SoC integration (AMBA/AXI, IP qualification, register maps), DFT/scan/BIST, and EDA tool guidance. Per the Forge-Strategist exchange, analog/mixed-signal and RF are deferred.

**Boundary protocol with Forge:** The new agent builds; Forge audits. The new agent exposes security-relevant properties (access control matrices, shared microarchitectural state) for Forge to review. This handoff must be documented in both agents' "Dependencies on other domains" or "Known Blind Spots" sections, not buried in a skill file.

**Naming candidates (ranked by discoverability):**
1. **Silicon** -- Direct, unambiguous, no collision with existing names. Pairs with Forge without echoing it.
2. **Fabricator** -- Signals construction. Slightly verbose for frontmatter descriptions.
3. **Lithograph** -- Evocative of semiconductor manufacturing. May be too obscure for non-hardware users.

**Color:** Must not collide with Graphite (Forge), Titanium (Sentinel), Slate (Warden), or Pearl (Prover) -- the existing hardware-cluster colors. Candidates: **Cobalt**, **Tungsten**, or **Chrome**.

**Files to create:**
- `agents/council-silicon.md` (or chosen name) -- ~110 lines, 9 sections
- `skills/council/silicon/DEPARTMENT.md`
- `skills/council/silicon/chip-design-flow/SKILL.md`
- `skills/council/silicon/verification-methodology/SKILL.md`
- `skills/council/silicon/soc-integration/SKILL.md`

**Files to update:**
- `skills/council/registry.json` -- new department entry
- `skills/council/README.md` -- roster table, skills table, project structure
- `commands/council.md` -- scoring keywords, roster reference (if agent list is hardcoded)
- `agents/council-forge.md` -- add boundary protocol note in Known Blind Spots or Dependencies

### Skill Additions (priority order)

| Priority | Skill | Department | Files | Notes |
|----------|-------|------------|-------|-------|
| P1 | `finops-analysis` | Operator | Expand existing `cost-analysis` SKILL.md | Lowest effort, highest consensus |
| P2 | `a11y-audit` | Advocate | New SKILL.md + WCAG reference file | Reference file in `skills/council/references/` shared with Artisan |
| P3 | `i18n-review` | Advocate | New SKILL.md | Advocate grows to 4 skills (at ceiling) |
| P4 | `distributed-systems` | Architect | New SKILL.md | Architect grows to 4 skills (at ceiling) |
| P5 | `e2e-testing` | Craftsman | New SKILL.md | Craftsman grows to 3 skills; revisit for agent promotion after 10 sessions |

### ADR to Write

**Title:** ADR-001: Roster Expansion Policy -- Skill-First, Agent-Second

**Decision:** Coverage gaps are addressed as skill additions to existing agents unless the gap requires a distinct cognitive framework (different reasoning posture, not just different domain knowledge). New agents require: (a) evidence that no existing agent's cognitive framework can absorb the domain, (b) a boundary protocol with adjacent agents, and (c) full documentation updates before shipping.

**Consequences:** The roster grows slowly. Some gaps will be served by "good enough" skill coverage rather than dedicated agents. This is acceptable because the scoring system ensures only relevant agents are selected -- an adequate skill on a relevant agent outperforms a perfect agent that is never summoned.

---

## Final Summary Table

| Gap | Round 1 | Round 3 | Change Reason |
|-----|---------|---------|---------------|
| i18n | Skill to Advocate | **Skill to Advocate** | Unchanged; unanimous |
| Distributed Systems | Skill to Architect | **Skill to Architect** | Unchanged; Skeptic's zero-usage argument holds |
| FinOps | Skill to Operator | **Skill to Operator** | Unchanged; unanimous |
| a11y depth | Skill to Advocate | **Skill to Advocate** | Unchanged; unanimous |
| API Consumer/DevRel | Skill to Architect | **Skill to Architect + Chronicler + Craftsman** | Architect conceded agent; distributed across 3 existing departments |
| QA/E2E Testing | New Agent (Inspector) | **Skill to Craftsman** | Conceded; zero-usage means no evidence Craftsman is insufficient |
| EE/Chip Design | New Agent (Foundry) | **New Agent (Silicon)** | Strengthened; Forge conceded cognitive-posture problem. Renamed for discoverability |
| Skeptic+Guardian | Do Not Merge | **Do Not Merge** | Unchanged; near-unanimous. Record as ADR |
| Herald+Strategist | Do Not Merge | **Do Not Merge** | Unchanged; no pressure to consolidate |
