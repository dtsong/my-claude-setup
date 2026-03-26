# Chronicler Position -- Roster Gap Analysis

**Core recommendation:** Add no more than 2 new agents (EE/chip-level and QA/E2E Testing), address the remaining 5 gaps through skill additions to existing departments, and do not consolidate any agents -- the documentation and structural costs of merging outweigh the savings.

**Key argument:**

The council currently has a clean 1:1 mapping: 20 agents, 20 departments, 20 `agents/council-*.md` files, 20 `skills/council/<name>/` directories, each with a `DEPARTMENT.md` and 2-3 skill subdirectories. This symmetry is the single most important property for maintainability. A new developer can look at any agent file, predict the corresponding department path, and find skills -- no lookup table needed. Every addition must preserve this property; every consolidation threatens it. The question for each gap is not "is the domain important?" but "does the domain require its own cognitive framework, deliberation format, and skill tree, or can it be absorbed into an existing agent's mental models?"

## Per-Gap Analysis

### 1. i18n/Localization -- Skill Addition to Advocate

**Recommendation: Skill Addition**

Localization is fundamentally a user-facing concern: cultural adaptation, RTL layout, string externalization. The Advocate already owns journey-mapping and interaction-design. Adding an `i18n-review` skill to the Advocate department is the right scope. A standalone agent would need its own cognitive framework, but localization reasoning ("will this string break in German? does this layout work RTL?") maps naturally onto the Advocate's "think from the user's perspective" mental model.

- **Documentation cost:** One new SKILL.md, one line in DEPARTMENT.md, one entry in registry.json.
- **Discoverability:** Users searching for i18n will find it under Advocate, which is intuitive.

### 2. Distributed Systems -- Skill Addition to Architect

**Recommendation: Skill Addition**

The Architect already covers system design, APIs, data models, and integration patterns. Distributed systems (consensus, partitioning, replication) are architectural concerns. Adding a `distributed-systems` skill to the Architect department extends its cognitive framework without needing a separate agent persona. The Architect's existing mental models (C4, domain-driven design) already accommodate distributed thinking.

- **Documentation cost:** One SKILL.md, minor DEPARTMENT.md update.
- **Risk:** The Architect department grows to 4 skills, but that is within acceptable bounds.

### 3. FinOps / Cost Engineering -- Skill Addition to Operator

**Recommendation: Skill Addition**

The Operator already has a `cost-analysis` skill. FinOps is a natural deepening of that skill rather than a separate concern. Rename or expand `cost-analysis` to `finops-analysis` with broader scope (cloud spend forecasting, reserved instance strategy, cost allocation tagging). No new agent needed.

- **Documentation cost:** Edit one existing SKILL.md (or replace it). Zero new directories.
- **Discoverability:** Already exactly where someone would look.

### 4. Accessibility (a11y) depth -- Skill Addition to Advocate

**Recommendation: Skill Addition**

The Advocate's description already includes accessibility. Adding an `a11y-audit` skill with WCAG checklist methodology, screen reader testing flows, and ARIA pattern guidance gives the Advocate structured depth without a new agent. This is the same pattern as gap 1: the Advocate department grows to 4 skills (journey-mapping, interaction-design, i18n-review, a11y-audit), which is still maintainable and mirrors how the Skeptic has 3 skills.

- **Documentation cost:** One SKILL.md. Advocate department becomes the largest at 4 skills, but thematically coherent.
- **Alternative considered:** A standalone a11y agent. Rejected because accessibility is inseparable from user experience -- you cannot reason about a11y without reasoning about the user journey.

### 5. API Consumer / DevRel -- Skill Addition to Architect

**Recommendation: Skill Addition**

SDK design, developer portals, and API versioning are extensions of the Architect's existing `api-design` skill. The audience shifts (external developers instead of internal consumers), but the cognitive framework (contract-first design, backward compatibility, versioning strategy) is the same. Expand `api-design` or add a sibling `sdk-design` skill.

- **Documentation cost:** One SKILL.md or expanded existing skill.
- **Risk:** The Architect department grows to 4-5 skills. If this feels overloaded, split `api-design` into internal vs. external API design.

### 6. QA / E2E Testing -- New Agent

**Recommendation: New Agent**

This is the strongest case for a new agent. The Craftsman covers testing strategy and code quality, but QA/E2E testing (visual regression, cross-browser matrix, test environment management, flaky test diagnosis) requires a fundamentally different cognitive framework. The Craftsman thinks about unit test design and code patterns; a QA agent thinks about test infrastructure, environment parity, and systematic coverage of user-visible behavior.

- **Proposed name:** Inspector (color: Pewter or Copper)
- **Department skills:** `visual-regression`, `cross-browser-matrix`, `test-environment-design`
- **Documentation cost:** One agent file (~110 lines), one DEPARTMENT.md, 2-3 SKILL.md files, registry.json entry, roster table update.
- **Discoverability:** The name "Inspector" signals testing/verification. Color should be visually distinct from existing palette.
- **Naming note:** "Inspector" avoids collision with existing agent names and clearly signals the domain without being generic.

### 7. EE Fundamentals + Chip-Level Flows -- New Agent

**Recommendation: New Agent**

The user works in semiconductors. Forge covers silicon security specifically (RTL security review, physical design security, microarch analysis), but general EE fundamentals -- signal integrity, power delivery, chip-level verification flows, design-for-test (DFT), timing closure methodology -- are a distinct domain from security-focused hardware review. Forge's cognitive framework is adversarial ("how can this silicon be attacked?"), while EE fundamentals are constructive ("how do we get this chip to work correctly?").

- **Proposed name:** Foundry (color: Copper or Steel)
- **Department skills:** `signal-integrity`, `dft-methodology`, `chip-verification-flow`
- **Documentation cost:** Same as Inspector above.
- **Discoverability:** The name pairs naturally with Forge (both industrial/metallurgical metaphors), making the hardware cluster easy to find.
- **Naming risk:** "Foundry" might be confused with Forge. Alternative: "Fabricator" or "Lithograph." The key is that the name signals construction/manufacturing rather than security.

## Consolidation Analysis

### Skeptic + Guardian: Do Not Consolidate

The Skeptic and Guardian have overlapping keywords (both deal with "risk" and "security") but fundamentally different cognitive frameworks:

- **Skeptic:** Adversarial reasoning. "What can go wrong? What are you not thinking about?" General-purpose devil's advocate applicable to any domain.
- **Guardian:** Compliance and governance. "Does this meet GDPR? Where is PII stored? Who has audit access?" Regulatory and policy-driven.

**Structural impact of consolidation:**
- Two department directories (6 skills total) must merge into one. The merged department would have 6 skills, far exceeding the current norm of 2-3 and breaking the skill tree's visual uniformity.
- The agent file would need to hold two distinct cognitive frameworks, making it harder to read and maintain.
- The roster table row would need an unwieldy description covering both adversarial reasoning and compliance review.
- Trigger keywords would overlap, causing the scoring system to over-select the merged agent.
- The Skeptic's challenge-round behavior (devil's advocate) is structurally different from the Guardian's (compliance checklist). Merging them would dilute both.

**Documentation cost of consolidation:** Rewrite both agent files into one, merge two DEPARTMENT.md files, update registry.json, update README roster table, update all documentation references. This is more work than maintaining them separately.

### Herald + Strategist: Do Not Consolidate

- **Strategist:** Scope, prioritization, MVP definition. "Should we build this at all? What is the minimum viable version?"
- **Herald:** Growth engineering, monetization, messaging. "How do we get users? How do we make money? What is the onboarding funnel?"

These are complementary but distinct. The Strategist operates pre-decision ("should we?"), the Herald operates post-decision ("how do we grow it?"). Merging them creates a bloated agent that is simultaneously about restraint (Strategist) and expansion (Herald) -- contradictory mental models in one persona.

**Structural impact:** Same problems as Skeptic+Guardian. 6 skills in one department, dual cognitive frameworks, unwieldy description.

## Risks If Ignored

- **Roster sprawl without naming conventions.** If the roster grows past 22-23 agents without a documented naming convention (thematic families, color uniqueness constraints), new contributors will struggle to predict which agent covers which domain. The naming system must remain discoverable.
- **Skill tree depth inconsistency.** If some departments have 2 skills and others have 5, the registry.json and DEPARTMENT.md files lose their structural predictability. The 2-3 skill norm should be documented as a guideline.
- **Agent file bloat.** At ~110 lines per agent file and 9 required sections, the 2,240 total lines across 21 files is manageable. Adding 2 agents brings it to ~2,460 lines. But if 5 agents were added, the directory listing alone becomes harder to scan. The 9-section format should be validated as still appropriate at 22-23 agents.

## Dependencies on Other Domains

- **Architect** must confirm that distributed-systems and SDK-design skills fit within Architect's cognitive framework without overloading it.
- **Craftsman** must confirm that QA/E2E testing is genuinely outside Craftsman's scope (i.e., that a new Inspector agent is justified rather than expanding Craftsman's skills).
- **Forge** must confirm that EE fundamentals are outside Forge's intended scope and warrant a separate agent.
- **Strategist** must weigh in on whether 22 agents (vs. 20) creates scoring noise -- does adding agents reduce selection precision?
- **Operator** must confirm that FinOps deepening of `cost-analysis` is sufficient vs. a standalone concern.
