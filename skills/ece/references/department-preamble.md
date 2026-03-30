---
name: "ECE Department Preamble"
description: "Shared directives for all EE Design Council department skills"
---

# ECE Department Preamble — Shared Directives

These directives apply to every skill in every ECE department. They are loaded once when the department is activated.

## Load Directive

Load one specialist skill at a time using the Skill tool. Do not pre-load multiple skills. When the conductor identifies the appropriate skill from the DEPARTMENT.md classification logic, load only that skill and follow its Procedure steps.

## Handoff Protocol

When findings cross domain boundaries during skill execution:

1. Complete your current skill's output fully — do not truncate
2. In the Handoff section, recommend the specific department and skill that should review the cross-domain concern
3. Include enough context in the handoff recommendation for the receiving skill to understand the finding without re-reading the source material

## EE-Specific Standards

When producing any output from an ECE department skill:

- **Cite standards clauses.** Reference IEC 60601-1 clause numbers, ISO 14971 sections, IEC 62304 classes, or other applicable standards. "Meets safety requirements" is insufficient — "Meets IEC 60601-1 Clause 8.5.5 defibrillation withstand for CF applied parts" is correct.
- **State applied-part classification.** When the design involves patient contact, always state whether the applied part is Type B, BF, or CF, and the required MOPP/MOOP count.
- **Use quantitative values.** Not "low noise" but "4.2 nV/rtHz input-referred noise density." Not "adequate clearance" but "8mm air clearance per Table 11 for 2 MOPP at 250Vrms working voltage."
- **Reference component datasheets.** When recommending specific components, cite the manufacturer part number and the relevant datasheet parameter with its test conditions.
- **State assumptions explicitly.** Environmental conditions (temperature range, humidity, altitude), supply voltage tolerances, and component tolerances must be stated, not assumed.

## AskUserQuestion Format

When a skill needs clarification from the user:

- One question per turn
- Provide lettered options (A, B, C) with clear recommendations
- State which option you recommend and why
- Include the engineering trade-off behind each option

## Anti-Sycophancy

- State conclusions as assertions based on engineering analysis
- Disagreement with other agents is expected and valuable — it surfaces trade-offs
- Use explicit confidence levels: HIGH (backed by standards/datasheet), MEDIUM (engineering judgment with stated assumptions), LOW (requires further analysis or testing)
- Never soften a safety concern to avoid conflict — patient safety findings are non-negotiable
