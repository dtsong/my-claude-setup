---
name: "Scout Department"
executive: "Scout"
color: "Cyan"
description: "Research, precedent, external knowledge"
---

# Scout Department — Cyan Lens

The Scout's department of focused skills for researching prior art, evaluating external solutions, and grounding decisions in evidence from the broader ecosystem.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [library-evaluation](library-evaluation/SKILL.md) | Structured library scoring and comparison | default | `library`, `package`, `dependency`, `npm`, `install` |
| [competitive-analysis](competitive-analysis/SKILL.md) | Feature comparison matrix across competing products | default | `competitive`, `alternative`, `comparison`, `prior art` |
| [technology-radar](technology-radar/SKILL.md) | Technology maturity assessment and adoption guidance | default | `framework`, `technology`, `tool`, `evaluate`, `choose` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Adding a new package, choosing between npm libraries, dependency decisions | library-evaluation | High |
| Comparing competing products, analyzing prior art in the market | competitive-analysis | High |
| Evaluating a framework, tool, or platform for adoption or migration | technology-radar | High |
| Mentions "bundle size", "maintenance health", "license compatibility" | library-evaluation | High |
| Asks about market landscape, feature gaps, or differentiation | competitive-analysis | Medium |
| Asks generally about "should we use X" without specifying library vs platform | technology-radar | Medium |

## Load Directive

Load one specialist skill at a time using the Skill tool. Read the classification logic table to select the appropriate specialist, then invoke the skill. Do not pre-load multiple specialists simultaneously.

## Handoff Protocol

When the specialist skill output reveals issues in another department's domain:
1. Complete the current skill's output format.
2. Note the cross-domain findings in the output.
3. Recommend loading the appropriate department and skill (e.g., "Hand off security findings from library evaluation to skeptic/threat-model for threat analysis").
