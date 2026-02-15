---
name: "technology-radar"
department: "scout"
description: "Use when evaluating frameworks, tools, or platforms for adoption, migration, or stack decisions. Covers maturity assessment, ecosystem health, team readiness, migration cost, and long-term viability with radar quadrant placement. Do not use for comparing individual libraries (use library-evaluation) or analyzing competing products (use competitive-analysis)."
version: 1
triggers:
  - "framework"
  - "technology"
  - "tool"
  - "evaluate"
  - "choose"
  - "migrate"
  - "adopt"
  - "stack"
---

# Technology Radar

## Purpose

Assess technology maturity and fitness for the project, placing it on a radar quadrant with a clear adoption recommendation and risk profile.

## Scope Constraints

- Evaluates technologies, frameworks, tools, and platforms — not individual utility libraries.
- Focuses on maturity, ecosystem health, and project fit — not feature-by-feature product comparisons.
- Does not produce migration implementation plans; flag migration complexity for handoff.

## Inputs

- Technology, framework, or tool to evaluate
- Current tech stack and existing choices
- Project requirements and constraints
- Team size, skills, and familiarity
- Timeline and urgency

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Step 1: Categorize the Technology

Classify into one or more categories:
- **Language** (TypeScript, Rust, Go, Python)
- **Framework** (Next.js, SvelteKit, Remix, Astro)
- **Library** (React, Vue, Solid, htmx)
- **Tool** (Vite, Turbopack, Biome, ESLint)
- **Platform** (Vercel, Cloudflare, AWS, Supabase)
- **Infrastructure** (Docker, Kubernetes, Terraform, Pulumi)

### Step 2: Assess Maturity Level

Place the technology in one quadrant:
- **Adopt** — Proven in production at scale, low risk, strong ecosystem. We recommend using this.
- **Trial** — Promising technology worth exploring in non-critical paths. We've seen enough to recommend trying it.
- **Assess** — Interesting technology worth watching and experimenting with. Not ready for production use.
- **Hold** — Use with caution or actively migrate away. Known issues, declining ecosystem, or better alternatives exist.

Evidence for placement:
- Production usage at notable companies
- Stability of API (frequency of breaking changes)
- Age and version history
- Community sentiment trend (growing, stable, declining)

### Step 3: Evaluate Ecosystem Health

- **Documentation quality:** Official docs completeness, tutorials, examples
- **Community size:** GitHub stars, npm downloads, Discord/forum activity, conference talks
- **Corporate backing:** Funded by a company? Independent maintainers? Foundation-backed?
- **Plugin/integration ecosystem:** Middleware, extensions, adapters for common tools
- **Hiring market:** Can you find developers who know this? Learning resources available?

### Step 4: Check Team Familiarity and Learning Curve

- How many team members have experience with this technology?
- What is the learning curve (days, weeks, months to productivity)?
- Are there similar technologies the team already knows that transfer?
- What training or ramp-up would be needed?

### Step 5: Estimate Migration Cost from Current Stack

- What does the current solution look like?
- How many files, modules, or systems would need to change?
- Can migration be incremental or must it be all-at-once?
- What is the estimated effort (days/weeks/months)?
- What risks exist during migration (dual-system complexity, feature parity gaps)?

### Step 6: Assess Long-term Viability

- **Funding model:** VC-funded, open source donations, corporate sponsor, commercial license
- **Roadmap clarity:** Published roadmap? Active development toward clear goals?
- **Adoption trend:** Growing, plateau, declining? (npm downloads over 2 years)
- **Lock-in risk:** How hard is it to switch away if needed?
- **Standards alignment:** Does it follow web standards, or create proprietary abstractions?

### Step 7: Evaluate Alignment with Project Requirements

- Does it solve the specific problem at hand?
- Performance characteristics match requirements?
- Deployment model compatibility (serverless, edge, traditional server)?
- Scaling characteristics for expected load?
- Security posture and vulnerability response history?

### Progress Checklist

- [ ] Step 1: Technology categorized
- [ ] Step 2: Maturity level assessed
- [ ] Step 3: Ecosystem health evaluated
- [ ] Step 4: Team familiarity checked
- [ ] Step 5: Migration cost estimated
- [ ] Step 6: Long-term viability assessed
- [ ] Step 7: Project alignment evaluated

> **Compaction resilience:** If context was compacted, re-read this SKILL.md and check the Progress Checklist for completed steps before continuing.

## Handoff

- If migration complexity is significant, recommend loading operator/deployment-plan for migration planning.
- If security posture concerns emerge, recommend loading skeptic/threat-model for threat analysis.

## Output Format

### Technology Radar Placement

```
              ADOPT
                |
         +-----------+
         |  [Name]   |    (or placed in TRIAL / ASSESS / HOLD)
         +-----------+
                |
  HOLD ------- + ------- TRIAL
                |
              ASSESS
```

**Quadrant:** [Adopt / Trial / Assess / Hold]
**Confidence:** [High / Medium / Low]
**Category:** [Language / Framework / Library / Tool / Platform / Infrastructure]

### Adoption Recommendation

**Recommendation:** [Adopt now / Trial in next sprint / Assess and revisit in N months / Hold and consider alternatives]
**Timeline:** [Immediate / Next quarter / Next half / Not recommended]
**Migration path:** [Description of incremental adoption strategy if applicable]

### Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| ... | High/Med/Low | High/Med/Low | ... |

### Comparison with Current Solution

| Aspect | Current | Proposed | Delta |
|--------|---------|----------|-------|
| Performance | ... | ... | ... |
| DX | ... | ... | ... |
| Ecosystem | ... | ... | ... |
| Maintenance | ... | ... | ... |

## Quality Checks

- [ ] Technology categorized accurately
- [ ] Maturity level justified with evidence (not opinion)
- [ ] Ecosystem health assessed across all dimensions
- [ ] Team familiarity and learning curve honestly evaluated
- [ ] Migration cost estimated with scope
- [ ] Long-term viability assessed (funding, adoption trend, lock-in)
- [ ] Project-specific requirements checked for alignment
- [ ] Risk assessment includes mitigation strategies

## Evolution Notes
<!-- Observations appended after each use -->
