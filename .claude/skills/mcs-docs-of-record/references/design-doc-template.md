# Council synthesis design doc template

Source: `.claude/council/sessions/<session-slug>/design.md`, produced at Phase 4 (Planning) of the `/council` engine. This is a per-session synthesis artifact, not a maintained living doc; once the session closes, treat it as a frozen record of design intent at that date, not a doc to keep updating. Exemplar used here: `claude-config-model-optimization-20260702-0003/design.md`.

## Section order (from the exemplar, verified structure)

1. **`# Design Document: <Title>`**
2. **`## Overview`**: dense paragraph(s), no bullets. States the converged plan as delivered fact ("The council converged on a two-track plan..."), names every workstream by its issue-tracking ID (F1, F2, F3a...) inline so the doc is greppable against the PRD/issue map. Ends with the core philosophy in one sentence.
3. **`## Architecture`**: opens with a "Perspectives: <Agent> (<their lens>), <Agent> (<their lens>)..." line attributing which council agents drove this section. Then `###` subsections per major design decision, each titled with the decision and, in parens, which agent's position won or was "adopted by all" / "non-negotiable" if it was a hard constraint.
4. **`## User Experience`**: same Perspectives-line pattern. Covers MVP/roadmap scoping, user-facing surface changes, adoption friction.
5. **`## Risk Assessment`**: Perspectives line, then:
   - `### Critical and High findings`: numbered list, each item bolded with a severity tag (`(Critical if unconstrained)`, `(High)`, `(Medium)`), followed by the concrete mitigation required before ship, not after.
   - `### Rollback posture`: one paragraph, the literal rollback command or mechanism per risky change.
6. **`## Quality Strategy`**: Perspectives line, then subsections for the eval/test approach (e.g. `### Eval-before-activation`), an instrument-trustworthiness subsection when telemetry or measurement is load-bearing to the design, and `### Validation and verification` as a checklist of concrete pass/fail gates.
7. **`## Tension Resolutions`**: table, columns `Tension | Agents | Resolution | Reasoning`. One row per place the council disagreed and converged; the `Agents` column names both sides. This is the section that makes disagreement legible instead of silently averaged away, keep it even when it makes the design look contested.
8. **`## Decision Log`**: table, columns `Decision | Options Considered | Chosen | Reasoning`. Exhaustive: every option seriously considered gets a row, including ones ultimately rejected, with the reasoning that rejected them. A decision log missing rejected alternatives is a decision log that will get re-litigated next session.

## Rules

- Every workstream ID (F1, F2...) introduced in Overview must resolve to at least one Decision Log row and, once implemented, an issue number. Cross-check against `.claude/council/sessions/<slug>/issues.md` if present.
- Perspectives lines are not decorative, they are the accountability trail for which agent's judgment a design leans on. Do not drop them when summarizing the doc elsewhere.
- Numeric claims inside a design doc (line counts, percentages, dollar costs) carry the same authority-tier discipline as any other doc: they are tier-4/5 narrative unless they cite the enforcement artifact directly. Re-verify before quoting a design doc's numbers in a higher-authority doc like ARCHITECTURE.md.
- A design doc frequently gets an HTML render alongside it (e.g. `design.html`) for a browser-based design-approval touchpoint. The `.md` is the source; the `.html` is a presentation derivative, regenerate it, do not hand-edit it.
- If asked to write a NEW design doc outside the `/council` flow, keep the same 7-section skeleton; it forces risk assessment and a decision log even for a solo design, which is the actual value of the template.
