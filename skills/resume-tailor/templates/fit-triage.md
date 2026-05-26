# fit-triage.md — quick go/no-go scoring

Fast triage to decide whether a posting is worth a full `/tailor` run. This is lighter than SKILL.md step 2 (the full fit analysis); use it to sort many postings quickly. Score against `base/alan-resume.json` only — never against invented experience.

## Score 5 dimensions, 0–2 each (max 10)

| Dimension | 0 | 1 | 2 |
|---|---|---|---|
| **Title level** | Wrong level (IC, or VP+) | Adjacent (Sr Analyst, Lead) | Manager / Sr Manager / Director / TPM |
| **Domain overlap** | Unrelated stack | Some enterprise-systems overlap | POS / ERP / OMS / omnichannel / integration core |
| **Location** | Not SD, no remote | Remote, not SD-based | San Diego or SD-remote |
| **Required must-haves** | Hard blocker (active clearance, degree gate, 10y people-mgmt) | One stretch requirement | Alan meets all stated must-haves |
| **Multi-site / scale signal** | None | Single-site | Multi-site / multi-region / at-scale |

## Decision
- **8–10:** Strong. Run `/tailor <jd-path>` now.
- **5–7:** Maybe. Tailor only if it's a priority company (see `target-companies.md`) or network is 🟢. Note the stretch in the fit analysis.
- **0–4:** Skip. Log nothing, or note "passed" in `applications.md` if Alan wants the record.

## Hard blockers (auto-skip regardless of score)
- Active security clearance required (Alan has none — see `alan-voice.md`).
- Requires a tech on the "should NOT claim" list as a non-negotiable (Kubernetes, ML engineering, cloud architecture cert, programming beyond SQL).
- Requires direct people-management depth Alan can't evidence from base.

## Output (one line per posting)
`<Company> — <Role> — score X/10 — <Strong|Maybe|Skip> — <one-line reason>`

If Strong or a chosen Maybe, hand off: read the JD and run the `resume-tailor` workflow (or `/tailor <path>`).
