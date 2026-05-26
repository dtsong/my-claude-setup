---
name: resume-tailor
description: "Use whenever Alan Yu is applying to a specific job and needs his resume or cover letter tailored to that opportunity. Triggers on: pasting a job description, asking 'how should I tailor this for [role]', requesting a cover letter for a specific company, asking for fit analysis between Alan's background and a posted role, or producing a .docx resume targeted at a specific employer. Do NOT use for unrelated resume work or for other people's resumes."
---

# resume-tailor

A skill for producing job-specific tailored versions of Alan Yu's resume and a matching cover letter draft. Always grounded in his actual experience — never fabricates accomplishments or extrapolates beyond what's in `base/alan-resume.md`.

## When to use

The user pastes a JD (job description) and wants a tailored application package. Common phrasings:
- "Here's a JD, tailor my resume."
- "How well does Alan fit this role?"
- "Draft a cover letter for this [company] role."
- "Build me a .docx version tailored to this posting."

If the user just wants the base resume unchanged, skip the tailoring workflow — point them to `base/alan-resume.md` and `scripts/build.js` directly.

## Workflow

Follow these steps in order. Each builds on the prior.

### 1. Load context
Read in this order:
1. `base/alan-resume.md` — canonical source of truth for Alan's experience
2. `base/alan-voice.md` — framing rules, banned phrasings, verification status of metrics
3. The user-provided JD

If `alan-voice.md` flags an open verification question that touches the JD (e.g., MTTR metric, AI bullet specifics), surface that to the user before producing output.

### 2. Analyze fit

Produce a brief fit analysis (4-6 bullets max). Categorize each JD requirement as:
- **Direct hit** — Alan has clear, quantified experience matching this
- **Adjacent** — Alan has related experience that can be reframed honestly to fit
- **Gap** — Alan does not have this experience; flag for the user; do NOT paper over

Never invent matches. If the JD requires Kubernetes and Alan has never touched it, say so.

### 3. Calibrate framing

Based on the JD's industry signals, decide whether default retail framing fits or whether to propose adjustments per `alan-voice.md` § "Industry calibration":
- Retail / E-commerce / D2C → default (no changes needed)
- Healthcare / Biotech → propose subtitle and bullet adjustments
- Defense / Gov → propose subtitle and bullet adjustments; flag clearance gap if required
- Hospitality / Multi-Site → propose subtitle adjustment to surface multi-site scope
- TPM / Program Manager → propose PM-flavored subtitle and verb framing

Default: retail (Alan's authoritative positioning). For non-retail JDs, present the proposed calibration to the user before generating output — do not silently substitute. Only emphasize luxury retail when the JD is explicitly luxury.

### 4. Produce tailored content

Generate a JSON file at `output/tailored-resume.json` matching the schema in `base/alan-resume.json` (the structured form of the resume). Tailoring is allowed in these specific ways:

**Allowed:**
- Rewriting the summary paragraph to lead with traits the JD emphasizes
- Reordering bullets within a role to surface relevant work first
- Lightly rephrasing bullets to weave in JD keywords WHERE THE UNDERLYING WORK MATCHES
- Adjusting the subtitle line ("Retail Systems Manager · ..." → tuned to JD)
- Including/excluding optional bullets when length needs adjustment

**Not allowed:**
- Adding metrics, technologies, accomplishments, or scope not present in base
- Changing employer names, dates, or core titles (the "(Americas Lead)" descriptor on Hermès stays exactly as in base; nothing else changes)
- Inventing JD-keyword matches by twisting Alan's actual work into shapes it didn't take

### 5. Build the .docx

Run:
```bash
node scripts/build.js output/tailored-resume.json output/Alan_Yu_Resume_[CompanyName].docx
```

The build script consumes the JSON and emits a styled .docx matching Alan's established design (navy/blue color scheme, Arial, two-page layout).

**Verify the 2-page constraint.** Render to PDF and check the page count using the `docx-to-pdf` skill:
```bash
node ~/.claude/skills/docx-to-pdf/scripts/docx2pdf.js output/Alan_Yu_Resume_[CompanyName].docx /tmp
```
If `pages` > 2, compress lower-priority bullets (never the Hermès section) and rebuild. Do not ship a 3-page resume.

### 6. Draft cover letter

Follow `templates/cover-letter.md`. It encodes the structure, the verified-safe proof points, and the pre-return checklist. Read `base/alan-voice.md` § "Cover letter voice" first.

Write a 180–220 word letter to `output/Cover_Letter_[CompanyName].md`:
- Opening (2-3 sentences): why this role + why Alan; name one concrete fact about the company
- Middle (one proof point per paragraph): 2-3 verified accomplishments mapped to JD priorities
- Close (1-2 sentences): specific interest + call to action; end with the San Diego line

Voice: confident, not boastful. First person. Active verbs. Alan's measured palette (do not silently upgrade to owned/drove). No "I am writing to apply for" filler. Em-dash cap 0–1 across resume AND letter combined.

### 7. Output summary

Produce a short "what I tailored and why" note (5-8 bullets) so the user can review changes before sending. Flag any gaps surfaced in step 2 explicitly.

### 8. Log the run

Append one row to `output/applications.md` (create it from the header in that file if missing). Use:
- **Date** — today (YYYY-MM-DD)
- **Company** / **Role** — from the JD
- **Status** — `Drafted` (Alan updates as it progresses)
- **Follow-up** — Date + 7 days, or `—` if not applying yet
- **Files** — the generated `.docx` and cover letter filenames

One row per invocation. Never rewrite existing rows; only append.

## Weekly portal scan

For sourcing roles across Alan's San Diego target list (`output/target-companies.md`):

1. Regenerate the checklist: `node scripts/job-search-links.js` → writes `output/weekly-search.md` (per-company LinkedIn / Indeed / careers search links, scoped to San Diego). No scraping; Alan opens the links.
2. For each promising posting, run the quick triage in `templates/fit-triage.md` (0–10 score, go/no-go).
3. For Strong hits (and chosen Maybes), run the full workflow above via `/tailor <jd-path>` or by pasting the JD.
4. Respect the ⚠️ clearance flags carried into the checklist — auto-skip roles requiring an active clearance (Alan has none).

This is a sourcing aid, not an applicant. It generates search links and scores fit; a human reviews and applies.

## Hard constraints

These apply to every invocation, regardless of user request:

1. **Truth before polish.** If tailoring requires invention, stop and surface the gap.
2. **Never modify base files.** `base/alan-resume.md`, `base/alan-resume.json`, and `base/alan-voice.md` are read-only sources of truth. Updates to them happen through a separate workflow with Alan's confirmation.
3. **Preserve dates and employers exactly.** No exception.
4. **Two-page maximum** for the .docx output. If content overflows, compress lower-priority bullets, not the Hermès section.
5. **Output to `output/` directory.** Never write to `base/` or `scripts/`.
6. **Em-dash hard cap: 0–1 em-dashes across the entire resume and cover letter.** See `alan-voice.md` § "Em-dash restriction." Use commas, semicolons, or sentence restructuring instead. This is non-negotiable — em-dashes are a recognizable AI-generation signal and Alan has asked they be limited.
7. **Preserve Alan's voice.** Do not silently upgrade his verbs (e.g., "managed" to "owned"). If a stronger framing would meaningfully help for a senior role, propose it in the change summary and let Alan decide.

## File structure

```
resume-tailor/
├── SKILL.md                    # this file
├── README.md                   # install + first-time setup
├── base/
│   ├── alan-resume.md          # human-readable canonical content
│   ├── alan-resume.json        # structured form (consumed by build.js)
│   └── alan-voice.md           # framing rules + verification status
├── scripts/
│   ├── build.js                # JSON → .docx
│   └── job-search-links.js     # target-companies.md → weekly search links
├── templates/
│   ├── cover-letter.md         # cover letter scaffold + checklist
│   └── fit-triage.md           # quick go/no-go scoring rubric
├── examples/
│   └── tailored-example.json   # one worked example for reference
└── output/                     # generated files land here (created on first run)
```

## Updating the base

When Alan provides new information (e.g., confirms the MTTR metric, adds a new accomplishment, gets a title change), update `base/alan-resume.json` AND `base/alan-resume.md`. Then update `base/alan-voice.md` to remove the corresponding verification flag. The build script reads from JSON; markdown is for humans.

## Dependencies

- Node.js 18+
- `docx` npm package: `npm install -g docx`
