# resume-tailor

A Claude Code skill that produces job-specific tailored versions of Alan Yu's resume and matching cover letter drafts. Built on Alan's verified base experience — never fabricates, always grounded.

## Install

1. Install Node.js 18+ and the `docx` package:
   ```bash
   npm install -g docx
   ```

2. Place this directory inside your Claude Code skills folder:
   ```bash
   # macOS / Linux
   mv resume-tailor ~/.claude/skills/
   ```

3. Verify the skill loads. In Claude Code:
   ```
   /skills
   ```
   You should see `resume-tailor` listed.

## First-time test

Build the unmodified base resume to confirm the pipeline works:

```bash
cd ~/.claude/skills/resume-tailor
node scripts/build.js base/alan-resume.json output/Alan_Yu_Resume.docx
```

Open the `.docx` and confirm it looks correct.

## Usage

In a Claude Code session, paste the JD and say something like:

> "Here's a JD I want to apply to. Tailor my resume and draft a cover letter."

The skill will trigger automatically. It produces:
- `output/tailored-resume.json` — structured content
- `output/Alan_Yu_Resume_[Company].docx` — built resume
- `output/Cover_Letter_[Company].md` — cover letter draft
- A summary of what was changed and any gaps surfaced

## Editing the base

When new info arrives (a confirmed metric, a new accomplishment, a title change):

1. Edit `base/alan-resume.json` — this is what the build script consumes
2. Update `base/alan-resume.md` to match (for readability)
3. Update `base/alan-voice.md` to clear any related verification flag

The skill always reads from `base/`. Generated files live in `output/`.

## Files

- `SKILL.md` — workflow Claude follows when triggered
- `base/alan-resume.json` — canonical experience data (the source of truth)
- `base/alan-resume.md` — human-readable mirror
- `base/alan-voice.md` — framing rules, banned phrasings, verification status
- `scripts/build.js` — JSON → .docx renderer
- `examples/` — worked examples for reference
- `output/` — generated files (gitignored)

## Design notes

- **Two-page maximum.** If content overflows, the skill compresses lower-priority bullets, never the Hermès section.
- **Inline emphasis** in JSON strings: wrap in `**double asterisks**` to render in bold dark navy.
- **Title preservation.** The "Retail Systems Analyst (Americas Lead)" descriptor on Hermès is the canonical title (see `base/alan-resume.json`); do not invent others.
- **Truth-first.** Tailoring rephrases and reorders; it does not invent.
