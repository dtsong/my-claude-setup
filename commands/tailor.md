---
description: Tailor Alan Yu's resume + cover letter to a job description and log the run
argument-hint: <path-to-jd.md>
---

Run the `resume-tailor` skill end to end for the JD at: **$ARGUMENTS**

Steps (per `~/.claude/skills/resume-tailor/SKILL.md`):

1. Invoke the `resume-tailor` skill.
2. Read the JD file at `$ARGUMENTS`. If no path was given, ask for one and stop.
3. Load `base/alan-resume.json` and `base/alan-voice.md`. Surface any open verification flag that touches this JD.
4. Produce the fit analysis (Direct hit / Adjacent / Gap). Do not paper over gaps.
5. Calibrate framing. If the JD is non-retail, propose the subtitle/bullet changes from `alan-voice.md` § Industry calibration and WAIT for approval before generating output.
6. Write `output/tailored-resume.json`, then build `output/Alan_Yu_Resume_[Company].docx` via `scripts/build.js`.
7. Draft `output/Cover_Letter_[Company].md` using `templates/cover-letter.md`.
8. Run the constraint checks: 2-page resume, em-dash cap 0–1 across resume + letter, cover letter 180–220 words, no silently-upgraded verbs.
9. Append a row to `output/applications.md`.
10. Return the "what I tailored and why" summary plus any flagged gaps.

Hard constraints from SKILL.md apply: never modify `base/` files, preserve dates/employers, truth before polish.
