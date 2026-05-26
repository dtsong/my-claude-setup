---
name: docx-to-pdf
description: "Use to convert a Word .docx file to PDF and/or verify its page count. Triggers on: converting docx to pdf, rendering a document, checking how many pages a docx produces, or asserting a page-count constraint (e.g. a resume must stay 2 pages). Wraps LibreOffice headless conversion."
---

# docx-to-pdf

Convert a `.docx` to PDF via LibreOffice headless and report the rendered page count. Reusable from any project (e.g. `resume-tailor` uses it to enforce a 2-page resume).

## When to use
- "Convert this docx to PDF."
- "How many pages does this resume render to?"
- A workflow needs to assert a page-count constraint after generating a `.docx`.

## Prerequisite
LibreOffice must be installed (provides `soffice`):
```bash
brew install --cask libreoffice   # macOS
```
The script auto-locates `soffice` on PATH or at the standard macOS app path.

## Usage
```bash
node ~/.claude/skills/docx-to-pdf/scripts/docx2pdf.js <input.docx> [outdir]
```
- `outdir` defaults to the input file's directory.
- Prints one JSON line: `{"pdf":"<path>","pages":<n>}`.
- Exit codes: `0` success, `1` conversion error, `2` bad args, `3` LibreOffice missing.

## Example
```bash
$ node scripts/docx2pdf.js output/Alan_Yu_Resume.docx /tmp
{"pdf":"/tmp/Alan_Yu_Resume.pdf","pages":2}
```

## Verifying a page-count constraint
Parse the `pages` field and compare. Example (fail if a resume exceeds 2 pages):
```bash
PAGES=$(node scripts/docx2pdf.js "$DOCX" /tmp | node -e "process.stdin.on('data',d=>console.log(JSON.parse(d).pages))")
[ "$PAGES" -le 2 ] || { echo "Resume is $PAGES pages (max 2)"; exit 1; }
```

## Notes
- Page count is derived from PDF page objects (`/Type /Page`), which matches LibreOffice output reliably.
- Conversion is read-only on the source `.docx`; it never modifies the input.
- For batch use, call once per file; LibreOffice headless handles one document per invocation cleanly.
