#!/usr/bin/env node
/**
 * docx2pdf.js — Convert a .docx to PDF via LibreOffice headless and report
 * the page count. Reusable across projects.
 *
 * Usage:
 *   node docx2pdf.js <input.docx> [outdir]
 *
 * Prints a JSON line: {"pdf":"<path>","pages":<n>}
 * Exit code 0 on success, non-zero on failure.
 */

const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');

function findSoffice() {
  const candidates = [
    'soffice',
    'libreoffice',
    '/Applications/LibreOffice.app/Contents/MacOS/soffice',
    '/opt/homebrew/bin/soffice',
    '/usr/bin/soffice',
    '/usr/local/bin/soffice',
  ];
  for (const c of candidates) {
    try {
      execFileSync(c, ['--version'], { stdio: 'ignore' });
      return c;
    } catch (_) { /* try next */ }
  }
  return null;
}

// Count page objects in a PDF. LibreOffice writes one "/Type /Page" object per
// page (the page tree node is "/Type /Pages", excluded by the negative lookahead).
function countPdfPages(pdfPath) {
  const buf = fs.readFileSync(pdfPath, 'latin1');
  const matches = buf.match(/\/Type\s*\/Page(?![s])/g);
  return matches ? matches.length : 0;
}

function main() {
  const input = process.argv[2];
  const outdir = process.argv[3] || path.dirname(input || '.');

  if (!input) {
    console.error('Usage: node docx2pdf.js <input.docx> [outdir]');
    process.exit(2);
  }
  if (!fs.existsSync(input)) {
    console.error(`Input not found: ${input}`);
    process.exit(2);
  }

  const soffice = findSoffice();
  if (!soffice) {
    console.error('LibreOffice not found. Install it: brew install --cask libreoffice');
    process.exit(3);
  }

  fs.mkdirSync(outdir, { recursive: true });
  try {
    execFileSync(soffice, [
      '--headless', '--convert-to', 'pdf', '--outdir', outdir, input,
    ], { stdio: 'ignore' });
  } catch (e) {
    console.error(`Conversion failed: ${e.message}`);
    process.exit(1);
  }

  const pdfPath = path.join(outdir, path.basename(input).replace(/\.docx$/i, '.pdf'));
  if (!fs.existsSync(pdfPath)) {
    console.error(`Expected PDF not produced: ${pdfPath}`);
    process.exit(1);
  }

  const pages = countPdfPages(pdfPath);
  console.log(JSON.stringify({ pdf: pdfPath, pages }));
}

main();
