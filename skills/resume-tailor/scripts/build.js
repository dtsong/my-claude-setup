#!/usr/bin/env node
/**
 * build.js — Render a resume JSON into a styled .docx file.
 *
 * Usage:
 *   node scripts/build.js <input.json> [output.docx]
 *
 * If output.docx is omitted, writes to ./output/Alan_Yu_Resume.docx
 *
 * The input JSON schema is documented in base/alan-resume.json.
 * The styling matches Alan's established design (navy/blue Arial, 2-page layout).
 *
 * Inline emphasis: wrap text in **double asterisks** to render in bold dark navy.
 */

const fs = require('fs');
const path = require('path');
const {
  Document, Packer, Paragraph, TextRun, AlignmentType, BorderStyle,
  LevelFormat, TabStopType,
} = require('docx');

// ---------- Style constants ----------
const NAVY = "1B2A4A";
const BLUE = "2563A8";
const GRAY = "5A6475";
const LIGHT_GRAY = "CCCCCC";
const FONT = "Arial";

// ---------- Inline emphasis parser ----------
// Splits "text with **emphasized** parts" into TextRun array.
function parseInline(text) {
  if (!text) return [];
  const parts = text.split(/(\*\*[^*]+\*\*)/g).filter(Boolean);
  return parts.map(part => {
    if (part.startsWith('**') && part.endsWith('**')) {
      return new TextRun({
        text: part.slice(2, -2),
        font: FONT, size: 20, color: NAVY, bold: true,
      });
    }
    return new TextRun({
      text: part, font: FONT, size: 20, color: GRAY,
    });
  });
}

// ---------- Paragraph factories ----------
function sectionHeading(text) {
  return new Paragraph({
    spacing: { before: 160, after: 30, line: 240 },
    border: {
      bottom: { style: BorderStyle.SINGLE, size: 8, color: BLUE, space: 4 },
    },
    children: [new TextRun({
      text, font: FONT, size: 21, bold: true, color: NAVY,
    })],
  });
}

function bullet(text) {
  return new Paragraph({
    numbering: { reference: "bullets", level: 0 },
    spacing: { before: 20, after: 20, line: 264 },
    children: parseInline(text),
  });
}

function companyRow(company, location, dates) {
  return new Paragraph({
    spacing: { before: 160, after: 20, line: 240 },
    tabStops: [{ type: TabStopType.RIGHT, position: 9360 }],
    children: [
      new TextRun({ text: company, font: FONT, size: 22, bold: true, color: NAVY }),
      new TextRun({ text: `  ·  ${location}`, font: FONT, size: 20, color: GRAY }),
      new TextRun({ text: `\t${dates}`, font: FONT, size: 20, italics: true, color: GRAY }),
    ],
  });
}

function roleTitle(text) {
  return new Paragraph({
    spacing: { before: 20, after: 80, line: 240 },
    children: [new TextRun({ text, font: FONT, size: 22, bold: true, color: NAVY })],
  });
}

function roleIntro(text) {
  return new Paragraph({
    spacing: { before: 20, after: 60, line: 264 },
    children: parseInline(text),
  });
}

// ---------- Document builder ----------
function buildDoc(data) {
  const children = [];

  // Header
  children.push(new Paragraph({
    spacing: { before: 0, after: 30, line: 240 },
    alignment: AlignmentType.CENTER,
    children: [new TextRun({
      text: data.name, font: FONT, size: 60, bold: true, color: NAVY,
    })],
  }));
  children.push(new Paragraph({
    spacing: { before: 0, after: 50, line: 240 },
    alignment: AlignmentType.CENTER,
    children: [new TextRun({
      text: data.subtitle, font: FONT, size: 22, italics: true, color: BLUE,
    })],
  }));
  children.push(new Paragraph({
    spacing: { before: 0, after: 160, line: 240 },
    alignment: AlignmentType.CENTER,
    border: {
      bottom: { style: BorderStyle.SINGLE, size: 4, color: LIGHT_GRAY, space: 8 },
    },
    children: [new TextRun({
      text: data.contact, font: FONT, size: 19, color: GRAY,
    })],
  }));

  // Summary
  children.push(sectionHeading("PROFESSIONAL SUMMARY"));
  children.push(new Paragraph({
    spacing: { before: 60, after: 60, line: 276 },
    children: parseInline(data.summary),
  }));

  // Expertise
  children.push(sectionHeading("AREAS OF EXPERTISE"));
  for (const line of data.expertise) {
    children.push(new Paragraph({
      spacing: { before: 0, after: 40, line: 276 },
      alignment: AlignmentType.CENTER,
      children: parseInline(line),
    }));
  }

  // Experience
  children.push(sectionHeading("PROFESSIONAL EXPERIENCE"));
  for (const job of data.experience) {
    children.push(companyRow(job.company, job.location, job.dates));
    children.push(roleTitle(job.title));
    if (job.intro) children.push(roleIntro(job.intro));
    for (const b of (job.bullets || [])) {
      children.push(bullet(b));
    }
  }

  // Skills
  children.push(sectionHeading("TECHNICAL SKILLS"));
  for (const skill of data.skills) {
    children.push(new Paragraph({
      spacing: { before: 0, after: 40, line: 276 },
      children: [
        new TextRun({ text: `${skill.category}:  `, font: FONT, size: 20, bold: true, color: NAVY }),
        new TextRun({ text: skill.items, font: FONT, size: 20, color: GRAY }),
      ],
    }));
  }

  return new Document({
    creator: "resume-tailor",
    title: `${data.name} — Resume`,
    numbering: {
      config: [{
        reference: "bullets",
        levels: [{
          level: 0, format: LevelFormat.BULLET, text: "•",
          alignment: AlignmentType.LEFT,
          style: { paragraph: { indent: { left: 360, hanging: 200 } } },
        }],
      }],
    },
    sections: [{
      properties: {
        page: {
          size: { width: 12240, height: 15840 }, // US Letter
          margin: { top: 540, right: 1080, bottom: 540, left: 1080 },
        },
      },
      children,
    }],
  });
}

// ---------- CLI ----------
function main() {
  const inputPath = process.argv[2];
  const outputPath = process.argv[3] || path.join('output', 'Alan_Yu_Resume.docx');

  if (!inputPath) {
    console.error('Usage: node scripts/build.js <input.json> [output.docx]');
    process.exit(1);
  }

  const data = JSON.parse(fs.readFileSync(inputPath, 'utf8'));
  const doc = buildDoc(data);

  // Ensure output directory exists
  const outDir = path.dirname(outputPath);
  if (outDir && !fs.existsSync(outDir)) {
    fs.mkdirSync(outDir, { recursive: true });
  }

  Packer.toBuffer(doc).then(buffer => {
    fs.writeFileSync(outputPath, buffer);
    console.log(`Wrote ${outputPath}`);
  });
}

main();
