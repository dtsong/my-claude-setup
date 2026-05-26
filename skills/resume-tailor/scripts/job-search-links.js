#!/usr/bin/env node
/**
 * job-search-links.js — Generate a weekly per-company job-search checklist.
 *
 * Reads output/target-companies.md, parses each company row (name + search
 * terms + tier), and emits clickable LinkedIn / Indeed / careers-page search
 * URLs scoped to San Diego. No network calls, no scraping — just deep links
 * Alan opens by hand during the weekly scan.
 *
 * Usage:
 *   node scripts/job-search-links.js [input.md] [output.md]
 * Defaults:
 *   input  = output/target-companies.md
 *   output = output/weekly-search.md
 */

const fs = require('fs');
const path = require('path');

const LOCATION_LINKEDIN = 'San Diego, California, United States';
const LOCATION_INDEED = 'San Diego, CA';

// Clean a markdown company cell into a query-friendly name.
// "**Callaway Golf (Topgolf Callaway Brands)**" -> "Callaway Golf"
// "**CSAA Insurance / AAA**" -> "CSAA Insurance"
function queryName(display) {
  let n = display.replace(/\*\*/g, '').trim();
  n = n.replace(/\s*\(.*?\)\s*/g, ' ').trim(); // drop parentheticals
  n = n.split('/')[0].trim();                  // take before a slash
  return n;
}

function enc(s) { return encodeURIComponent(s); }

function links(name, terms) {
  const primary = terms[0] || 'IT Manager';
  const orKeywords = terms.slice(0, 3).join(' OR ');
  return {
    linkedin: `https://www.linkedin.com/jobs/search/?keywords=${enc(orKeywords)}&location=${enc(LOCATION_LINKEDIN)}`,
    indeed: `https://www.indeed.com/jobs?q=${enc(name + ' ' + primary)}&l=${enc(LOCATION_INDEED)}`,
    careers: `https://www.google.com/search?q=${enc(`"${name}" careers "${primary}" San Diego`)}`,
  };
}

function parse(md) {
  const lines = md.split('\n');
  const rows = [];
  let tier = 'Untiered';
  let prevTerms = null;

  for (const line of lines) {
    const tierMatch = line.match(/^##\s+(Tier\s+\d+[^\n]*)/);
    if (tierMatch) { tier = tierMatch[1].trim(); continue; }

    // A data row: starts with "| **Name**" and has 6 columns.
    if (!/^\|\s*\*\*/.test(line)) continue;
    const cells = line.split('|').slice(1, -1).map(c => c.trim());
    if (cells.length < 6) continue;

    const display = cells[0];
    const whyFit = cells[3];
    let termsCell = cells[4];

    // Resolve "Same as X" / "Same" references.
    let terms;
    const sameAs = termsCell.match(/^Same as (.+)$/i);
    if (/^Same$/i.test(termsCell)) {
      terms = prevTerms || [];
    } else if (sameAs) {
      const refName = sameAs[1].trim().toLowerCase();
      const ref = rows.find(r => r.queryName.toLowerCase().startsWith(refName)
        || queryName(r.display).toLowerCase().includes(refName));
      terms = ref ? ref.terms : [];
    } else {
      terms = termsCell.split(',').map(t => t.trim()).filter(Boolean);
    }
    prevTerms = terms;

    rows.push({
      tier,
      display: display.replace(/\*\*/g, '').trim(),
      queryName: queryName(display),
      terms,
      clearance: /⚠️/.test(whyFit),
    });
  }
  return rows;
}

function render(rows) {
  const today = new Date().toISOString().slice(0, 10);
  const out = [];
  out.push(`# Alan Yu — Weekly Job Search Checklist`);
  out.push('');
  out.push(`Generated ${today} from \`target-companies.md\`. Open each company's links, scan for fresh postings matching the search terms, then run the fit triage (\`templates/fit-triage.md\`). Promising postings: paste the JD and run \`/tailor\`.`);
  out.push('');
  out.push(`Re-generate anytime: \`node scripts/job-search-links.js\``);
  out.push('');

  let lastTier = null;
  for (const r of rows) {
    if (r.tier !== lastTier) {
      out.push('');
      out.push(`## ${r.tier}`);
      out.push('');
      lastTier = r.tier;
    }
    const l = links(r.queryName, r.terms);
    const flag = r.clearance ? ' ⚠️ *check clearance requirement*' : '';
    out.push(`- [ ] **${r.display}**${flag}`);
    out.push(`  - [LinkedIn](${l.linkedin}) · [Indeed](${l.indeed}) · [Careers (Google)](${l.careers})`);
    out.push(`  - Terms: ${r.terms.join(', ') || '_none parsed_'}`);
  }
  out.push('');
  return out.join('\n');
}

function main() {
  const skillRoot = path.resolve(__dirname, '..');
  const inputPath = process.argv[2] || path.join(skillRoot, 'output', 'target-companies.md');
  const outputPath = process.argv[3] || path.join(skillRoot, 'output', 'weekly-search.md');

  if (!fs.existsSync(inputPath)) {
    console.error(`Input not found: ${inputPath}`);
    process.exit(1);
  }
  const rows = parse(fs.readFileSync(inputPath, 'utf8'));
  if (rows.length === 0) {
    console.error('No company rows parsed. Check the table format in the input.');
    process.exit(1);
  }
  fs.writeFileSync(outputPath, render(rows));
  console.log(`Parsed ${rows.length} companies → ${outputPath}`);
}

main();
