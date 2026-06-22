// Canonical deep-audit workflow for agentic-council (Phase 5D / --audit mode).
// The conductor invokes this script VERBATIM via the Workflow tool — every
// session-specific value flows through `args`. Do not substitute into the body.
//
// args contract:
//   sessionDir   absolute path to $SESSION_DIR (audit/{zones,} dirs created by 5D.1)
//   workspace    absolute workspace path
//   zones        [{ name, files: [paths] | description, loc }] from the coverage map
//   criteria     audit criteria text (what to look for + severity definitions)
//   auditModel   model tier for zone agents (from the engine routing table)
//   maxPasses    convergence cap (default 5)
//   contextBlock PROJECT_CONTEXT block text
//
// Convergence: a pass with zero new findings (after pass 2) ends the loop.
// A token budget, when set on the invocation, is a hard ceiling — the loop
// also exits early ("budget-converged") when the remaining budget is too thin
// for another pass.

export const meta = {
  name: 'council-audit',
  description: 'Multi-pass codebase audit: zone waves, gap detection, loop until convergence',
  phases: [
    { title: 'Audit', detail: 'parallel zone agents per pass' },
    { title: 'Gap Detection', detail: 'judge flags adjacent zones between passes' },
    { title: 'Report', detail: 'final convergence report' },
  ],
}

const {
  sessionDir, workspace,
  zones = [], criteria = '', auditModel = 'sonnet',
  maxPasses = 5, contextBlock = '',
} = args || {}

if (!sessionDir || !workspace || zones.length === 0) {
  throw new Error('council-audit requires args: sessionDir, workspace, zones[]')
}

const ZONE_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  properties: {
    zone: { type: 'string' },
    findings: {
      type: 'array',
      items: {
        type: 'object',
        additionalProperties: false,
        properties: {
          severity: { type: 'string', enum: ['critical', 'warning', 'info'] },
          file: { type: 'string' },
          description: { type: 'string' },
        },
        required: ['severity', 'file', 'description'],
      },
    },
    summary: { type: 'string' },
    reportPath: { type: 'string' },
  },
  required: ['zone', 'findings', 'summary', 'reportPath'],
}

const GAP_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  properties: {
    zonesToReview: { type: 'array', items: { type: 'string' } },
    rationale: { type: 'string' },
  },
  required: ['zonesToReview', 'rationale'],
}

const PASS_BUDGET_FLOOR = 60000 // rough tokens needed for one more pass + report

const zoneByName = {}
for (const z of zones) zoneByName[z.name] = z

const seen = new Set() // severity|file|description keys across all passes
let pass = 0
let pending = zones.map((z) => z.name)
const allFindings = []
let convergence = 'pass-cap'

while (pass < maxPasses && pending.length > 0) {
  pass += 1
  if (budget.total && budget.remaining() < PASS_BUDGET_FLOOR) {
    convergence = 'budget-converged'
    log(`Pass ${pass}: skipped — ${Math.round(budget.remaining() / 1000)}K tokens remaining is below the per-pass floor`)
    break
  }
  phase('Audit')
  log(`Pass ${pass}: auditing ${pending.length} zone(s)`)

  const results = (await parallel(pending.map((name) => () => {
    const z = zoneByName[name]
    const fileList = Array.isArray(z.files) ? z.files.join('\n') : String(z.files || name)
    return agent(`You are a codebase audit specialist.

## Project Context
${contextBlock}

## Audit Criteria
${criteria}

## Your Zone: ${name}
Files (workspace ${workspace}):
${fileList}

Audit every file in your zone against the criteria. Severity levels:
critical (broken/exploitable), warning (likely problem), info (improvement).
Report every issue you find, including ones you are uncertain about — a
downstream pass filters; your job is coverage.

Write the FULL zone report to ${sessionDir}/audit/zones/pass${pass}-${name.replace(/[^a-zA-Z0-9_-]/g, '_')}.md
and return the structured findings.`,
      { model: auditModel, label: `audit:p${pass}:${name}`, phase: 'Audit', schema: ZONE_SCHEMA })
  }))).filter(Boolean)

  const fresh = []
  for (const r of results) {
    for (const f of r.findings || []) {
      const key = `${f.severity}|${f.file}|${f.description}`
      if (!seen.has(key)) {
        seen.add(key)
        fresh.push({ ...f, zone: r.zone, pass })
      }
    }
  }
  allFindings.push(...fresh)
  log(`Pass ${pass}: ${fresh.length} new finding(s), ${allFindings.length} total`)

  if (fresh.length === 0 && pass >= 2) {
    convergence = 'converged'
    pending = []
    break
  }

  // Gap detection: decide which zones need another look
  phase('Gap Detection')
  const gap = await agent(`You are the audit conductor running gap detection between passes.

Zones available: ${zones.map((z) => z.name).join(', ')}
New findings this pass (pass ${pass}):
${fresh.map((f) => `- [${f.severity}] ${f.zone} ${f.file}: ${f.description}`).join('\n') || '(none)'}

Trace callers/importers of flagged files in ${workspace} (grep imports) and
identify which zones should be re-reviewed next pass: zones containing files
that import or are imported by flagged files, plus zones with critical
findings. Return an empty list if nothing warrants another pass.`,
    { label: `gaps:p${pass}`, phase: 'Gap Detection', schema: GAP_SCHEMA })

  pending = (gap.zonesToReview || []).filter((n) => zoneByName[n])
  if (pending.length === 0 && fresh.length > 0 && pass < 2) {
    // Always run at least a second pass over flagged zones before declaring convergence
    pending = [...new Set(fresh.map((f) => f.zone))].filter((n) => zoneByName[n])
  }
  if (pending.length === 0) {
    convergence = fresh.length === 0 ? 'converged' : 'gap-converged'
  }
}

// ---- Final report ----
phase('Report')
const counts = { critical: 0, warning: 0, info: 0 }
for (const f of allFindings) counts[f.severity] = (counts[f.severity] || 0) + 1

const report = await agent(`You are the audit conductor writing the final convergence report.

Read the per-zone reports under ${sessionDir}/audit/zones/ (passes 1-${pass}).
Cumulative structured findings:
${JSON.stringify(allFindings, null, 2)}

Write these files:
1. ${sessionDir}/audit/report.md — Summary (${pass} passes, ${allFindings.length} findings, convergence: ${convergence}),
   Findings by severity (critical first), final coverage map, prioritized recommendations.
2. ${sessionDir}/audit/findings.md — the cumulative findings log (one line per finding: severity, zone, file, description, pass).
3. Update ${sessionDir}/audit/coverage.md — set every audited zone's Status and Pass columns.
4. Update ${sessionDir}/audit/state.md — set active: false, passes: ${pass}, findings: ${allFindings.length}, convergence: ${convergence}.

Return a one-paragraph summary as plain text.`,
  { label: 'final-report', phase: 'Report' })

if (budget.total) log(`Token budget: ${budget.spent()} spent of ${budget.total}`)

return {
  passes: pass,
  convergence,
  totalFindings: allFindings.length,
  bySeverity: counts,
  reportPath: `${sessionDir}/audit/report.md`,
  summary: report,
}
