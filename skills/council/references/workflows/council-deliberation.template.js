// Canonical deliberation workflow for agentic-council (all themes).
// The conductor invokes this script VERBATIM via the Workflow tool — every
// session-specific value flows through `args`. Do not substitute into the body.
//
// args contract:
//   sessionDir          absolute path to $SESSION_DIR (must exist, with deliberation/round{1,2,3}/)
//   workspace           absolute workspace path
//   idea                the idea under deliberation
//   contextBlock        PROJECT_CONTEXT block text
//   interviewTranscript interview transcript (or topic summary)
//   pairingRules        $CHALLENGE_RULES text from the theme ("organic" or themed rules)
//   roster              [{ name, agentType, model, color, skillContent }]
//   rounds              3 (default) | 1 for position-only invocations (quick-style, guided gate)
//   maxPairs            max tension pairs (default 4)
//   challengeModel      model tier for Round 2 challenge agents (null → each member's own model)
//   guidedFeedback      user feedback injected into pairing (guided mode, second invocation)
//   startAtRound        1 (default) | 2 to resume from pairing using round1 files on disk
//   designTemplate      reserved; "engine" = the engine's design.md section layout

export const meta = {
  name: 'council-deliberation',
  description: 'Council deliberation: parallel positions, tension-pair challenges, convergence, synthesis',
  phases: [
    { title: 'Position', detail: 'all members write positions in parallel' },
    { title: 'Pairing', detail: 'judge selects 2-4 tension pairs from positions' },
    { title: 'Challenge', detail: 'pair members rebut each other' },
    { title: 'Converge', detail: 'all members write final positions' },
    { title: 'Synthesis', detail: 'conductor persona writes design.md' },
  ],
}

const {
  sessionDir, workspace, idea,
  contextBlock = '', interviewTranscript = '', pairingRules = 'organic',
  roster = [], rounds = 3, maxPairs = 4,
  challengeModel = null, guidedFeedback = null, startAtRound = 1,
} = args || {}

if (!sessionDir || !idea || !Array.isArray(roster) || roster.length === 0) {
  throw new Error('council-deliberation requires args: sessionDir, idea, roster[]')
}

const POSITION_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  properties: {
    agent: { type: 'string' },
    coreRecommendation: { type: 'string' },
    summary: { type: 'string', description: 'Position summary in 120 words or fewer' },
    risks: { type: 'array', items: { type: 'string' } },
    dependencies: { type: 'array', items: { type: 'string' } },
    filePath: { type: 'string' },
  },
  required: ['agent', 'coreRecommendation', 'summary', 'filePath'],
}

const PAIRING_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  properties: {
    pairs: {
      type: 'array',
      items: {
        type: 'object',
        additionalProperties: false,
        properties: {
          a: { type: 'string' },
          b: { type: 'string' },
          tension: { type: 'string' },
          whyItMatters: { type: 'string' },
        },
        required: ['a', 'b', 'tension', 'whyItMatters'],
      },
    },
  },
  required: ['pairs'],
}

const CHALLENGE_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  properties: {
    agent: { type: 'string' },
    stance: { type: 'string', enum: ['Maintain', 'Modify', 'Defer'] },
    summary: { type: 'string', description: 'Exchange summary in 80 words or fewer' },
    filePath: { type: 'string' },
  },
  required: ['agent', 'stance', 'summary', 'filePath'],
}

const CONVERGE_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  properties: {
    agent: { type: 'string' },
    summary: { type: 'string', description: 'Final position summary in 100 words or fewer' },
    nonNegotiables: { type: 'array', items: { type: 'string' } },
    filePath: { type: 'string' },
  },
  required: ['agent', 'summary', 'filePath'],
}

const SYNTHESIS_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  properties: {
    overview: { type: 'string', description: '2-3 sentence executive summary' },
    tensionResolutions: {
      type: 'array',
      items: {
        type: 'object',
        additionalProperties: false,
        properties: {
          tension: { type: 'string' },
          agents: { type: 'string' },
          resolution: { type: 'string' },
          reasoning: { type: 'string' },
        },
        required: ['tension', 'agents', 'resolution', 'reasoning'],
      },
    },
    decisionLog: {
      type: 'array',
      items: {
        type: 'object',
        additionalProperties: false,
        properties: {
          decision: { type: 'string' },
          optionsConsidered: { type: 'string' },
          chosen: { type: 'string' },
          reasoning: { type: 'string' },
        },
        required: ['decision', 'chosen', 'reasoning'],
      },
    },
    designPath: { type: 'string' },
  },
  required: ['overview', 'tensionResolutions', 'decisionLog', 'designPath'],
}

const byName = {}
for (const m of roster) byName[m.name] = m

const identityBlock = (m) => `You are ${m.name}, the ${m.color} Lens.

## Project Context
${contextBlock}

## The Idea
${idea}

## Interview Transcript
${interviewTranscript}`

// ---- Round 1: Position (parallel) ----
let positions = []
if (startAtRound <= 1) {
  phase('Position')
  positions = (await parallel(roster.map((m) => () =>
    agent(`${identityBlock(m)}

## Your Loaded Skills
${m.skillContent || '(none loaded)'}

## Round 1: Position
Explore the codebase at ${workspace} first to ground your position in the actual code.
Ground your position using the Process steps from your loaded skills; include
skill-formatted outputs as appendices.

Write your position statement:
- Core recommendation (1-2 sentences)
- Key argument (1 paragraph)
- Risks if ignored (2-3 bullets)
- Dependencies on other agents' domains

Save the FULL position to ${sessionDir}/deliberation/round1/${m.name}.md and
return the structured summary (the summary field must stand alone — the
conductor reads only summaries).`,
      { agentType: m.agentType, model: m.model, label: `R1:${m.name}`, phase: 'Position', schema: POSITION_SCHEMA }),
  ))).filter(Boolean)
  log(`Round 1 complete: ${positions.length}/${roster.length} positions`)
}

if (rounds === 1) {
  return { positions }
}

// ---- Pairing: judgment over R1 summaries (genuine barrier) ----
phase('Pairing')
const positionDigest = positions.length
  ? JSON.stringify(positions, null, 2)
  : `(positions not in memory — read all files under ${sessionDir}/deliberation/round1/)`
const pairing = await agent(`You are the deliberation conductor selecting tension pairs.

## Challenge Rules
${pairingRules}

## Round 1 Position Summaries
${positionDigest}
${guidedFeedback ? `\n## User Feedback To Weigh\n${guidedFeedback}\n` : ''}
Identify 2-${maxPairs} tension pairs — members whose positions directly
contradict, compete for resources, clash on priorities, or surface a real
trade-off that would change the design. Read the full position files under
${sessionDir}/deliberation/round1/ when a summary is insufficient. Member
names must come from: ${roster.map((m) => m.name).join(', ')}.`,
  { label: 'TensionPairing', phase: 'Pairing', schema: PAIRING_SCHEMA })

const validPairs = (pairing.pairs || [])
  .filter((p) => byName[p.a] && byName[p.b] && p.a !== p.b)
  .slice(0, maxPairs)
log(`Tension pairs: ${validPairs.map((p) => `${p.a}<>${p.b}`).join(', ') || '(none — converging directly)'}`)

// ---- Round 2: Challenge (parallel across pair members) ----
let challenges = []
if (validPairs.length > 0) {
  phase('Challenge')
  challenges = (await parallel(
    validPairs
      .flatMap((p) => [[p.a, p.b, p.tension], [p.b, p.a, p.tension]])
      .map(([selfName, otherName, tension]) => () => {
        const m = byName[selfName]
        return agent(`${identityBlock(m)}

## Round 2: Challenge
Your own Round 1 position is at ${sessionDir}/deliberation/round1/${selfName}.md — read it first; it is YOUR prior work.
${otherName}'s position is at ${sessionDir}/deliberation/round1/${otherName}.md — read it next.

The tension under examination: ${tension}

Respond using your Challenge format:
- Summarize their position
- State: Maintain, Modify, or Defer
- Your reasoning (1 paragraph)

Save the FULL response to ${sessionDir}/deliberation/round2/${selfName}-responds-to-${otherName}.md
and return the structured summary.`,
          { agentType: m.agentType, model: challengeModel || m.model, label: `R2:${selfName}->${otherName}`, phase: 'Challenge', schema: CHALLENGE_SCHEMA })
      }),
  )).filter(Boolean)
}

// ---- Round 3: Converge (parallel, all members) ----
phase('Converge')
const exchangeSummary = challenges.length
  ? challenges.map((c) => `- ${c.agent}: ${c.stance} — ${c.summary}`).join('\n')
  : '(no tension pairs were challenged this session)'
const finals = (await parallel(roster.map((m) => () =>
  agent(`${identityBlock(m)}

## Round 3: Converge
Your Round 1 position is at ${sessionDir}/deliberation/round1/${m.name}.md — read it first; it is YOUR prior work.

Here is what happened in the Challenge round:
${exchangeSummary}

Write your final position using your Converge format:
- Revised recommendation
- Concessions made and why
- Non-negotiables
- Implementation notes

Save the FULL final position to ${sessionDir}/deliberation/round3/${m.name}.md
and return the structured summary.`,
    { agentType: m.agentType, model: m.model, label: `R3:${m.name}`, phase: 'Converge', schema: CONVERGE_SCHEMA }),
))).filter(Boolean)
log(`Round 3 complete: ${finals.length}/${roster.length} final positions`)

// ---- Synthesis: write design.md, return only the structured payload ----
phase('Synthesis')
const synthesis = await agent(`You are the deliberation conductor synthesizing the unified Design Document.

Read ALL files under ${sessionDir}/deliberation/round3/ (and round1/round2 for
context where positions shifted). The idea: ${idea}

Write the Design Document to ${sessionDir}/design.md with exactly these sections:
# Design Document: <Idea>
## Overview (1-2 paragraph executive summary)
## Architecture / ## User Experience / ## Risk Assessment / ## Quality Strategy
   (one section per participating perspective: ${roster.map((m) => m.name).join(', ')})
## Tension Resolutions (table: Tension | Agents | Resolution | Reasoning)
## Decision Log (table: Decision | Options Considered | Chosen | Reasoning)

Return the structured payload mirroring the two tables — the conductor presents
your payload to the user without re-reading the file.`,
  { label: 'Synthesis', phase: 'Synthesis', schema: SYNTHESIS_SCHEMA })

if (budget.total) log(`Token budget: ${budget.spent()} spent of ${budget.total}`)

return {
  pairs: validPairs,
  positions: positions.map((p) => ({ agent: p.agent, summary: p.summary })),
  finals: finals.map((f) => ({ agent: f.agent, summary: f.summary, nonNegotiables: f.nonNegotiables || [] })),
  ...synthesis,
}
