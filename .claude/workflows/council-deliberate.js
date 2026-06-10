export const meta = {
  name: 'council-deliberate',
  description: 'Council Phase 3 on the Workflow substrate: position -> challenge -> converge -> synthesized design doc',
  whenToUse: 'Invoked by /council (or directly) to run the 3-round deliberation over selected personas. args: { idea, agents?, context?, sessionDir?, quick? }',
  phases: [
    { title: 'Position', detail: 'each persona writes a grounded position in parallel' },
    { title: 'Pair', detail: 'identify 2-4 tension pairs across positions' },
    { title: 'Challenge', detail: 'paired personas respond to each other' },
    { title: 'Converge', detail: 'final positions with concessions and non-negotiables' },
    { title: 'Synthesize', detail: 'unified design document' },
  ],
}

// args: {
//   idea: string (required)
//   agents: string[] persona names, default classic trio + Craftsman
//   context: string of project context gathered by the caller (optional)
//   sessionDir: if set, agents persist round artifacts there (optional)
//   quick: if true, stop after Round 1 and return a design sketch
// }
const idea = args?.idea
if (!idea) throw new Error('council-deliberate requires args.idea')

const roster = (args?.agents && args.agents.length ? args.agents : ['Architect', 'Advocate', 'Skeptic', 'Craftsman'])
const personaFile = (name) => `agents/council-${name.toLowerCase()}.md`
const context = args?.context ? `\n## Project Context\n${args.context}\n` : ''
const sessionDir = args?.sessionDir || null
const save = (sub) => (sessionDir ? `\nSave a copy of your output to ${sessionDir}/deliberation/${sub}.` : '')

const POSITION = {
  type: 'object',
  properties: {
    recommendation: { type: 'string', description: 'Core recommendation, 1-2 sentences' },
    argument: { type: 'string', description: 'Key argument, one paragraph' },
    risks: { type: 'array', items: { type: 'string' }, description: '2-3 risks if ignored' },
    dependencies: { type: 'string', description: 'Dependencies on other agents\' domains' },
  },
  required: ['recommendation', 'argument', 'risks', 'dependencies'],
}

phase('Position')
log(`Deliberating with ${roster.join(', ')}`)
const positions = (await parallel(roster.map((name) => () =>
  agent(
    `You are the council persona defined in ${personaFile(name)} — read that file first and adopt it fully.\n\n` +
    `Round 1: Position. Write your position statement for: ${idea}\n${context}\n` +
    `Explore the codebase first to ground your position in actual code. ` +
    `Follow the Position format from your persona file.${save(`round1/${name.toLowerCase()}`)}`,
    { label: `position:${name}`, phase: 'Position', schema: POSITION }
  ).then((p) => p && { name, ...p })
))).filter(Boolean)

if (args?.quick) {
  return { mode: 'sketch', idea, positions }
}

phase('Pair')
const positionDigest = positions.map((p) =>
  `### ${p.name}\nRecommendation: ${p.recommendation}\nArgument: ${p.argument}\nRisks: ${p.risks.join('; ')}\nDependencies: ${p.dependencies}`
).join('\n\n')

const pairing = await agent(
  `Here are council position statements on: ${idea}\n\n${positionDigest}\n\n` +
  `Identify 2-4 tension pairs — personas whose positions conflict or create an interesting trade-off. ` +
  `Prefer genuine disagreement over manufactured conflict; return fewer pairs if positions mostly align.`,
  {
    label: 'identify-tensions', phase: 'Pair',
    schema: {
      type: 'object',
      properties: {
        pairs: {
          type: 'array',
          items: {
            type: 'object',
            properties: {
              a: { type: 'string' }, b: { type: 'string' },
              tension: { type: 'string', description: 'one sentence naming the conflict' },
            },
            required: ['a', 'b', 'tension'],
          },
        },
      },
      required: ['pairs'],
    },
  }
)
const pairs = (pairing?.pairs || []).filter((p) => positions.some((x) => x.name === p.a) && positions.some((x) => x.name === p.b))

phase('Challenge')
const byName = Object.fromEntries(positions.map((p) => [p.name, p]))
const challengeOf = (self, other, tension) =>
  agent(
    `You are the council persona defined in ${personaFile(self)} — read that file first and adopt it fully.\n\n` +
    `Round 2: Challenge. Tension under examination: ${tension}\n\n` +
    `${other} wrote this position on "${idea}":\n` +
    `Recommendation: ${byName[other].recommendation}\nArgument: ${byName[other].argument}\nRisks: ${byName[other].risks.join('; ')}\n\n` +
    `Your own Round 1 position was:\nRecommendation: ${byName[self].recommendation}\nArgument: ${byName[self].argument}\n\n` +
    `Respond using your Challenge format: summarize their position; state Maintain, Modify, or Defer; one paragraph of reasoning.${save(`round2/${self.toLowerCase()}-responds-to-${other.toLowerCase()}`)}`,
    {
      label: `challenge:${self}->${other}`, phase: 'Challenge',
      schema: {
        type: 'object',
        properties: {
          stance: { type: 'string', enum: ['Maintain', 'Modify', 'Defer'] },
          summary: { type: 'string' },
          reasoning: { type: 'string' },
        },
        required: ['stance', 'summary', 'reasoning'],
      },
    }
  ).then((r) => r && { self, other, tension, ...r })

const exchanges = (await parallel(pairs.flatMap((p) => [
  () => challengeOf(p.a, p.b, p.tension),
  () => challengeOf(p.b, p.a, p.tension),
]))).filter(Boolean)

phase('Converge')
const exchangeDigest = exchanges.length
  ? exchanges.map((e) => `- ${e.self} -> ${e.other} [${e.stance}] (${e.tension}): ${e.reasoning}`).join('\n')
  : 'No tension pairs were identified; positions largely aligned.'

const finals = (await parallel(roster.map((name) => () =>
  agent(
    `You are the council persona defined in ${personaFile(name)} — read that file first and adopt it fully.\n\n` +
    `Round 3: Converge, on: ${idea}\n\nYour Round 1 position:\n` +
    `Recommendation: ${byName[name]?.recommendation}\nArgument: ${byName[name]?.argument}\n\n` +
    `What happened in the Challenge round:\n${exchangeDigest}\n\n` +
    `Write your final position using your Converge format: revised recommendation; concessions made and why; non-negotiables; implementation notes.${save(`round3/${name.toLowerCase()}`)}`,
    {
      label: `converge:${name}`, phase: 'Converge',
      schema: {
        type: 'object',
        properties: {
          recommendation: { type: 'string' },
          concessions: { type: 'string' },
          nonNegotiables: { type: 'array', items: { type: 'string' } },
          implementationNotes: { type: 'string' },
        },
        required: ['recommendation', 'concessions', 'nonNegotiables', 'implementationNotes'],
      },
    }
  ).then((f) => f && { name, ...f })
))).filter(Boolean)

phase('Synthesize')
const finalDigest = finals.map((f) =>
  `### ${f.name}\nFinal recommendation: ${f.recommendation}\nConcessions: ${f.concessions}\nNon-negotiables: ${f.nonNegotiables.join('; ')}\nImplementation notes: ${f.implementationNotes}`
).join('\n\n')

const designDoc = await agent(
  `Synthesize a unified Design Document for: ${idea}\n${context}\n` +
  `## Final Positions (Round 3)\n${finalDigest}\n\n` +
  `## Challenge Round Exchanges\n${exchangeDigest}\n\n` +
  `Produce a markdown Design Document with sections: Overview; Architecture; User Experience; ` +
  `Risk Assessment; Quality Strategy; Tension Resolutions (how each identified tension was resolved and why); ` +
  `Decision Log. Where a non-negotiable was overridden, say so explicitly and justify it.` +
  (sessionDir ? ` Save the document to ${sessionDir}/design.md as well as returning it.` : ''),
  { label: 'synthesize-design-doc', phase: 'Synthesize' }
)

return { mode: 'full', idea, roster, pairs, designDoc }
