---
description: "Big Ideas Multi-Agent Workflow — interview, design, plan, build"
argument-hint: "[--resume] [IDEA...]"
---

# /council — Big Ideas Multi-Agent Workflow

An interview-first, dynamically-assembled council of perspective agents that collaborate on design and produce an actionable development plan for ambitious features.

## Usage

```
/council                              # Interactive — asks what the big idea is
/council "Build a tournament coach"   # Direct — starts with the idea
/council --resume                     # Resume previous session
```

## Instructions

Parse `$ARGUMENTS` to determine the mode:

- No arguments: Ask the user "What's the big idea?" via `AskUserQuestion`
- Quoted text: Use as the idea directly
- `--resume`: Look for existing session at `$WORKSPACE/.claude/council/session.md`, resume from last phase

### Workspace Detection

Detect the workspace dynamically — **never hardcode paths**:

```
# Try these in order:
1. If inside a git repo: WORKSPACE = git rev-parse --show-toplevel
2. If $PWD has a CLAUDE.md: WORKSPACE = $PWD
3. Ask the user: "What's the workspace path for this project?"
```

### Context Injection

When spawning any agent, inject runtime project context. Read these from the workspace:

```
PROJECT_CONTEXT:
  workspace: $WORKSPACE
  claude_md: <contents of $WORKSPACE/CLAUDE.md, if it exists>
  tech_stack: <inferred from package.json, pyproject.toml, etc.>
  key_dirs: <ls of top-level directories>
```

Include this context block in every agent's spawn prompt so they understand the project without hardcoded paths.

---

## Department Skills System

Each council executive manages a **department** of focused skills — structured prompt templates with methodology, output format, and quality checks. Skills produce higher-quality, more structured output than freestyling.

### Skill Structure

```
.claude/skills/council/
  registry.json                          # Usage tracking across all departments
  architect/
    DEPARTMENT.md                        # Department index
    codebase-context/SKILL.md            # "Tech chief" — infra analysis + context briefing
    schema-design/SKILL.md               # Database schema design
    api-design/SKILL.md                  # REST/RPC endpoint contracts
  skeptic/
    DEPARTMENT.md
    threat-model/SKILL.md                # STRIDE-based threat analysis
    failure-mode-analysis/SKILL.md       # Failure scenarios + mitigations
    edge-case-enumeration/SKILL.md       # Systematic edge case discovery
  advocate/
    DEPARTMENT.md
    journey-mapping/SKILL.md             # User journey with states + emotions
    interaction-design/SKILL.md          # Component specs with all states
  craftsman/
    DEPARTMENT.md
    testing-strategy/SKILL.md            # Test plan with coverage targets
    pattern-analysis/SKILL.md            # Codebase pattern audit + conventions
```

### How Skills Are Used

1. **During Assembly (Phase 2.5):** The conductor reads each selected agent's `DEPARTMENT.md`, matches skill triggers against the idea + interview transcript, selects 1-2 skills per agent, and records loaded skills in `session.md`.
2. **During Deliberation (Phase 3):** Skill content is inlined into agent round messages — agents follow the Process steps and include skill-formatted outputs as appendices.
3. **During Execution (Phase 5):** Task assignments include the relevant skill so agents follow structured methodology.
4. **After session:** The conductor updates `registry.json` (increment uses, set last_used, append session slug) and appends observations to each skill's `## Evolution Notes`.

### Skill Evolution

After each council session, the conductor:
1. Appends an observation to the skill's `## Evolution Notes` section: `<!-- YYYY-MM-DD | session-slug | observation -->`
2. If a skill consistently needs the same adjustment, bumps the `version` in frontmatter and updates the Process steps.

---

## Agent Roster (8 Perspectives)

| # | Agent | Color | Lens | File | Subagent Type |
|---|-------|-------|------|------|---------------|
| 1 | **Architect** | Blue | Systems, APIs, data models, integration | `council-architect` | `Architect` |
| 2 | **Advocate** | Green | UX, product thinking, accessibility | `council-advocate` | `Advocate` |
| 3 | **Skeptic** | Red | Risk, security, devil's advocate | `council-skeptic` | `Skeptic` |
| 4 | **Craftsman** | Purple | Testing, DX, code quality, patterns | `council-craftsman` | `Craftsman` |
| 5 | **Scout** | Cyan | Research, precedent, external knowledge | `council-scout` | `Scout` |
| 6 | **Strategist** | Gold | Business value, scope, MVP, prioritization | `council-strategist` | `general-purpose` |
| 7 | **Operator** | Orange | DevOps, deployment, infra, monitoring | `council-operator` | `general-purpose` |
| 8 | **Chronicler** | Ivory | Documentation, knowledge architecture | `council-chronicler` | `general-purpose` |

---

## Phase 0: Intake

If no idea was provided in `$ARGUMENTS`, use `AskUserQuestion`:

```
What's the big idea?

Describe the feature, system, or capability you want to build.
Be as specific or vague as you like — the council will interview you.
```

Capture the response as `$IDEA`.

---

## Phase 1: Interview (No Agents Spawned)

You (the main agent / conductor) interview the user directly. **No agents are spawned yet.**

### 1.1 Setup

Create the council session directory:

```bash
SLUG=$(echo "$IDEA" | tr '[:upper:]' '[:lower:]' | tr ' ' '-' | sed 's/[^a-z0-9-]//g' | cut -c1-40)
mkdir -p $WORKSPACE/.claude/council/deliberation/{round1,round2,round3}
mkdir -p $WORKSPACE/.claude/prd
```

Write session metadata to `$WORKSPACE/.claude/council/session.md`:

```markdown
# Council Session: <Idea>
Date: <today>
Phase: interview
Slug: <slug>
```

### 1.1b Context Scan

Before interviewing, scan the project to ground your questions in reality:

1. Read `$WORKSPACE/CLAUDE.md` for project conventions
2. Read `package.json` / `pyproject.toml` for tech stack
3. `ls` top-level directories for project structure
4. Read `.claude/skills/council/registry.json` for previously-used skills

Store the scan results mentally — use them to make interview questions specific to the actual project.

### 1.2 Adaptive Interview (2-3 rounds)

Replace the fixed "cover all 8 perspectives" approach with adaptive, context-aware questioning.

**For each round:**

1. **Score the 8 perspectives** (0-5) for relevance to this idea + project context:
   - Architecture, User Experience, Risk, Quality, Research, Strategy, Operations, Documentation
2. **Select top 3-4 perspectives** (score >= 3) for this round
3. **Generate 1 targeted question per selected perspective** that references actual project context:
   - Good: "Your project uses Supabase — should this feature use RLS policies or server-side auth checks?"
   - Bad: "What's your database strategy?"
4. **Follow-up rounds adapt** based on prior answers — don't re-ask addressed topics, dig deeper into gaps

**Round format** — use `AskUserQuestion`:

```
Council Interview — Round <N>/<total>

<question 1 — context-aware, from a specific perspective lens>
<question 2 — context-aware, from a different lens>
<question 3 — context-aware, from a third lens>
```

### 1.3 Interview Summary

After all rounds, write a structured summary to `$WORKSPACE/.claude/council/interview-summary.md`:

```markdown
# Interview Summary: <Idea>

## Core Intent
[1-2 sentences — what the user actually wants to build]

## Key Decisions Made
- [Decision 1 from interview answers]
- [Decision 2 from interview answers]

## Open Questions for Deliberation
- [Question the council should resolve]

## Perspective Relevance Scores
| Perspective | Score (0-5) | Rationale |
|-------------|-------------|-----------|
| Architecture | 5 | New data model + API endpoints needed |
| User Experience | 4 | User-facing feature with complex flow |
| Risk | 3 | Auth implications identified |
| Quality | 3 | Needs testing strategy |
| Research | 1 | No external dependencies |
| Strategy | 2 | Scope already defined |
| Operations | 1 | Standard deployment |
| Documentation | 1 | Minimal docs needed |
```

This relevance table feeds directly into Assembly scoring (Phase 2).

### 1.4 Record Transcript

After each round, append Q&A to `$WORKSPACE/.claude/council/interview-transcript.md`:

```markdown
## Round <N>

**Q:** <question>
**A:** <user's answer>

**Q:** <question>
**A:** <user's answer>
```

---

## Phase 2: Assembly (Agent Selection)

After the interview, score each of the 8 agents for relevance and select 3-6 to participate in deliberation.

### 2.1 Scoring Algorithm

Score each agent 0-10:

1. **Keyword match (0-4):** Count trigger domain keyword hits across `$IDEA` + interview transcript. Normalize to 0-4 scale.
2. **Semantic relevance (0-4):** Your judgment of how relevant the agent's perspective is to this specific idea. Consider:
   - Does this idea touch their domain significantly?
   - Would the plan be weaker without their input?
   - Do interview answers reveal needs in their area?
3. **Modifiers:**
   - **+2 mandatory bonus:** Architect gets +2 for any new functionality. Advocate gets +2 for any user-facing feature. Skeptic gets +2 for any auth/security-related work.
   - **-2 anti-redundancy:** If two agents overlap heavily for this idea (e.g., Craftsman and Operator both scoring on CI/CD), penalize the less relevant one by -2.

### 2.2 Selection Rules

- Score >= 7: **Auto-include**
- Fill to minimum 3 if needed (next highest scores)
- Add agents scoring >= 4 up to cap of 6
- Maximum 6 agents

### 2.3 Present Selection

Show the user the selection with scores and rationale before spawning. Use `AskUserQuestion`:

```
Council Assembly — Agent Selection

Based on the interview, here are the recommended council members:

| Agent | Score | Rationale |
|-------|-------|-----------|
| Architect (Blue) | 9 | New data model and API endpoints needed |
| Advocate (Green) | 8 | User-facing dashboard with complex flows |
| Skeptic (Red) | 7 | Auth implications, data exposure risks |
| Craftsman (Purple) | 5 | Testing strategy for new API layer |

Not selected:
| Scout (Cyan) | 3 | No significant external dependencies |
| Strategist (Gold) | 2 | Scope is already well-defined |
| Operator (Orange) | 2 | Standard Vercel deployment, no special infra |
| Chronicler (Ivory) | 1 | Documentation needs are minimal |

Approve this council, or adjust?
```

Options:
- **Approve** — Spawn selected agents
- **Add agent** — "Which agent should be added?"
- **Remove agent** — "Which agent should be removed?"
- **Restart interview** — Go back to Phase 1

### 2.4 Spawn Team

Once approved, create the team and spawn selected agents:

```
Teammate.spawnTeam:
  operation: "spawnTeam"
  team_name: "council-<slug>"
  description: "Council session for: <idea>"
```

For each selected agent, spawn using the Task tool with `team_name` and `name`:

```
Task:
  name: "council-<agent-name>"
  team_name: "council-<slug>"
  subagent_type: <from roster table>
  prompt: |
    You are <Agent Name>, the <Color> Lens on the Council.

    ## Project Context
    <PROJECT_CONTEXT block>

    ## The Idea
    <$IDEA>

    ## Interview Transcript
    <full interview transcript>

    ## Your Task
    You are participating in a structured deliberation about this idea.
    Read your agent file for your full persona, cognitive framework, and deliberation formats.
    Explore the codebase at $WORKSPACE to understand the current state.

    Wait for the conductor to start Round 1 of deliberation.
```

Update session.md phase to `deliberation`.

### 2.5 Skill Loading

After spawning agents but before deliberation, load relevant skills for each agent:

1. For each selected agent, read their `DEPARTMENT.md` at `.claude/skills/council/<agent>/DEPARTMENT.md`
2. Match skill triggers against `$IDEA` + interview transcript + interview summary
3. Select top 1-2 skills per agent (the most relevant to this session's topic)
4. **Special rule:** If Architect is selected, always load `codebase-context` — its output becomes shared context for all agents
5. Record loaded skills in `session.md`:

```markdown
## Loaded Skills
- Architect: codebase-context, schema-design
- Skeptic: threat-model
- Advocate: journey-mapping
- Craftsman: testing-strategy
```

6. Update `.claude/skills/council/registry.json`:
   - Increment `uses` for each loaded skill
   - Set `last_used` to today's date
   - Append session slug to `sessions` array

---

## Phase 3: Deliberation (3 Rounds)

### Round 1: Position (Parallel)

Send a message to **all agents simultaneously** asking them to write their position statement. **Include loaded skill content inline:**

```
Round 1: Position

Write your position statement for: <$IDEA>

## Your Loaded Skills
<inline the full SKILL.md content for each skill selected in Phase 2.5>

Ground your position using the Process steps from your loaded skills.
Include skill-formatted outputs as appendices to your position.

Follow the Position format from your agent file:
- Core recommendation (1-2 sentences)
- Key argument (1 paragraph)
- Risks if ignored (2-3 bullets)
- Dependencies on other agents' domains

Explore the codebase first to ground your position in the actual code.
Save your position to $WORKSPACE/.claude/council/deliberation/round1/<agent-name>.md
```

Wait for all agents to respond. Collect all position statements.

### Round 2: Challenge (Targeted Pairs)

Read all Round 1 positions. Identify **2-4 tension pairs** — agents whose positions conflict or create interesting trade-offs. Examples:
- Architect wants a new table, Strategist says defer it
- Advocate wants rich interactions, Skeptic flags complexity risks
- Craftsman wants full test coverage, Strategist wants to ship faster

For each tension pair, send both agents each other's position and ask them to respond:

```
Round 2: Challenge

<Other Agent> wrote this position:
<paste their Round 1 position>

Respond using your Challenge format:
- Summarize their position
- State: Maintain, Modify, or Defer
- Your reasoning (1 paragraph)

Save your response to $WORKSPACE/.claude/council/deliberation/round2/<agent-name>-responds-to-<other-agent>.md
```

Agents **not in any tension pair** skip this round.

### Round 3: Converge (Parallel)

Share a summary of all Round 2 exchanges with all agents. Ask each to write their final position:

```
Round 3: Converge

Here's what happened in the Challenge round:
<summary of all Round 2 exchanges — who shifted, who held firm>

Write your final position using your Converge format:
- Revised recommendation
- Concessions made and why
- Non-negotiables
- Implementation notes

Save to $WORKSPACE/.claude/council/deliberation/round3/<agent-name>.md
```

Wait for all agents to respond.

### Synthesis

Read all Round 3 positions. Synthesize into a unified **Design Document**:

```markdown
# Design Document: <Idea>

## Overview
<1-2 paragraph executive summary>

## Architecture
<From Architect's perspective, incorporating challenges>

## User Experience
<From Advocate's perspective, incorporating challenges>

## Risk Assessment
<From Skeptic's perspective, with mitigations agreed upon>

## Quality Strategy
<From Craftsman's perspective>

## [Other sections based on selected agents — Strategy, Operations, Documentation]

## Tension Resolutions
| Tension | Agents | Resolution | Reasoning |
|---------|--------|------------|-----------|
| ... | ... | ... | ... |

## Decision Log
| Decision | Options Considered | Chosen | Reasoning |
|----------|-------------------|--------|-----------|
| ... | ... | ... | ... |
```

Save to `$WORKSPACE/.claude/council/design.md`.

Commit:
```bash
git -C $WORKSPACE add .claude/council/
git -C $WORKSPACE commit -m "docs(council): design document for <idea>"
```

Update session.md phase to `planning`.

---

## Phase 4: Planning

### 4.1 Generate PRD

Produce a PRD from the design document:

```markdown
# PRD: <Idea>

## Overview
<From design document>

## Goals
<Bulleted list>

## Non-Goals
<What's explicitly out of scope>

## Quality Gates
- `npm run build` — Build passes
- `npx tsc --noEmit` — Type checking
- `npx next lint` — Linting
- `npm test` — Tests pass

## User Stories

### US-001: <Story title>
**Description:** As a <user>, I want <capability> so that <benefit>.
**Agent:** <Architect|Advocate|Craftsman|etc.>
**Acceptance Criteria:**
- [ ] <Criterion 1>
- [ ] <Criterion 2>

### US-002: ...
(continue for all stories)

## Technical Notes
<Architecture decisions, data model changes, API contracts>

## Dependencies
<External services, new packages, migration requirements>
```

Save to `$WORKSPACE/.claude/prd/prd-<slug>.md`.

### 4.2 Task Decomposition

Create tasks via `TaskCreate` for each user story. Set up dependencies with `TaskUpdate`.

### 4.3 Plan Summary

Write task breakdown to `$WORKSPACE/.claude/council/plan.md`.

### 4.4 User Approval

Present the plan via `AskUserQuestion`:

```
Council Plan Ready

<N> user stories across <N> tasks.

PRD: .claude/prd/prd-<slug>.md
Design: .claude/council/design.md

How would you like to proceed?
```

Options:
- **Team execution** — Assign tasks to council agents
- **Ralf handoff** — PRD goes to `/ralf` for autonomous execution
- **Launch handoff** — PRD goes to `/launch` in a separate worktree
- **Review first** — Read the PRD and design doc before deciding

### 4.5 Commit

```bash
git -C $WORKSPACE add .claude/council/ .claude/prd/
git -C $WORKSPACE commit -m "docs(council): execution plan and PRD for <idea>"
```

Update session.md phase to `action`.

---

## Phase 5: Action

### Path A: Team Execution

Assign tasks to agents based on their strengths:
- **Architect** — Backend, APIs, database, schema tasks
- **Advocate** — Frontend, components, UX flow tasks
- **Craftsman** — Tests, quality gates, infra tasks
- **Skeptic** — Reviews all changes (read-only, sends feedback)
- **Strategist** — Scope decisions, prioritization during execution
- **Operator** — Deployment, monitoring, infrastructure tasks
- **Chronicler** — Documentation tasks

**Skill injection for task assignments:** When assigning a task, include the relevant skill inline:

```
Task: Design the database schema for X

## Skill: Schema Design
<inline SKILL.md content>

Follow the Process steps. Verify against Quality Checks.
```

Auto-commit during execution:
```bash
git -C $WORKSPACE add <changed-files>
git -C $WORKSPACE commit -m "<type>(<scope>): <description>"
```

### Path B: Ralf Handoff

Tell the user to run:
```
/ralf --from-prd .claude/prd/prd-<slug>.md
```

### Path C: Launch Handoff

Tell the user to run:
```
/launch "<idea>" --from-prd .claude/prd/prd-<slug>.md
```

---

## Session Management

### Resume (`/council --resume`)

1. Read `$WORKSPACE/.claude/council/session.md`
2. Determine last completed phase
3. Resume from the next phase
4. Re-spawn agents as needed for remaining phases

### Artifacts

```
$WORKSPACE/.claude/council/
  session.md                    # Metadata + phase tracking + loaded skills
  interview-transcript.md       # Full Q&A from interview
  interview-summary.md          # Structured summary with relevance scores
  assembly.md                   # Agent selection scores + rationale
  deliberation/
    round1/*.md                 # Position statements (with skill appendices)
    round2/*.md                 # Challenge exchanges
    round3/*.md                 # Final positions
  design.md                     # Synthesized design document
  plan.md                       # Task breakdown
$WORKSPACE/.claude/prd/
  prd-<slug>.md                 # PRD for handoff
```

---

## Cleanup

When the council session is complete:

1. **Evolve skills:** For each loaded skill, append an observation to its `## Evolution Notes`:
   `<!-- YYYY-MM-DD | session-slug | observation about skill effectiveness -->`
2. Send `shutdown_request` to all remaining agents
3. Call `Teammate.cleanup` to remove team resources
4. Update `session.md` with completion status

Artifacts remain in the workspace. The session history is preserved for reference.
