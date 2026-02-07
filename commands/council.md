---
description: "Big Ideas Multi-Agent Workflow — interview, design, plan, build"
argument-hint: "[--resume [SLUG] [--pick]] [--list [--all]] [--archive SLUG] [--cleanup] [--status] [IDEA...]"
---

# /council — Big Ideas Multi-Agent Workflow

An interview-first, dynamically-assembled council of perspective agents that collaborate on design and produce an actionable development plan for ambitious features.

## Usage

```
/council                              # New session (interactive)
/council "Build a tournament coach"   # New session (direct)
/council --resume                     # Resume most recent active session
/council --resume <slug>              # Resume specific session
/council --resume --pick              # Pick from active sessions
/council --list                       # List sessions in workspace
/council --list --all                 # List sessions across all workspaces
/council --archive <slug>             # Export session to GitHub issue
/council --cleanup                    # Review and clean stale sessions
/council --status                     # Quick workspace session summary
```

## Instructions

### Argument Parsing

Parse `$ARGUMENTS` using this priority order — first match wins:

1. **Management commands** (`--list`, `--archive`, `--cleanup`, `--status`): Execute the management workflow (see [Session Management Commands](#session-management-commands)), then **EXIT** — do not start a session.
2. **Resume** (`--resume`): Find and load an existing session (see [Resume Logic](#resume-logic)), then resume from last completed phase.
3. **Direct idea** (quoted text): Use as `$IDEA`, start a new session.
4. **No arguments**: Ask "What's the big idea?" via `AskUserQuestion`, capture response as `$IDEA`.

### Workspace Detection

Detect the workspace dynamically — **never hardcode paths**:

```
# Try these in order:
1. If inside a git repo: WORKSPACE = git rev-parse --show-toplevel
2. If $PWD has a CLAUDE.md: WORKSPACE = $PWD
3. Ask the user: "What's the workspace path for this project?"
```

### Staleness Warning

At the start of every new session (not resume, not management commands), check `$WORKSPACE/.claude/council/index.json` for stale sessions. If any exist:

```
⚠ You have N stale sessions. Run /council --cleanup to review.
```

### Legacy Migration Check

If `$WORKSPACE/.claude/council/session.md` exists (old flat format without a `sessions/` directory), offer to migrate:

```
Legacy session detected. Migrate to multi-session format?
- **Migrate** — Move to sessions/legacy-<slug>-<date>/
- **Skip** — Leave as-is (will be ignored)
- **Delete** — Remove old session files
```

If migrating, move all existing flat files (`session.md`, `interview-*.md`, `assembly.md`, `design.md`, `plan.md`, `deliberation/`) into `sessions/legacy-<slug>-<date>/` and create an `index.json` entry for it.

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
  scout/
    DEPARTMENT.md
    library-evaluation/SKILL.md          # Structured library scoring + comparison
    competitive-analysis/SKILL.md        # Feature comparison matrix
    technology-radar/SKILL.md            # Technology maturity assessment
  strategist/
    DEPARTMENT.md
    mvp-scoping/SKILL.md                 # MoSCoW prioritization + value-effort matrix
    impact-estimation/SKILL.md           # RICE scoring for feature prioritization
    analytics-design/SKILL.md            # Telemetry events + A/B test instrumentation
  operator/
    DEPARTMENT.md
    deployment-plan/SKILL.md             # Deployment strategy + rollback procedures
    observability-design/SKILL.md        # Monitoring, alerting, logging strategy
    cost-analysis/SKILL.md               # Infrastructure cost modeling
  chronicler/
    DEPARTMENT.md
    documentation-plan/SKILL.md          # Documentation architecture + audiences
    adr-template/SKILL.md               # Architecture Decision Record creation
    changelog-design/SKILL.md            # Changelog + migration guide design
  guardian/
    DEPARTMENT.md
    compliance-review/SKILL.md           # GDPR/privacy compliance review
    data-classification/SKILL.md         # Data sensitivity classification
    audit-trail-design/SKILL.md          # Audit logging design
  tuner/
    DEPARTMENT.md
    performance-audit/SKILL.md           # Bottleneck identification + profiling
    caching-strategy/SKILL.md            # Cache hierarchy design
    load-modeling/SKILL.md               # Capacity planning + benchmarks
  alchemist/
    DEPARTMENT.md
    schema-evaluation/SKILL.md           # Data warehouse schema design
    pipeline-design/SKILL.md             # ETL/ELT pipeline architecture
    ml-workflow/SKILL.md                 # ML workflow + experiment tracking
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

## Agent Roster (11 Perspectives)

| # | Agent | Color | Lens | File | Subagent Type |
|---|-------|-------|------|------|---------------|
| 1 | **Architect** | Blue | Systems, APIs, data models, integration | `council-architect` | `Architect` |
| 2 | **Advocate** | Green | UX, product thinking, accessibility | `council-advocate` | `Advocate` |
| 3 | **Skeptic** | Red | Risk, security, devil's advocate | `council-skeptic` | `Skeptic` |
| 4 | **Craftsman** | Purple | Testing, DX, code quality, patterns | `council-craftsman` | `Craftsman` |
| 5 | **Scout** | Cyan | Research, precedent, external knowledge | `council-scout` | `Scout` |
| 6 | **Strategist** | Gold | Business value, scope, MVP, prioritization | `council-strategist` | `Strategist` |
| 7 | **Operator** | Orange | DevOps, deployment, infra, monitoring | `council-operator` | `Operator` |
| 8 | **Chronicler** | Ivory | Documentation, knowledge architecture | `council-chronicler` | `Chronicler` |
| 9 | **Guardian** | Silver | Compliance, governance, privacy | `council-guardian` | `Guardian` |
| 10 | **Tuner** | Amber | Performance, scalability, optimization | `council-tuner` | `Tuner` |
| 11 | **Alchemist** | Indigo | Data engineering, data science, ML, analytics | `council-alchemist` | `Alchemist` |

Selection cap remains at **6 agents max** per session. The larger roster (11) gives more to choose from, not more in every session.

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

Generate a session ID and create the session directory:

```bash
SLUG=$(echo "$IDEA" | tr '[:upper:]' '[:lower:]' | tr ' ' '-' | sed 's/[^a-z0-9-]//g' | cut -c1-40)
TIMESTAMP=$(date +%Y%m%d-%H%M)
SESSION_ID="${SLUG}-${TIMESTAMP}"
SESSION_DIR="$WORKSPACE/.claude/council/sessions/$SESSION_ID"

mkdir -p "$SESSION_DIR/deliberation"/{round1,round2,round3}
mkdir -p "$WORKSPACE/.claude/prd"
```

Write session metadata to `$SESSION_DIR/session.md`:

```markdown
# Council Session: <Idea>
Date: <today>
Session ID: <session-id>
Phase: interview
Slug: <slug>
```

**Update per-workspace index** at `$WORKSPACE/.claude/council/index.json`:

```json
{
  "version": "1.0",
  "workspace": "$WORKSPACE",
  "sessions": [
    {
      "id": "<session-id>",
      "slug": "<slug>",
      "idea": "<idea>",
      "created": "<ISO 8601>",
      "updated": "<ISO 8601>",
      "phase": "interview",
      "status": "active",
      "agents": [],
      "skills_used": [],
      "archived_to": null
    }
  ]
}
```

If `index.json` already exists, append to the `sessions` array. If it doesn't exist, create it.

**Update global registry** at `~/.claude/council/global-registry.json`:

```json
{
  "version": "1.0",
  "workspaces": {
    "$WORKSPACE": {
      "name": "<project-name from package.json or directory name>",
      "last_session": "<ISO 8601>",
      "session_count": <N>,
      "active_sessions": <N>
    }
  },
  "sessions": [
    {
      "id": "<session-id>",
      "workspace": "$WORKSPACE",
      "idea": "<idea>",
      "created": "<ISO 8601>",
      "phase": "interview",
      "status": "active"
    }
  ]
}
```

If `global-registry.json` already exists, merge workspace entry and append session. If it doesn't exist, create it with `mkdir -p ~/.claude/council/`.

### 1.1b Context Scan

Before interviewing, scan the project to ground your questions in reality:

1. Read `$WORKSPACE/CLAUDE.md` for project conventions
2. Read `package.json` / `pyproject.toml` for tech stack
3. `ls` top-level directories for project structure
4. Read `.claude/skills/council/registry.json` for previously-used skills

Store the scan results mentally — use them to make interview questions specific to the actual project.

### 1.2 Adaptive Interview (2-3 rounds)

Replace the fixed "cover all 11 perspectives" approach with adaptive, context-aware questioning.

**For each round:**

1. **Score the 11 perspectives** (0-5) for relevance to this idea + project context:
   - Architecture, User Experience, Risk, Quality, Research, Strategy, Operations, Documentation, Compliance, Performance, Data
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

After all rounds, write a structured summary to `$SESSION_DIR/interview-summary.md`:

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
| Compliance | 4 | Handles user PII, consent required |
| Performance | 2 | Standard load expectations |
```

This relevance table feeds directly into Assembly scoring (Phase 2).

### 1.4 Record Transcript

After each round, append Q&A to `$SESSION_DIR/interview-transcript.md`:

```markdown
## Round <N>

**Q:** <question>
**A:** <user's answer>

**Q:** <question>
**A:** <user's answer>
```

**Update index.json** — set `updated` timestamp and `phase: "interview"`.

---

## Phase 2: Assembly (Agent Selection)

After the interview, score each of the 11 agents for relevance and select 3-6 to participate in deliberation.

### 2.1 Scoring Algorithm

Score each agent 0-10:

1. **Keyword match (0-4):** Count trigger domain keyword hits across `$IDEA` + interview transcript. Normalize to 0-4 scale.
2. **Semantic relevance (0-4):** Your judgment of how relevant the agent's perspective is to this specific idea. Consider:
   - Does this idea touch their domain significantly?
   - Would the plan be weaker without their input?
   - Do interview answers reveal needs in their area?
3. **Modifiers:**
   - **+2 mandatory bonus:** Architect gets +2 for any new functionality. Advocate gets +2 for any user-facing feature. Skeptic gets +2 for any auth/security-related work. Guardian gets +2 for any feature handling user data or PII. Tuner gets +2 for any feature with significant data volume or user-facing performance concerns. Alchemist gets +2 for any feature involving data pipelines, warehousing, ML workflows, or analytics.
   - **-2 anti-redundancy:** If two agents overlap heavily for this idea (e.g., Craftsman and Operator both scoring on CI/CD, or Skeptic and Guardian both scoring on data handling), penalize the less relevant one by -2.

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
| Guardian (Silver) | 7 | Feature handles user PII, consent flows needed |
| Skeptic (Red) | 6 | Auth implications, data exposure risks |

Not selected:
| Tuner (Amber) | 4 | Standard load, no performance concerns |
| Craftsman (Purple) | 3 | Testing strategy straightforward |
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
TeamCreate:
  team_name: "council-<session-id>"
  description: "Council session for: <idea>"
```

For each selected agent, spawn using the Task tool with `team_name` and `name`:

```
Task:
  name: "council-<agent-name>"
  team_name: "council-<session-id>"
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

Update `$SESSION_DIR/session.md` phase to `deliberation`.

### 2.5 Skill Loading

After spawning agents but before deliberation, load relevant skills for each agent:

1. For each selected agent, read their `DEPARTMENT.md` at `.claude/skills/council/<agent>/DEPARTMENT.md`
2. Match skill triggers against `$IDEA` + interview transcript + interview summary
3. Select top 1-2 skills per agent (the most relevant to this session's topic)
4. **Special rule:** If Architect is selected, always load `codebase-context` — its output becomes shared context for all agents
5. Record loaded skills in `$SESSION_DIR/session.md`:

```markdown
## Loaded Skills
- Architect: codebase-context, schema-design
- Skeptic: threat-model
- Advocate: journey-mapping
- Guardian: compliance-review
- Tuner: performance-audit
```

6. Update `.claude/skills/council/registry.json`:
   - Increment `uses` for each loaded skill
   - Set `last_used` to today's date
   - Append session slug to `sessions` array

**Update index.json** — set `agents` array and `skills_used` array, update timestamp.

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
Save your position to $SESSION_DIR/deliberation/round1/<agent-name>.md
```

Wait for all agents to respond. Collect all position statements.

### Round 2: Challenge (Targeted Pairs)

Read all Round 1 positions. Identify **2-4 tension pairs** — agents whose positions conflict or create interesting trade-offs. Examples:
- Architect wants a new table, Strategist says defer it
- Advocate wants rich interactions, Skeptic flags complexity risks
- Craftsman wants full test coverage, Strategist wants to ship faster
- Guardian wants full consent flow, Advocate wants frictionless UX
- Tuner wants caching layer, Architect says premature optimization

For each tension pair, send both agents each other's position and ask them to respond:

```
Round 2: Challenge

<Other Agent> wrote this position:
<paste their Round 1 position>

Respond using your Challenge format:
- Summarize their position
- State: Maintain, Modify, or Defer
- Your reasoning (1 paragraph)

Save your response to $SESSION_DIR/deliberation/round2/<agent-name>-responds-to-<other-agent>.md
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

Save to $SESSION_DIR/deliberation/round3/<agent-name>.md
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

## Compliance & Privacy
<From Guardian's perspective — data handling, consent, audit requirements>

## Performance & Scalability
<From Tuner's perspective — bottlenecks, caching, load projections>

## [Other sections based on selected agents — Research, Strategy, Operations, Documentation]

## Tension Resolutions
| Tension | Agents | Resolution | Reasoning |
|---------|--------|------------|-----------|
| ... | ... | ... | ... |

## Decision Log
| Decision | Options Considered | Chosen | Reasoning |
|----------|-------------------|--------|-----------|
| ... | ... | ... | ... |
```

Save to `$SESSION_DIR/design.md`.

Commit:
```bash
git -C $WORKSPACE add .claude/council/
git -C $WORKSPACE commit -m "docs(council): design document for <idea>"
```

Update `$SESSION_DIR/session.md` phase to `planning`.
**Update index.json** — set `phase: "planning"`, update timestamp.

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
**Agent:** <Architect|Advocate|Craftsman|Guardian|Tuner|etc.>
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

Save PRD inside the session: `$SESSION_DIR/prd.md`

Create a backward-compatible symlink for `/ralf` and `/launch`:
```bash
ln -sf "$SESSION_DIR/prd.md" "$WORKSPACE/.claude/prd/prd-<slug>.md"
```

### 4.2 Task Decomposition

Create tasks via `TaskCreate` for each user story. Set up dependencies with `TaskUpdate`.

### 4.3 Plan Summary

Write task breakdown to `$SESSION_DIR/plan.md`.

### 4.4 User Approval

Present the plan via `AskUserQuestion`:

```
Council Plan Ready

<N> user stories across <N> tasks.

PRD: .claude/council/sessions/<session-id>/prd.md
Design: .claude/council/sessions/<session-id>/design.md

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

Update `$SESSION_DIR/session.md` phase to `action`.
**Update index.json** — set `phase: "action"`, update timestamp.

---

## Phase 5: Action

### Path A: Team Execution

Assign tasks to agents based on their strengths:
- **Architect** — Backend, APIs, database, schema tasks
- **Advocate** — Frontend, components, UX flow tasks
- **Craftsman** — Tests, quality gates, infra tasks
- **Skeptic** — Reviews all changes (read-only, sends feedback)
- **Scout** — Research tasks, library evaluation, competitive analysis
- **Strategist** — Scope decisions, prioritization during execution
- **Operator** — Deployment, monitoring, infrastructure tasks
- **Chronicler** — Documentation tasks
- **Guardian** — Compliance review, data classification, audit trail tasks
- **Tuner** — Performance optimization, caching, load testing tasks
- **Alchemist** — Data pipeline, warehouse schema, ML workflow, analytics tasks

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

### Session Directory Structure

```
$WORKSPACE/.claude/council/
  index.json                                  # Per-workspace session index
  sessions/
    <slug>-<YYYYMMDD-HHmm>/                  # Each session isolated
      session.md
      interview-transcript.md
      interview-summary.md
      assembly.md
      deliberation/
        round1/*.md
        round2/*.md
        round3/*.md
      design.md
      plan.md
      prd.md
$WORKSPACE/.claude/prd/
  prd-<slug>.md                               # Symlink for /ralf backward compat
```

### Global Registry

Cross-workspace session tracking at `~/.claude/council/global-registry.json`. Updated whenever a session is created, updated, archived, or deleted.

### Resume Logic

`/council --resume` behavior:

1. **No slug, no `--pick`:** Resume most recent `active` session by `updated` timestamp from `index.json`
2. **With slug:** Fuzzy-match on slug prefix in `index.json`. If ambiguous (multiple matches), show a picker.
3. **With `--pick`:** Always show interactive picker of all `active` sessions via `AskUserQuestion`.

When resuming:
1. Read `$SESSION_DIR/session.md` to determine last completed phase
2. Read index.json to get session metadata
3. Resume from the next phase
4. Re-spawn agents as needed for remaining phases (use `agents` list from index.json)

### Status Values

| Status | Meaning |
|--------|---------|
| `active` | Session in progress or recently completed work |
| `completed` | All phases finished, artifacts available |
| `archived` | Exported to GitHub issue, local files may be deleted |
| `stale` | Exceeded staleness threshold (auto-set by `--cleanup`) |

---

## Session Management Commands

### `--list`

List sessions in the current workspace from `index.json`:

```
Council Sessions — <project-name>

| # | Session | Status | Phase | Age | Agents |
|---|---------|--------|-------|-----|--------|
| 1 | build-tournament-coach | active | deliberation | 2h | Architect, Advocate, Skeptic, Guardian |
| 2 | add-analytics-dashboard | completed | action | 3d | Architect, Advocate, Tuner, Strategist |
| 3 | refactor-auth-system | archived | — | 14d | — |

Active: 1 | Completed: 1 | Archived: 1
```

**`--list --all`**: Read `~/.claude/council/global-registry.json` and list sessions across all workspaces:

```
Council Sessions — All Workspaces

## my-project (/Users/user/projects/my-project)
| # | Session | Status | Phase | Age |
| 1 | build-tournament-coach | active | deliberation | 2h |

## other-project (/Users/user/projects/other-project)
| 1 | redesign-homepage | completed | action | 5d |

Total: 2 sessions across 2 workspaces
```

### `--status`

Quick summary of the current workspace:

```
Council Status — <project-name>

Active sessions: 1
  └─ build-tournament-coach (deliberation phase, 2h ago)
Completed: 1
Stale: 0

Last session: 2h ago
```

### `--archive <slug>`

Export a session to a GitHub issue for long-term storage.

**Guards:**
- Session must have reached at least `deliberation` phase (has a design.md)
- Workspace must be a git repo with a GitHub remote
- `gh` CLI must be authenticated (test with `gh auth status`)

**Body structure:**

```markdown
## Session Metadata
- **Date:** <created>
- **Agents:** <agent list>
- **Skills Used:** <skill list>
- **Phase Reached:** <phase>

## Interview Summary
<full interview-summary.md>

## Design Document
<full design.md>

## PRD
<full prd.md, if exists>

## Decision Log
<extracted from design.md Tension Resolutions + Decision Log tables>

<details>
<summary>Interview Transcript</summary>

<full interview-transcript.md>
</details>

<details>
<summary>Assembly Scores</summary>

<full assembly.md>
</details>

<details>
<summary>Deliberation — Round 1 Positions</summary>

<concatenated round1/*.md>
</details>

<details>
<summary>Deliberation — Round 2 Challenges</summary>

<concatenated round2/*.md>
</details>

<details>
<summary>Deliberation — Round 3 Convergence</summary>

<concatenated round3/*.md>
</details>
```

**Execution:**

```bash
gh issue create --title "[Council Archive] $IDEA" \
  --label "council-archive,documentation" --body "$BODY"
```

**If body exceeds 60K characters:** Truncate deliberation round details (keep summaries, cut full positions). Warn the user about truncation.

**After creation:**
1. Store issue URL in `index.json` → `"archived_to": "<url>"`
2. Update status to `archived` in both index.json and global registry
3. Ask user via `AskUserQuestion`:

```
Archive created at <url>. Delete local session files?
- **Yes** — Delete session directory
- **No** — Keep local files
```

### `--cleanup`

Interactive workflow to review and clean stale sessions.

**Staleness rules:**

| Status | Stale after |
|--------|-------------|
| `active` | 7 days since `updated` |
| `completed` | 14 days since `updated` |

**Workflow:**

1. Scan `index.json` for sessions matching staleness criteria
2. For each stale session, present via `AskUserQuestion`:

```
Stale session: <idea> (<age> old, phase: <phase>)

- **Archive + Delete** (Recommended) — Export to GitHub issue, then delete local files
- **Delete** — Remove without archiving
- **Skip** — Leave for now
- **Keep** — Reset staleness timer (update `updated` timestamp)
```

3. Execute chosen action for each session
4. Show summary:

```
Cleanup complete:
  Archived: 2
  Deleted: 1
  Skipped: 1
  Kept: 0
  Disk freed: ~450KB
```

**`--cleanup --all`**: Also check global registry for workspaces that no longer exist (deleted projects). Offer to remove orphaned entries.

---

## Cleanup

When the council session is complete:

1. **Evolve skills:** For each loaded skill, append an observation to its `## Evolution Notes`:
   `<!-- YYYY-MM-DD | session-slug | observation about skill effectiveness -->`
2. Send `shutdown_request` to all remaining agents
3. Call `TeamDelete` to remove team resources
4. Update `$SESSION_DIR/session.md` with completion status
5. **Update index.json** — set `status: "completed"`, `phase` to final phase reached, update timestamp
6. **Update global registry** — set session status to `completed`, update workspace metadata

Artifacts remain in the workspace under `sessions/<session-id>/`. The session history is preserved for reference and future archival.
