# Shared Deliberation Engine

This is the **theme-agnostic orchestration core** used by both `/council` and `/academy` (and future themed variants). It is not a standalone command — it is referenced by themed command files that supply configuration variables.

---

## Theme Extension Points

Each themed command file must define these variables before referencing this engine:

| Variable | Purpose | Example (Council) | Example (Academy) |
|----------|---------|--------------------|--------------------|
| `$THEME_ID` | Directory prefix for sessions, teams, artifacts | `council` | `academy` |
| `$THEME_NAME` | Display name in user-facing messages | `Council` | `Officers Academy` |
| `$ROSTER_TABLE` | Agent roster with names, colors, files, subagent types | *(see council.md)* | *(see academy.md)* |
| `$INTAKE_PROMPT` | Phase 0 question text | "What's the big idea?" | "What challenge brings you to the Officers Academy?" |
| `$AGENT_FILE_PREFIX` | Filename prefix for agent personas | `council-` | `academy-` |
| `$MODIFIER_RULES` | Mandatory bonuses and anti-redundancy penalties | *(see council.md)* | *(see academy.md)* |
| `$CHALLENGE_RULES` | How Round 2 tension pairs are identified | Organic (from positions) | House tensions (structured) |
| `$CONDUCTOR_PERSONA` | Agent file the conductor embodies | `council-steward` | `academy-professor` |
| `$SESSION_DIR_ROOT` | Root path for sessions | `.claude/council/sessions/` | `.claude/academy/sessions/` |
| `$TEAM_PREFIX` | Prefix for team names | `council-` | `academy-` |
| `$GLOBAL_REGISTRY_PATH` | Path for cross-workspace registry | `~/.claude/council/global-registry.json` | `~/.claude/academy/global-registry.json` |
| `$INDEX_PATH` | Relative path to workspace index | `.claude/council/index.json` | `.claude/academy/index.json` |
| `$PHASE_LABELS` | Themed labels for each phase | *(see council.md)* | *(see academy.md)* |
| `$ASSEMBLY_LABEL` | Header for the assembly table | "Council Assembly — Agent Selection" | "Academy Assembly — Unit Selection" |
| `$EXTRA_MECHANICS` | Theme-specific mechanics to execute during workflow | *(none)* | Support Conversations, Class Promotion, House Tensions |

---

## Instructions

### Argument Parsing

Parse `$ARGUMENTS` using this priority order — first match wins:

1. **Management commands** (`--list`, `--archive`, `--cleanup`, `--status`): Execute the management workflow (see [Session Management Commands](#session-management-commands)), then **EXIT** — do not start a session.
2. **Resume** (`--resume`): Find and load an existing session (see [Resume Logic](#resume-logic)), then resume from last completed phase.
3. **Direct idea** (quoted text): Use as `$IDEA`, start a new session.
4. **No arguments**: Ask the `$INTAKE_PROMPT` via `AskUserQuestion`, capture response as `$IDEA`.

### Workspace Detection

Detect the workspace dynamically — **never hardcode paths**:

```
# Try these in order:
1. If inside a git repo: WORKSPACE = git rev-parse --show-toplevel
2. If $PWD has a CLAUDE.md: WORKSPACE = $PWD
3. Ask the user: "What's the workspace path for this project?"
```

### Staleness Warning

At the start of every new session (not resume, not management commands), check `$WORKSPACE/$INDEX_PATH` for stale sessions. If any exist:

```
Warning: You have N stale sessions. Run /<command> --cleanup to review.
```

### Legacy Migration Check

If `$WORKSPACE/.claude/$THEME_ID/session.md` exists (old flat format without a `sessions/` directory), offer to migrate:

```
Legacy session detected. Migrate to multi-session format?
- **Migrate** — Move to sessions/legacy-<slug>-<date>/
- **Skip** — Leave as-is (will be ignored)
- **Delete** — Remove old session files
```

If migrating, move all existing flat files (`session.md`, `interview-*.md`, `assembly.md`, `design.md`, `plan.md`, `deliberation/`) into `sessions/legacy-<slug>-<date>/` and create an `$INDEX_PATH` entry for it.

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

Each agent manages a **department** of focused skills — structured prompt templates with methodology, output format, and quality checks. Skills produce higher-quality, more structured output than freestyling.

### Skill Structure

Skills are stored in `.claude/skills/council/` and are **shared across all themes**. Both `/council` and `/academy` agents reference the same skill files.

```
.claude/skills/council/
  registry.json                          # Usage tracking across all departments
  <agent-name>/
    DEPARTMENT.md                        # Department index
    <skill-name>/SKILL.md               # Individual skill template
```

See the themed command file for the full skill tree listing.

### How Skills Are Used

1. **During Assembly (Phase 2.5):** The conductor reads each selected agent's `DEPARTMENT.md`, matches skill triggers against the idea + interview transcript, selects 1-2 skills per agent, and records loaded skills in `session.md`.
2. **During Deliberation (Phase 3):** Skill content is inlined into agent round messages — agents follow the Process steps and include skill-formatted outputs as appendices.
3. **During Execution (Phase 5):** Task assignments include the relevant skill so agents follow structured methodology.
4. **After session:** The conductor updates `registry.json` (increment uses, set last_used, append session slug) and appends observations to each skill's `## Evolution Notes`.

### Skill Evolution

After each session, the conductor:
1. Appends an observation to the skill's `## Evolution Notes` section: `<!-- YYYY-MM-DD | session-slug | observation -->`
2. If a skill consistently needs the same adjustment, bumps the `version` in frontmatter and updates the Process steps.

---

## Phase 0: Intake

If no idea was provided in `$ARGUMENTS`, use `AskUserQuestion` with the themed `$INTAKE_PROMPT`:

```
$INTAKE_PROMPT

Describe the feature, system, or capability you want to build.
Be as specific or vague as you like — the $THEME_NAME will interview you.
```

Capture the response as `$IDEA`.

---

## Phase 1: Interview (No Agents Spawned)

You (the main agent / conductor) interview the user directly, embodying the `$CONDUCTOR_PERSONA`. **No agents are spawned yet.** Read the conductor's agent file for interview philosophy, synthesis methodology, and conflict resolution framework.

### 1.1 Setup

Generate a session ID and create the session directory:

```bash
SLUG=$(echo "$IDEA" | tr '[:upper:]' '[:lower:]' | tr ' ' '-' | sed 's/[^a-z0-9-]//g' | cut -c1-40)
TIMESTAMP=$(date +%Y%m%d-%H%M)
SESSION_ID="${SLUG}-${TIMESTAMP}"
SESSION_DIR="$WORKSPACE/.claude/$THEME_ID/sessions/$SESSION_ID"

mkdir -p "$SESSION_DIR/deliberation"/{round1,round2,round3}
mkdir -p "$WORKSPACE/.claude/prd"
```

Write session metadata to `$SESSION_DIR/session.md`:

```markdown
# $THEME_NAME Session: <Idea>
Date: <today>
Session ID: <session-id>
Phase: interview
Slug: <slug>
```

**Update per-workspace index** at `$WORKSPACE/$INDEX_PATH`:

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

If the index already exists, append to the `sessions` array. If it doesn't exist, create it.

**Update global registry** at `$GLOBAL_REGISTRY_PATH`:

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

If the global registry already exists, merge workspace entry and append session. If it doesn't exist, create it with `mkdir -p`.

### 1.1b Context Scan

Before interviewing, scan the project to ground your questions in reality:

1. Read `$WORKSPACE/CLAUDE.md` for project conventions
2. Read `package.json` / `pyproject.toml` for tech stack
3. `ls` top-level directories for project structure
4. Read `.claude/skills/council/registry.json` for previously-used skills

Store the scan results mentally — use them to make interview questions specific to the actual project.

### 1.2 Adaptive Interview (2-3 rounds)

Replace the fixed "cover all perspectives" approach with adaptive, context-aware questioning.

**For each round:**

1. **Score the perspectives** (0-5) for relevance to this idea + project context. Use the agent roster from `$ROSTER_TABLE` to enumerate perspectives.
2. **Select top 3-4 perspectives** (score >= 3) for this round
3. **Generate 1 targeted question per selected perspective** that references actual project context:
   - Good: "Your project uses Supabase — should this feature use RLS policies or server-side auth checks?"
   - Bad: "What's your database strategy?"
4. **Follow-up rounds adapt** based on prior answers — don't re-ask addressed topics, dig deeper into gaps

**Round format** — use `AskUserQuestion`:

```
$THEME_NAME Interview — Round <N>/<total>

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
- [Question the agents should resolve]

## Perspective Relevance Scores
| Perspective | Score (0-5) | Rationale |
|-------------|-------------|-----------|
| <perspective 1> | <score> | <rationale> |
| ... | ... | ... |
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

**Update index** — set `updated` timestamp and `phase: "interview"`.

---

## Phase 2: Assembly (Agent Selection)

After the interview, score each agent for relevance and select 3-7 to participate in deliberation.

### 2.1 Scoring Algorithm

Score each agent 0-10:

1. **Keyword match (0-4):** Count trigger domain keyword hits across `$IDEA` + interview transcript. Normalize to 0-4 scale.
2. **Semantic relevance (0-4):** Your judgment of how relevant the agent's perspective is to this specific idea. Consider:
   - Does this idea touch their domain significantly?
   - Would the plan be weaker without their input?
   - Do interview answers reveal needs in their area?
3. **Modifiers:** Apply `$MODIFIER_RULES` — mandatory bonuses and anti-redundancy penalties as defined by the theme.

### 2.2 Selection Rules

- Score >= 7: **Auto-include**
- Fill to minimum 3 if needed (next highest scores)
- Add agents scoring >= 4 up to cap of 7
- Maximum 7 agents

### 2.3 Present Selection

Show the user the selection with scores and rationale before spawning. Use `AskUserQuestion`:

```
$ASSEMBLY_LABEL

Based on the interview, here are the recommended members:

| Agent | Score | Rationale |
|-------|-------|-----------|
| <agent 1> | <score> | <rationale> |
| ... | ... | ... |

Not selected:
| <agent> | <score> | <rationale> |
| ... | ... | ... |

Approve this selection, or adjust?
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
  team_name: "$TEAM_PREFIX<session-id>"
  description: "$THEME_NAME session for: <idea>"
```

For each selected agent, spawn using the Task tool with `team_name` and `name`:

```
Task:
  name: "$AGENT_FILE_PREFIX<agent-name>"
  team_name: "$TEAM_PREFIX<session-id>"
  subagent_type: <from roster table>
  prompt: |
    You are <Agent Name>, the <Color> Lens.

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

**Execute `$EXTRA_MECHANICS` for spawn phase** — e.g., Support Conversations rank check, Class Promotion status check.

Update `$SESSION_DIR/session.md` phase to `deliberation`.

### 2.5 Skill Loading

After spawning agents but before deliberation, load relevant skills for each agent:

1. For each selected agent, read their `DEPARTMENT.md` at `.claude/skills/council/<base-agent>/DEPARTMENT.md`
2. Match skill triggers against `$IDEA` + interview transcript + interview summary
3. Select top 1-2 skills per agent (the most relevant to this session's topic)
4. **Special rule:** If the Architect-equivalent is selected, always load `codebase-context` — its output becomes shared context for all agents
5. **Execute `$EXTRA_MECHANICS` for skill loading** — e.g., Class Promotion bonus skills
6. Record loaded skills in `$SESSION_DIR/session.md`:

```markdown
## Loaded Skills
- <Agent 1>: <skill-1>, <skill-2>
- <Agent 2>: <skill-1>
- ...
```

7. Update `.claude/skills/council/registry.json`:
   - Increment `uses` for each loaded skill
   - Set `last_used` to today's date
   - Append session slug to `sessions` array

**Update index** — set `agents` array and `skills_used` array, update timestamp.

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

Read all Round 1 positions. Apply `$CHALLENGE_RULES` to identify **2-4 tension pairs** — agents whose positions conflict or create interesting trade-offs.

For themes with structured challenge rules (e.g., house tensions), follow those rules to determine mandatory pairings. For themes with organic challenge rules, identify pairs from position content.

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
<From the systems/architecture perspective, incorporating challenges>

## User Experience
<From the user advocate perspective, incorporating challenges>

## Risk Assessment
<From the risk/security perspective, with mitigations agreed upon>

## Quality Strategy
<From the quality/testing perspective>

## [Other sections based on selected agents]

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
git -C $WORKSPACE add .claude/$THEME_ID/
git -C $WORKSPACE commit -m "docs($THEME_ID): design document for <idea>"
```

Update `$SESSION_DIR/session.md` phase to `planning`.
**Update index** — set `phase: "planning"`, update timestamp.

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
**Agent:** <Agent name>
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
$THEME_NAME Plan Ready

<N> user stories across <N> tasks.

PRD: .claude/$THEME_ID/sessions/<session-id>/prd.md
Design: .claude/$THEME_ID/sessions/<session-id>/design.md

How would you like to proceed?
```

Options:
- **Team execution** — Assign tasks to agents
- **Ralf handoff** — PRD goes to `/ralf` for autonomous execution
- **Launch handoff** — PRD goes to `/launch` in a separate worktree
- **Review first** — Read the PRD and design doc before deciding

### 4.5 Commit

```bash
git -C $WORKSPACE add .claude/$THEME_ID/ .claude/prd/
git -C $WORKSPACE commit -m "docs($THEME_ID): execution plan and PRD for <idea>"
```

Update `$SESSION_DIR/session.md` phase to `action`.
**Update index** — set `phase: "action"`, update timestamp.

---

## Phase 5: Action

### Path A: Team Execution

Assign tasks to agents based on their strengths. Each theme defines its own agent-to-task mapping in its roster. **Skill injection for task assignments:** When assigning a task, include the relevant skill inline:

```
Task: <task description>

## Skill: <Skill Name>
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
$WORKSPACE/.claude/$THEME_ID/
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

Cross-workspace session tracking at `$GLOBAL_REGISTRY_PATH`. Updated whenever a session is created, updated, archived, or deleted.

### Resume Logic

`--resume` behavior:

1. **No slug, no `--pick`:** Resume most recent `active` session by `updated` timestamp from the index
2. **With slug:** Fuzzy-match on slug prefix in the index. If ambiguous (multiple matches), show a picker.
3. **With `--pick`:** Always show interactive picker of all `active` sessions via `AskUserQuestion`.

When resuming:
1. Read `$SESSION_DIR/session.md` to determine last completed phase
2. Read index to get session metadata
3. Resume from the next phase
4. Re-spawn agents as needed for remaining phases (use `agents` list from index)

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

List sessions in the current workspace from the index:

```
$THEME_NAME Sessions — <project-name>

| # | Session | Status | Phase | Age | Agents |
|---|---------|--------|-------|-----|--------|
| 1 | <session> | <status> | <phase> | <age> | <agents> |
| ... | ... | ... | ... | ... | ... |

Active: N | Completed: N | Archived: N
```

**`--list --all`**: Read the global registry and list sessions across all workspaces:

```
$THEME_NAME Sessions — All Workspaces

## <project-name> (<path>)
| # | Session | Status | Phase | Age |
| ... | ... | ... | ... | ... |

Total: N sessions across N workspaces
```

### `--status`

Quick summary of the current workspace:

```
$THEME_NAME Status — <project-name>

Active sessions: N
  <session tree>
Completed: N
Stale: N

Last session: <age> ago
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
gh issue create --title "[$THEME_NAME Archive] $IDEA" \
  --label "$THEME_ID-archive,documentation" --body "$BODY"
```

**If body exceeds 60K characters:** Truncate deliberation round details (keep summaries, cut full positions). Warn the user about truncation.

**After creation:**
1. Store issue URL in index → `"archived_to": "<url>"`
2. Update status to `archived` in both index and global registry
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

1. Scan index for sessions matching staleness criteria
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
  Archived: N
  Deleted: N
  Skipped: N
  Kept: N
  Disk freed: ~NKB
```

**`--cleanup --all`**: Also check global registry for workspaces that no longer exist (deleted projects). Offer to remove orphaned entries.

---

## Cleanup

When the session is complete:

1. **Evolve skills:** For each loaded skill, append an observation to its `## Evolution Notes`:
   `<!-- YYYY-MM-DD | session-slug | observation about skill effectiveness -->`
2. Send `shutdown_request` to all remaining agents
3. Call `TeamDelete` to remove team resources
4. Update `$SESSION_DIR/session.md` with completion status
5. **Update index** — set `status: "completed"`, `phase` to final phase reached, update timestamp
6. **Update global registry** — set session status to `completed`, update workspace metadata

Artifacts remain in the workspace under `sessions/<session-id>/`. The session history is preserved for reference and future archival.
