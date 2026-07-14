# Shared Deliberation Engine

This is the **theme-agnostic orchestration core** for `/council` (and future themed variants). It is not a standalone command — it is referenced by themed command files that supply configuration variables.

---

## Theme Extension Points

Each themed command file must define these variables before referencing this engine:

| Variable | Purpose | Example |
|----------|---------|---------|
| `$THEME_ID` | Directory prefix for sessions, teams, artifacts | `council` |
| `$THEME_NAME` | Display name in user-facing messages | `Council` |
| `$ROSTER_TABLE` | Agent roster with names, colors, files, subagent types | *(see council.md)* |
| `$INTAKE_PROMPT` | Phase 0 question text | "What's the big idea?" |
| `$AGENT_FILE_PREFIX` | Filename prefix for agent personas | `council-` |
| `$MODIFIER_RULES` | Mandatory bonuses and anti-redundancy penalties | *(see council.md)* |
| `$CHALLENGE_RULES` | How Round 2 tension pairs are identified | Organic (from positions) |
| `$CONDUCTOR_PERSONA` | Agent file the conductor embodies | `council-steward` |
| `$SESSION_DIR_ROOT` | Root path for sessions | `.claude/council/sessions/` |
| `$TEAM_PREFIX` | Prefix for team names | `council-` |
| `$GLOBAL_REGISTRY_PATH` | Path for cross-workspace registry | `~/.claude/council/global-registry.json` |
| `$INDEX_PATH` | Relative path to workspace index | `.claude/council/index.json` |
| `$PHASE_LABELS` | Themed labels for each phase | *(see council.md)* |
| `$ASSEMBLY_LABEL` | Header for the assembly table | "Council Assembly — Agent Selection" |
| `$EXTRA_MECHANICS` | Theme-specific mechanics to execute during workflow | *(none for council)* |
| `$ACTION_PATHS` | Phase 5 action paths the theme supports (in addition to Path A team execution) | *(see council.md — Paths B–F)* |

---

## Instructions

### Preflight: Orchestration Capability Check

The engine selects an orchestration backend per session — it never requires a single runtime and **never hard-exits** here.

1. **Detect teams:** `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS` set to `1` (`printenv CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS` via Bash) → teams available.
2. **Detect workflows:** the Workflow tool is available and `CLAUDE_CODE_DISABLE_WORKFLOWS` is unset/empty (`printenv CLAUDE_CODE_DISABLE_WORKFLOWS`). Workflows require Claude Code ≥ 2.1.154. If a workflow invocation later fails because the runtime is unavailable or disabled by org policy, treat that failure as detection — degrade to the next backend and continue.
3. **Resolve `$ORCH_BACKEND`** per the mode's Backend column in [Mode Configuration](#mode-configuration):
   - `inline` modes need neither capability — plain Task calls.
   - `workflow` modes degrade: workflow → teams → sequential (conductor drives each round with plain parallel Task calls).
   - `teams-preferred` phases degrade: teams → workflow/sequential degradation (documented at the phase).
4. Print a one-line notice of the selected backend when it differs from the mode's preferred backend, e.g. `Orchestration: teams (workflows unavailable)` or `Orchestration: sequential (neither workflows nor agent teams available — slower, same artifacts)`.

The resolved backend is recorded in `session.md` (`Backend:`) during Phase 1.1 setup.

### Argument Parsing & Mode Resolution

Parse `$ARGUMENTS` using this priority order — **first matching flag wins:**

**Session management commands** (execute and exit — no session started):
1. `--help` → Print help text (see [Help Text](#help-text)) and **EXIT**
2. `--list [--all]` → List sessions (see [Session Management Commands](#session-management-commands)) and **EXIT**
3. `--status` → Quick workspace session summary and **EXIT**
4. `--archive <slug>` → Export session to GitHub issue and **EXIT**
5. `--lock <slug>` → Re-create GitHub issue from acceptance contract and **EXIT**
6. `--cleanup [--all]` → Review and clean stale sessions and **EXIT**

**Session modes** (start or resume a session):
7. `--resume [<slug>] [--pick]` → Resume (see [Resume Logic](#resume-logic))
8. `--brainstorm` → **brainstorm** mode
9. `--quick` → **quick** mode
10. `--deep` → **deep** mode
11. `--auto` → **auto** mode
12. `--guided` → **guided** mode
13. `--meet` → **meeting** mode
14. `--audit` → **audit** mode
15. No flag → **standard** mode (default)

**Option flags** (composable with any session mode — parse and strip before mode resolution):
- `--profile <lean|balanced|max>` → set `$PROFILE` (see [Cost Profiles & Model Routing](#cost-profiles--model-routing)). Invalid value → print `Invalid profile. Usage: --profile lean|balanced|max` and **EXIT**. If absent: theme's `$DEFAULT_PROFILE`, else `balanced`.

Strip the matched flag from `$ARGUMENTS`. Remaining text is the **idea**.

### Mode Configuration

| Mode | Phases | Agents | Rounds | Touchpoints | Backend | Budget | Output |
|------|--------|--------|--------|-------------|---------|--------|--------|
| brainstorm | 0 + inline | 3 (sonnet) | 0 | 0 | inline | — | Inline chat only |
| quick | 0, 2, 3(1-round), 4(light) | 3 | 1 | 1 | inline | — | design-sketch.md, task list |
| standard | 0, 1, 2, 3, 4, 5 | 3-7 | 3 | 6-7 | workflow | ~750K | Full design doc, PRD, GitHub issues |
| deep | 0, 1, 2, 3, 4, 5D | 3-7 | 3 | 5-6 | workflow | ~1.5M + ~2M audit | Full design doc, PRD, audit report, GitHub issues |
| auto | 0, 2, 3, 4, 5 | 3-7 | 3 | 0 | workflow | ~750K | Full design doc, PRD, GitHub issues |
| guided | 0, 1, 2, 3, 4, 5 | 3-7 | 3 + gates | 8+ | workflow ×2 | ~750K split | Full design doc, PRD, GitHub issues |
| meeting | 0, 1(light), 2, 3-meeting | 3-7 | Meeting protocol | 2-3 | teams-preferred | — | meeting-notes.md |
| audit | 0, context, 5D | 3-5 | 0 | 2-3 | workflow | ~2M | Deep audit report |

Backend values: `inline` = plain Task calls; `workflow` = background Workflow run (degrades to teams, then sequential); `teams-preferred` = agent teams when available (degrades per phase notes). Budget = token target passed to the workflow invocation (tune per project size).

Every mode except brainstorm additionally maintains `session.html`, the live session page (see [Touchpoint Presentation Contract](#touchpoint-presentation-contract)).

### Cost Profiles & Model Routing

`$PROFILE` controls which model tier each spawned agent runs on. Resolution order: `--profile` flag > theme `$DEFAULT_PROFILE` > `balanced`. Persist the resolved profile in `session.md` and the index; sessions without a recorded profile resume as `balanced`.

Models are fixed at spawn time, so routing is keyed by **spawn site**:

| Spawn site | lean | balanced | max |
|------------|------|----------|-----|
| Brainstorm agents (3× one-shot) | sonnet | sonnet | sonnet |
| Council agents (Phase 2.4 — live R1→R3, Path A execution) | sonnet | opus | opus |
| Round 2 challenge agents | opus (fresh one-shots — see Round 2) | — (persistent agents respond) | fable (fresh one-shots; fall back to opus on spawn error) |
| Audit agents (5D.2 / audit workflow) | sonnet | sonnet | opus |
| Conductor (interview, synthesis, PRD) | inherits the user's `/model` — guidance only, not controlled by the engine | | |

Pass the routed tier as the `model:` parameter on every Task spawn, and as each roster entry's `model` in workflow args. Always use tier aliases (`sonnet`, `opus`, `fable`) — never pinned `claude-*` model IDs (they go stale; the validator rejects them in agent frontmatter).

Source of truth: this table is the prose rendering of `skills/council/model-routing.json` (spec 2.0, `spawn_sites` keyed by profile), validated by `pipeline/hooks/check_model_routing.py`. When editing routing, change the JSON first and update this table to match; on disagreement the JSON wins. Human-readable overview: `docs/model-routing.md`.

**Estimated session cost** (total tokens, 5-agent baseline — scale roughly by `selected agents / 5`):

| Mode | lean | balanced | max |
|------|------|----------|-----|
| brainstorm | 10–15K | 10–15K | 10–15K |
| quick | 20–35K | 30–50K | 45–75K |
| standard | 80–120K | 120–180K | 180–270K |
| deep | standard + 50–80K audit | standard + 50–100K audit | standard + 80–150K audit |

Dollar figures live in the README **Cost guide** (pricing is dated there). On Claude Max plans there is no per-token dollar cost — sessions draw on plan rate limits instead.

**Choosing a profile:**
- `lean` — API-billed / enterprise users: Sonnet positions and converge, Opus only where debate quality pays most (Round 2 challenges).
- `balanced` (default) — Opus deliberation, Sonnet audits.
- `max` — Max-plan users chasing ceiling quality: Opus everywhere, Fable for adversarial challenges.

### Mode Interaction with `$EXTRA_MECHANICS`

When the themed command defines `$EXTRA_MECHANICS`, apply these rules per mode:

| Mode | Extra Mechanics Behavior |
|------|--------------------------|
| brainstorm | **Skip all** — no team, no mechanics |
| quick | **Skip all** — no support conversation check, no house tension mechanics, no promotion announcements |
| auto | **Auto-advance** — auto-advance promotions, skip support logging, skip interactive mechanics |
| meeting | **Partial** — house tensions still apply for cross-examination pairing; skip support logging and promotion tracking |
| standard / deep / guided | **All active** — full mechanics at appropriate phases |
| audit | **Skip all** — direct audit, no deliberation mechanics |

### Help Text

When `--help` is matched, output this (substituting `$THEME_NAME` and the theme's command name) and **EXIT**:

```
/<command> — $THEME_NAME Multi-Agent Workflow

USAGE:
  /<command> [MODE] [IDEA...]

MODES:
  (default)       Full session — interview, deliberate, plan, build
  --brainstorm    Quick gut-check from 3 agents, inline output (~30s)
  --quick         Fast sketch — skip interview, 1-round deliberation (~3 min)
  --deep          Max rigor — full session + mandatory deep audit (~1 hr)
  --auto          Hands-off — no touchpoints, auto-approve everything (~10 min)
  --guided        Tight control — approval gates at every phase (~30 min)
  --meet          Discussion only — cross-examination, no action plan (~15 min)
  --audit         Direct codebase audit — skip straight to deep audit (~10 min)

SESSION MANAGEMENT:
  --resume                Resume most recent active session
  --resume <slug>         Resume a specific session
  --resume --pick         Pick from active sessions interactively
  --list                  List sessions in current workspace
  --list --all            List sessions across all workspaces
  --status                Quick workspace session summary
  --archive <slug>        Export session to GitHub issue
  --lock <slug>          Re-create GitHub issue from acceptance contract
  --cleanup               Review and clean stale sessions

OTHER:
  --profile <p>   Cost profile: lean | balanced | max (default: balanced)
  --help          Show this help message

EXAMPLES:
  /<command> "Build a tournament coach"
  /<command> --quick "Add a speed tier sidebar"
  /<command> --deep --profile lean "Redesign auth" (Sonnet agents, Opus challenges)
  /<command> --meet "Should we migrate to Drizzle?"
  /<command> --auto "Add dark mode toggle"
  /<command> --deep "Redesign the authentication system"
  /<command> --audit "Review our API security"
  /<command> --brainstorm "What about a replay analyzer?"
  /<command> --list
  /<command> --resume --pick
```

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
  workspace_config: <contents of workspace config, if found — see below>
```

**Workspace Lookup:** Check for a pre-configured workspace:
1. Determine the project name from `git remote get-url origin` (extract repo name) or fall back to the workspace directory name
2. Look for `~/.claude/workspaces/<project-name>/INFRASTRUCTURE_MAP.md`
3. If found, read it and include in the PROJECT_CONTEXT block as `workspace_config`
4. If not found, proceed normally — no error, just skip the workspace config

Include this context block in every agent's spawn prompt so they understand the project without hardcoded paths.

### Touchpoint Presentation Contract

Every user-facing decision point must be self-contained in chat, and every file-creating session maintains a live HTML window. Both rules exist because context that lives only in a file or a prior turn never reaches the user.

1. **No blind references.** An `AskUserQuestion` may never rely on "the detail above", a previous turn, or a file path as its only context. Restate the decision-relevant facts compactly (a short table or 3-6 bullets) inside the question text itself.
2. **Detail asides.** When the conductor produces comparison detail mid-phase (option shapes, trade-off tables), it must (a) print a compact rendering in chat, (b) write the full version to `$SESSION_DIR/detail-<n>.md`, and (c) rerun the scribe.
3. **Live session page setup (Phase 1.1, all file-creating modes; brainstorm excluded).** Copy the scribe and its template into the session dir, write the initial `session-state.json`, render, and open the page once:

   ```bash
   cp ~/.claude/skills/council/references/render-session.py "$SESSION_DIR/"
   cp ~/.claude/skills/council/references/session-page.template.html "$SESSION_DIR/"
   # write session-state.json first (schema below), then:
   python3 "$SESSION_DIR/render-session.py" "$SESSION_DIR" || true
   open "$SESSION_DIR/session.html" 2>/dev/null || xdg-open "$SESSION_DIR/session.html" 2>/dev/null || echo "Live page: $SESSION_DIR/session.html"
   ```

4. **Scribe hooks.** Rerun `python3 "$SESSION_DIR/render-session.py" "$SESSION_DIR" || true` after: each interview round, assembly approval, each deliberation artifact (workflow agents run it themselves via `scribePath`; on teams/sequential backends the conductor runs it between rounds), synthesis, PRD and contract generation, the verification sweep, and cleanup. Update `session-state.json` first at each phase transition.
5. **`session-state.json` schema of record:**

   ```json
   {
     "phase": "deliberation",
     "complete": false,
     "idea": "...",
     "themeName": "Council",
     "sessionId": "<session-id>",
     "date": "<YYYY-MM-DD>",
     "mode": "standard",
     "profile": "balanced",
     "backend": "workflow",
     "roster": [{"name": "Architect", "color": "#60a5fa", "score": 9, "rationale": "...", "skills": ["codebase-context"], "status": "active"}],
     "tensionPairs": [{"a": "Architect", "b": "Skeptic", "tension": "..."}],
     "costEstimate": "~120-180K tokens",
     "phases": ["interview", "assembly", "deliberation", "verdict", "planning", "verification"]
   }
   ```

   Set `phases` to only the phases the resolved mode runs (for example quick mode omits `interview` and `verification`).
6. **Degradation.** A scribe or `open` failure is silent and never blocks the text flow. Markdown files remain the artifacts of record; `AskUserQuestion` remains the sole approval mechanism. In headless environments print the page path once so the user can open it elsewhere.

---

## Department Skills System

Each agent manages a **department** of focused skills — structured prompt templates with methodology, output format, and quality checks. Skills produce higher-quality, more structured output than freestyling.

### Skill Structure

Skills are stored in `~/.claude/skills/council/` (symlinked to this setup's `skills/council/`).

```
~/.claude/skills/council/
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

## Mode-Aware Phase Dispatch

After resolving `$MODE`, execute phases according to the mode's configuration:

| Mode | Phase Sequence |
|------|---------------|
| brainstorm | Phase 0 → [Brainstorm Protocol](#brainstorm-protocol) → done |
| quick | Phase 0 → Phase 2 (auto) → Phase 3 (1-round) → Phase 4 (light) → done |
| standard | Phase 0 → Phase 1 → Phase 2 → Phase 3 (+ design review) → Phase 4 (+ scope review) → Phase 5 → Cleanup |
| deep | Phase 0 → Phase 1 → Phase 2 → Phase 3 → Phase 4 → Phase 5D → Cleanup |
| auto | Phase 0 → Phase 2 (auto) → Phase 3 → Phase 4 (auto) → Phase 5 → Cleanup |
| guided | Phase 0 → Phase 1 → Phase 2 → Phase 3 (+ gates) → Phase 4 (+ gates) → Phase 5 (+ gates) → Cleanup |
| meeting | Phase 0 → Phase 1 (light) → Phase 2 → [Meeting Protocol](#phase-3-meeting-cross-examination) → Cleanup |
| audit | Phase 0 → Context Scan → Phase 5D → Cleanup |

Apply mode overrides at each phase as documented in the mode-specific notes below.

---

## Phase 0: Intake

### Standard / Deep / Guided / Meeting

If no idea was provided in `$ARGUMENTS`, use `AskUserQuestion` with the themed `$INTAKE_PROMPT`:

```
$INTAKE_PROMPT

Describe the feature, system, or capability you want to build.
Be as specific or vague as you like — the $THEME_NAME will interview you.
```

Capture the response as `$IDEA`.

### Auto Mode Override

In **auto** mode, the idea **must** come from `$ARGUMENTS`. If no args provided after the flag, **error and exit:**

```
Auto mode requires an idea. Usage: /<command> --auto "your idea here"
```

Do NOT ask via `AskUserQuestion`.

### Quick Mode Override

Get idea from args or ask briefly. No interview will follow.

### Meeting Mode Override

The intake prompt becomes: "What do you want to discuss with the $THEME_NAME?"

### Audit Mode Override

The idea becomes audit criteria. The intake prompt becomes: "What should the audit focus on?"

---

## Brainstorm Protocol

**Mode: `--brainstorm`** — Quick gut-check from 3 parallel perspectives. No files, no team, no ceremony.

1. Use the idea from `$ARGUMENTS`. If no idea, ask via `AskUserQuestion`.
2. Gather project context:
   - Read `$WORKSPACE/CLAUDE.md` (if exists)
   - Read `package.json` / `pyproject.toml` for tech stack
   - `ls` top-level directories
   - `git branch --show-current` + `git log --oneline -3`
3. Launch **3 Task agents** in parallel (single message, 3 tool calls). Each uses `subagent_type: "general-purpose"` with `model:` from the Brainstorm row of the [model routing table](#cost-profiles--model-routing) (`sonnet` in every profile):

   **Architect:** Systems/technical perspective — where it fits, what to build, architectural considerations (2-4 sentences).

   **Advocate:** UX/product perspective — is it good for users, what should the interaction feel like, what's missing (2-4 sentences).

   **Skeptic:** Critical/risk perspective — what could go wrong, unnecessary scope, simpler version (2-4 sentences).

4. Once all 3 return, synthesize and present inline:

```
## Quick $THEME_NAME: `<idea summary>`

**Architect** says: <their take>

**Advocate** says: <their take>

**Skeptic** says: <their take>

---

**Where they agree:** <1-2 sentences>
**Key tension:** <1 sentence>
**Recommended next step:** <concrete suggestion>
```

5. **No files created. No team spawned. No cleanup needed. EXIT.**

---

## Phase 1: Interview (No Agents Spawned)

**Mode applicability:** Standard, Deep, Guided run full interview. Meeting runs light interview (1 round). Quick, Auto, Brainstorm, Audit **skip this phase entirely**.

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

Then set up the live session page per the [Touchpoint Presentation Contract](#touchpoint-presentation-contract) item 3: copy the scribe and template into `$SESSION_DIR`, write the initial `session-state.json` (`phase: "interview"`, empty roster, the resolved mode/profile/backend), render, and open the page once.

Write session metadata to `$SESSION_DIR/session.md`:

```markdown
# $THEME_NAME Session: <Idea>
Date: <today>
Session ID: <session-id>
Phase: interview
Slug: <slug>
Profile: <resolved $PROFILE>
Backend: <resolved $ORCH_BACKEND>
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
      "profile": "<resolved $PROFILE>",
      "agents": [],
      "skills_used": [],
      "contract_generated": false,
      "contract_issue": null,
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
4. Read `~/.claude/skills/council/registry.json` for previously-used skills (create empty `{}` file if missing)

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

Rerun the scribe after appending each round (contract item 4).

### Meeting Mode: Light Interview

In **meeting** mode, run only **1 quick round**. Goal: understand the topic and what kind of perspectives are needed. Ask 2-3 clarifying questions, then move on to Phase 2. Skip the full interview summary — write a brief topic summary instead.

### Guided Mode: Interview Approval Gate

In **guided** mode, after writing the interview summary, present it to the user:

```
Here's the interview summary. Does this capture your intent?
```

Options:
- **Approve** — Proceed to Assembly
- **Revise** — Loop back into interview for additional round

---

## Phase 2: Assembly (Agent Selection)

**Mode applicability:** All modes except Brainstorm and Audit (which skip assembly).

After the interview (or context scan for modes that skip interview), score each agent for relevance and select agents to participate in deliberation.

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

**Quick / Auto mode override:** Select top **3** agents by score. No gap analysis, no user approval. Auto-approve and spawn immediately. Print (don't ask) a one-line estimate first: `Estimated: ~<range from the mode × profile table> tokens (mode: <mode>, profile: <profile>, 3 agents).`

### 2.3 Present Selection

Before presenting, update `session-state.json` (`phase: "assembly"`, full `roster` with names, lens colors, scores, rationale, and `costEstimate`) and rerun the scribe so the live page shows the full bench detail.

Show the user the selection with scores and rationale before spawning. The table below is mandatory inside the question text (contract item 1: never present bare options). Use `AskUserQuestion`:

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

Estimated cost — mode: <mode>, profile: <profile>, agents: <N>
  Tokens: ~<range from the mode × profile table, scaled by N/5> total
  API billing: see README Cost guide for current $/MTok; Claude Max plans draw on rate limits, not dollars
  Conductor runs on your session model: <current /model> (synthesis + PRD quality follow it)

Approve this selection, or adjust?
```

Options:
- **Approve** — Spawn selected agents
- **Add agent** — "Which agent should be added?"
- **Remove agent** — "Which agent should be removed?"
- **Restart interview** — Go back to Phase 1

### 2.4 Prepare Roster / Spawn Team (backend-dependent)

**Workflow / inline / sequential backends:** Do **not** create a team. Record the deliberation roster for Phase 3 instead — for each selected agent: `{ name, agentType: <Subagent Type column from roster table>, model: <council-agent tier from the routing table>, color, skillContent: <inlined in Phase 2.5> }`. Update `$SESSION_DIR/session.md` phase to `deliberation`, run `$EXTRA_MECHANICS` for spawn phase, and continue to Phase 2.5.

**Teams backend:** create the team and spawn selected agents:

```
TeamCreate:
  team_name: "$TEAM_PREFIX<session-id>"
  description: "$THEME_NAME session for: <idea>"
```

For each selected agent, spawn using the Task tool with `team_name`, `name`, and the profile-routed model:

```
Task:
  name: "$AGENT_FILE_PREFIX<agent-name>"
  team_name: "$TEAM_PREFIX<session-id>"
  subagent_type: <from roster table>
  model: <council-agent tier from the routing table>
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

1. For each selected agent, read their `DEPARTMENT.md` at `~/.claude/skills/council/<base-agent>/DEPARTMENT.md` to get the list of skills available
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

7. Update `~/.claude/skills/council/registry.json` (create with `{}` if missing):
   - Increment `uses` for each loaded skill
   - Set `last_used` to today's date
   - Append session slug to `sessions` array

**Update index** — set `agents` array and `skills_used` array, update timestamp.

---

## Phase 3: Deliberation (3 Rounds)

**Mode applicability:** Standard, Deep, Auto, Guided run full 3-round deliberation. Quick runs 1 round only. Meeting uses [Meeting Protocol](#phase-3-meeting-cross-examination) instead. Brainstorm and Audit skip this phase.

### Deliberation via Workflow (primary — workflow backend)

Run the full R1 → pairing → R2 → R3 → synthesis loop as a background Workflow so round texts never enter the conductor's context.

1. Read the canonical script at `~/.claude/skills/council/references/workflows/council-deliberation.template.js` and invoke the **Workflow tool** with that script verbatim (everything session-specific flows through `args` — substitute nothing in the script body). Pass `args` as an **actual JSON object** in the tool call, never a JSON-encoded string — a stringified payload reaches the script as one string and the contract guard throws `requires args: sessionDir, idea, roster[]`:

   ```
   args:
     sessionDir: <absolute $SESSION_DIR>
     workspace: $WORKSPACE
     idea: $IDEA
     contextBlock: <PROJECT_CONTEXT block>
     interviewTranscript: <full transcript, or topic summary for modes without interview>
     pairingRules: <$CHALLENGE_RULES text from the theme>
     roster: [{ name, agentType, model, color, skillContent }]   # from Phase 2.4/2.5
     rounds: 3
     maxPairs: 4
     challengeModel: <Round 2 tier from the routing table, or null for balanced (persistent-style prompts still run as fresh agents)>
     designTemplate: "engine"                                    # script knows the design.md section layout
     scribePath: <absolute $SESSION_DIR>/render-session.py      # agents rerun the live page after each save
   ```

   Before invoking, update `session-state.json` (`phase: "deliberation"`, roster statuses) and rerun the scribe.

2. The run executes in the background — the session stays responsive; check progress via the workflow's progress view if the user asks.
3. On completion the workflow returns **only** the structured synthesis payload (tension pairs, Tension Resolutions rows, Decision Log rows, overview). All round files and `design.md` are already on disk under `$SESSION_DIR`.
4. Continue at [Synthesis](#synthesis) — commit, then present the design-approval touchpoint **from the returned payload**; do not re-read round files into context.

**Guided mode (workflow backend):** invoke the script twice. First with `rounds: 1` (positions only — script returns position summaries), present the positions gate below, then re-invoke with `startAtRound: 2` and the user's feedback as `guidedFeedback`. Round 1 files on disk carry over between invocations.

**Quick mode (inline backend):** no workflow, no team. Run Round 1 as one parallel batch of one-shot Task calls — for each of the 3 selected agents: `subagent_type` from the roster, `model:` from the routing table, prompt = the Round 1 prompt below plus the instruction to read their persona file for formats. Then produce the design sketch as described under Quick mode below.

**Sequential fallback (neither workflows nor teams):** the conductor drives the same three rounds with plain Task calls — R1 as one parallel batch of one-shots (Round 1 prompt below), pairing by conductor judgment as in Round 2 below, R2/R3 as fresh one-shots whose prompts instruct them to read their own prior round file(s) from `$SESSION_DIR/deliberation/` first. Slower, but identical artifacts.

**Live page on teams/sequential backends:** the conductor reruns the scribe after each round completes (and updates `tensionPairs` in `session-state.json` after pairing). On the workflow backend the agents themselves handle this via `scribePath`.

### Deliberation via Teams (teams backend)

When `$ORCH_BACKEND` is teams, drive the persistent teammates through the three rounds below by team message.

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

**Quick mode:** After Round 1, **skip Rounds 2-3**. Produce a **design sketch** instead of a full design doc:
- Overview: What we're building and why
- Key recommendations from each agent
- Open questions / trade-offs identified

Save as `$SESSION_DIR/design-sketch.md`. Proceed to Phase 4 (lightweight plan).

**Guided mode:** After collecting positions, present them to the user:
```
Here are the initial positions. Any feedback before they debate?
```
Options:
- **Continue** — Proceed to Round 2
- **Provide feedback** — Inject feedback into Round 2 context

### Round 2: Challenge (Targeted Pairs)

Read all Round 1 positions. Apply `$CHALLENGE_RULES` to identify **2-4 tension pairs** — agents whose positions conflict or create interesting trade-offs.

For themes with structured challenge rules (e.g., house tensions), follow those rules to determine mandatory pairings. For themes with organic challenge rules, identify pairs from position content.

**Profile override (lean / max):** do **not** message the persistent agents for Round 2. For each tension pair, spawn a fresh one-shot Task per member — `subagent_type` from the roster, `model:` from the Round 2 row of the [routing table](#cost-profiles--model-routing) — whose prompt includes the PROJECT_CONTEXT block and instructs it to read **both** Round 1 position files from `$SESSION_DIR/deliberation/round1/` (its own first) before responding in the Challenge format. Output paths unchanged. If a `fable` spawn errors, retry the spawn with `opus`. Round 3 returns to the persistent agents as normal.

For each tension pair (balanced profile), send both agents each other's position and ask them to respond:

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

**Workflow backend:** the workflow has already written `design.md` and returned the structured payload — skip the synthesis writing below and go straight to the commit and the design-approval presentation, sourcing the tables from the returned payload.

**Teams / sequential backends:** read all Round 3 positions. Synthesize into a unified **Design Document**:

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

**HTML verdict render (Standard / Deep / Guided):** Before the approval question, render the synthesis payload as a self-contained HTML page and open it in the browser:

1. Read the reference template at `~/.claude/skills/council/references/design-verdict.template.html` (structure: masthead with session metadata and lens-color spectrum, two-track plan rails, tension ledger with per-agent lens dots and centered verdicts, risk cards, decision-log table). Fill it from the synthesis payload (overview, tension resolutions, decision log) plus session metadata; substitute the `{{...}}` placeholders and repeat the marked row/card blocks per item. The two-track and risk-card sections are OPTIONAL: fill them only when the payload's decision log carries phased-plan or severity data; otherwise delete them rather than fabricating content or re-reading deliberation files. Use each participating agent's lens color for attribution dots (distinct hex per agent; see the template's color comment).
2. Write the result to `$SESSION_DIR/design.html` and open it (`open` on macOS, `xdg-open` on Linux).
3. **Graceful degradation:** if the template is missing, the write fails, or no GUI browser is available, skip the render silently and proceed. The HTML is presentation only; `design.md` remains the artifact of record and `AskUserQuestion` below remains the sole approval mechanism.
4. Update `session-state.json` (`phase: "verdict"`, `tensionPairs` from the synthesis payload) and rerun the scribe; the live page's Verdict section links to `design.html`.

**Standard / Deep mode:** After synthesis (and the HTML render, when available), present the key decisions to the user via `AskUserQuestion`:

```
Design Document Ready — Key Decisions

<2-3 sentence overview from design doc's Overview section>

Tension Resolutions:
| Tension | Resolution | Reasoning |
|---------|------------|-----------|
<rows from design.md Tension Resolutions table>

Decision Log:
| Decision | Chosen | Reasoning |
|----------|--------|-----------|
<rows from design.md Decision Log table>

Approve this design direction, or adjust before planning?
```
Options:
- **Approve** — Proceed to PRD generation (Phase 4)
- **Adjust** — Describe what to change; conductor revises design.md and re-presents

**Auto mode:** Skip (auto-approve).

**Guided mode:** After synthesis, present the design document to the user:
```
Here's the design document. Approve before generating PRD?
```
Options:
- **Approve** — Proceed to Phase 4
- **Revise** — Conductor adjusts design based on feedback
- **Re-deliberate** — Run another round of deliberation

---

## Phase 3-Meeting: Cross-Examination Protocol

**Mode: `--meet`** — This phase replaces standard Phase 3 deliberation when running in meeting mode. Agents interact with each other directly — asking questions, challenging claims, and building on each other's ideas.

**Backend: teams-preferred.** Live cross-examination — direct agent-to-agent questions, conditional follow-ups, and the user steering individual panelists (Shift+Down) — is what the agent-teams runtime is for. Without the teams flag, degrade: run sub-rounds 2a/2b as fixed phases of fresh one-shot Tasks that read prior outputs from `$SESSION_DIR`, allow exactly one follow-up phase, and print: `Note: live steering of individual panel members requires CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1.`

### Round 1: Opening Perspectives

Send to **each agent in parallel:**

```
TOPIC: <the discussion topic>
CONTEXT: <project context block>
INTERVIEW NOTES: <from Phase 1 light interview>

Share your opening perspective on this topic in 3-5 sentences.
- What is your initial take?
- What aspect falls most squarely in your domain?
- What is the most important question or consideration from your lens?
```

Collect all opening perspectives.

### Round 2: Cross-Examination (2-3 sub-rounds)

**Sub-Round 2a — Questions:** Share ALL opening perspectives with each agent. Ask each to write 1-2 questions directed at specific other agents, focusing on disagreements, gaps, or domain intersections.

**Sub-Round 2b — Responses:** Route each question to its target agent. Each responds concisely (2-3 sentences) and may pose an optional follow-up question.

**Sub-Round 2c — Follow-ups (optional):** If there are follow-up questions from 2b, route them for one more round. **Maximum 1 follow-up round.**

### Round 3: Collective Synthesis

Share the full discussion transcript with all agents. Each provides:
- **Key insight gained** from the discussion
- **Unresolved tension** the group didn't fully resolve
- **Recommendation to the user**
- **Question for the user** the agents couldn't resolve themselves

### Compile Meeting Notes

Assemble `$SESSION_DIR/meeting-notes.md`:

```markdown
# $THEME_NAME Meeting: <topic summary>
**Date:** <YYYY-MM-DD>
**Panel:** <list of agents>

## Topic
<the discussion topic>

## Opening Perspectives
<each agent's opening perspective, labeled>

## Cross-Examination Highlights
<curated 3-5 most valuable exchanges>

## Key Insights
<one insight per agent>

## Unresolved Tensions
<trade-offs and disagreements identified>

## Questions for You
<questions the agents couldn't resolve>

## Recommended Next Steps
<2-3 concrete suggestions>
```

Present a summary to the user inline, then reference the full notes file.

**After meeting:** Skip Phases 4-5. Proceed directly to Cleanup.

---

## Phase 4: Planning

**Mode applicability:** Standard, Deep, Auto, Guided run full planning. Quick runs lightweight planning. Meeting, Brainstorm, Audit **skip this phase**.

**Quick mode:** Generate a **task list** (not a full PRD). Numbered tasks with brief descriptions. Present action path choice to user: team execution, ralf, or export. No Phase 5 — output is the sketch + task list.

**Auto mode:** Generate PRD. Auto-approve without user review. Default to **Ship** action path (Path F: export issues then implement, review, and merge).

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

### 4.1b Generate Acceptance Contract

After writing the PRD, generate a structured acceptance contract from its criteria:

1. **Read the PRD** at `$SESSION_DIR/prd.md`
2. **Extract acceptance criteria** from each user story (the `- [ ]` items under each `US-NNN`)
3. **Assign verification method** per criterion based on keywords:
   - "displays/shows/renders/UI" → `e2e-test` or `manual-check`
   - "returns/accepts/rejects/validates" → `unit-test`
   - "calls/sends/receives/integrates" → `integration-test`
   - "builds/compiles" → `build-output`
   - Default → `unit-test`
4. **Assign test location hints** based on project conventions (from context scan)
5. **Write the contract** to `$SESSION_DIR/acceptance-contract.md`:

```markdown
# Acceptance Contract: <Idea>
Session: <id> | PRD: prd.md | Status: locked

## Quality Gates
| Gate | Command | Required |
|------|---------|----------|
| build | `npm run build` | yes |
| typecheck | `npx tsc --noEmit` | yes |

## Acceptance Criteria

### US-001: <Story title>

#### AC-001: <Criterion text>
- **Method:** unit-test | integration-test | e2e-test | build-output | manual-check | metric
- **Test:** `path/to/test.ts` > "test description"
- **Status:** pending
- **Evidence:** —
- **Verified-by:** —

## Verification Summary
| ID | Criterion | Method | Status | Evidence |
|----|-----------|--------|--------|----------|
| AC-001 | <short> | unit-test | pending | — |

Progress: 0/N verified
```

6. **Create backward-compatible symlink:**
   ```bash
   ln -sf "$SESSION_DIR/acceptance-contract.md" "$WORKSPACE/.claude/prd/contract-<slug>.md"
   ```

7. **Generate BDD test stub files** from each criterion:
   - Detect project test framework (Jest, Vitest, pytest, etc.) from context scan
   - Create `describe/it` blocks with Given/When/Then structure per AC
   - Stubs throw `Not implemented — AC-NNN pending` (guarantees RED on first run)
   - Test file locations follow project conventions
   - Write stubs to `$SESSION_DIR/test-stubs/` and note paths in the contract

   **Generated stub example:**
   ```typescript
   // Generated from AC-001: User can create a new project
   describe('US-001: Project Creation', () => {
     describe('AC-001: User can create a new project', () => {
       it('GIVEN a logged-in user WHEN they submit a project name THEN a new project is created', () => {
         // TODO: Implement — this test must fail first (RED)
         throw new Error('Not implemented — AC-001 pending');
       });
     });
   });
   ```

8. **Auto-create GitHub issue** from the contract:
   ```bash
   gh issue create \
     --title "[AC] <Idea> — Acceptance Contract" \
     --label "acceptance-contract,tracking" \
     --body "$CONTRACT_BODY"
   ```
   - Body contains task-list checkboxes from contract criteria + quality gates
   - Store issue URL in contract file and session index (`contract_issue: "<url>"`)
   - During execution, update GitHub issue checkboxes via `gh api` when criteria are verified

### 4.2 Task Decomposition

Create tasks via `TaskCreate` for each user story. Set up dependencies with `TaskUpdate`.

### 4.3 Plan Summary

Write task breakdown to `$SESSION_DIR/plan.md`.

### 4.3b Scope Review (Standard / Deep mode)

Present the PRD scope to the user via `AskUserQuestion` before offering action paths:

```
PRD Scope Review

Goals:
<bulleted goals from PRD>

Non-Goals (out of scope):
<bulleted non-goals from PRD>

User Stories (<N> total):
1. US-001: <title> — <1-line description>
2. US-002: <title> — <1-line description>
...

Acceptance Contract: <N> criteria across <N> stories
Verification methods: <N> unit-test, <N> integration-test, <N> e2e-test, <N> manual-check
Contract: .claude/$THEME_ID/sessions/<session-id>/acceptance-contract.md

Does this scope match what you had in mind?
```
Options:
- **Approve** — Proceed to action path selection
- **Adjust scope** — Tell the conductor what to add, remove, or change (conductor revises prd.md, plan.md, and tasks, then re-presents)

**Auto mode:** Skip (auto-approve).
**Guided mode:** Superseded by the more thorough Guided PRD review in 4.4.

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
- **Ship (Recommended)** — Export issues, implement, review, and merge all PRs automatically via `/ship`
- **Export to GitHub Issues** — Create one issue per user story with acceptance criteria and dependencies
- **Team execution** — Assign tasks to agents
- **Ralf handoff** — PRD goes to `/ralf` for autonomous execution
- **Launch handoff** — PRD goes to `/launch` in a separate worktree
- **Deep audit** — Exhaustive multi-pass codebase audit (see [Phase 5D](#phase-5d-deep-audit))
- **Review first** — Read the PRD and design doc before deciding

**Deep mode:** Skip this touchpoint — always route to Phase 5D automatically.

**Guided mode:** Present PRD to user before offering action paths:
```
Review the PRD. Ready to proceed?
```
Options: Approve / Edit / Back (return to design)

### 4.5 Commit

```bash
git -C $WORKSPACE add .claude/$THEME_ID/ .claude/prd/
git -C $WORKSPACE commit -m "docs($THEME_ID): execution plan and PRD for <idea>"
```

Update `$SESSION_DIR/session.md` phase to `action`.
**Update index** — set `phase: "action"`, update timestamp.
Update `session-state.json` (`phase: "planning"`) and rerun the scribe so the live page shows the PRD scope and contract summary.

---

## Phase 5: Action

The path catalog below is the engineering theme's default. Themed variants may declare additional or alternative paths via `$ACTION_PATHS` (e.g., a finance theme may emit a memo + journal-entries package instead of GitHub issues). Path A (team execution) is the only mandatory path; all others are theme-opt-in.

### Path A: Team Execution

**Backend: teams-preferred.** The shared task list, dependency unblocking, file locking, and per-task plan approval are team features. Without the teams flag, the conductor executes the same `TaskCreate` dependency list sequentially: for each unblocked task, spawn a one-shot Task (`subagent_type` from the roster, `model:` council-agent tier from the routing table) with the task description + inline skill, mark it complete, and continue until the list is done. The verification sweep below is unchanged.

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

#### Verification Sweep

After all team agents complete their tasks, the conductor runs a contract verification sweep:

1. Read `$SESSION_DIR/acceptance-contract.md`
2. For each `pending` criterion: run the associated test or verification command, update status
3. For `failed` criteria: re-assign to the appropriate agent for remediation
4. Present the contract summary table to the user:

```
Acceptance Contract — Verification Summary

| ID | Criterion | Method | Status | Evidence |
|----|-----------|--------|--------|----------|
| AC-001 | <short> | unit-test | verified | test-file:line |
| AC-002 | <short> | e2e-test | failed | — |

Progress: N/M verified | F failed | P pending-manual
```

5. **Block completion** until all non-manual criteria are `verified`
6. Update the GitHub issue checkboxes via `gh api` for each verified criterion
7. Update `session-state.json` (`phase: "verification"`) and rerun the scribe

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

### Path D: Deep Audit

Read and follow [Phase 5D: Deep Audit](#phase-5d-deep-audit).

### Path E: GitHub Issues Export

Export user stories from the PRD as individual GitHub issues with acceptance criteria and dependency tracking.

1. **Read artifacts:**
   - `$SESSION_DIR/prd.md` — extract user stories, acceptance criteria, technical notes
   - `$SESSION_DIR/acceptance-contract.md` — extract verification methods and test locations

2. **Detect repo context:**
   ```bash
   REPO=$(gh repo view --json nameWithOwner -q .nameWithOwner)
   ```
   If `gh` fails, warn the user and abort: "GitHub CLI not authenticated. Run `gh auth login` first."

3. **Create milestone** (with error discrimination):
   ```bash
   MILESTONE_RESULT=$(gh api repos/$REPO/milestones --method POST -f title="$IDEA" -f state=open 2>&1)
   MILESTONE_EXIT=$?
   if [ $MILESTONE_EXIT -ne 0 ]; then
     if echo "$MILESTONE_RESULT" | grep -q "already_exists"; then
       # Duplicate — expected, proceed normally
     else
       # Real error — warn but continue
       echo "Warning: Milestone creation failed: $MILESTONE_RESULT"
     fi
   fi
   MILESTONE_NUMBER=$(gh api repos/$REPO/milestones --jq '.[] | select(.title=="'"$IDEA"'") | .number')
   ```

   **Validate milestone before proceeding:**
   ```bash
   if [ -z "$MILESTONE_NUMBER" ]; then
     echo "Error: Milestone '$IDEA' not found after creation attempt. Check repo permissions."
     # Abort — do not proceed to issue creation
     exit 1
   fi
   ```

4. **Create labels** (idempotent, best-effort):
   ```bash
   gh label create "user-story" --description "User story from council PRD" --color "0E8A16" 2>/dev/null || true
   LABEL_RESULT=$(gh label create "$THEME_ID-<session-slug>" --description "Council session: <slug>" --color "5319E7" 2>&1)
   if [ $? -ne 0 ] && ! echo "$LABEL_RESULT" | grep -q "already_exists"; then
     echo "Warning: Could not create session label — issues will be created without it"
   fi
   ```

5. **Initialize issue map** — write `$SESSION_DIR/issues.md` header before the loop:
   ```markdown
   # GitHub Issues: <Idea>
   Session: <session-id> | Milestone: <milestone-url>

   | Issue | Title | Labels | Depends On |
   |-------|-------|--------|------------|
   ```

6. **Create issues in dependency order.** For each user story (US-001, US-002, etc.):

   **Idempotency check** — before creating, search for an existing issue:
   ```bash
   EXISTING=$(gh issue list --label "$THEME_ID-<session-slug>" --search "[US-NNN]" --json number,title --jq '.[0].number // empty')
   if [ -n "$EXISTING" ]; then
     echo "Skipped [US-NNN] — already exists as #$EXISTING"
     # Record in issues.md and continue to next story
   fi
   ```

   **Create issue** (only if no existing match):
   ```bash
   gh issue create \
     --title "[US-NNN] <Story title>" \
     --label "user-story,$THEME_ID-<session-slug>" \
     --milestone "$IDEA" \
     --body "$ISSUE_BODY"
   ```

   **Append to issue map immediately** after each successful creation or skip:
   ```
   | #<N> | [US-NNN] <title> | user-story | <depends-on or —> |
   ```

   **Issue body template:**
   ```markdown
   ## User Story
   As a <user>, I want <capability> so that <benefit>.

   ## Acceptance Criteria
   - [ ] <AC-NNN>: <Criterion 1>
   - [ ] <AC-NNN>: <Criterion 2>

   ## Testing
   | Criterion | Method | Test Location |
   |-----------|--------|---------------|
   | AC-NNN | unit-test | `path/to/test.ts` |

   ## Technical Notes
   <Relevant technical notes from PRD for this story>

   ## Dependencies
   - Blocked by #<N> <!-- only if prior stories are prerequisites -->

   ---
   Tracking: <acceptance-contract-issue-url>
   Session: `<session-id>`
   ```

   Track each created issue number for dependency linking in subsequent issues.

7. **Update acceptance contract issue** — append a cross-reference section to the existing contract issue body listing all created user story issues:
   ```bash
   gh issue edit <contract-issue-number> --body "$UPDATED_BODY"
   ```

8. **Print summary** to the user:
   ```
   GitHub Issues Created — <N> issues in milestone "<Idea>"

   | # | Title | Dependencies |
   |---|-------|--------------|
   | <issue#> | [US-001] <title> | — |
   | <issue#> | [US-002] <title> | Blocked by #<N> |

   Milestone: <milestone-url>
   Acceptance Contract: <contract-issue-url>
   Issue map: $SESSION_DIR/issues.md

   Next: /ship --from-session <session-id>
   ```

### Path F: Ship (Issues to Merged PRs)

Run Path E (GitHub Issues Export) first, then automatically invoke `/ship` to implement, review, and merge all issues.

1. Execute Path E steps 1-8 (create GitHub issues with acceptance criteria and dependencies)
2. After Path E completes, invoke:
   ```
   /ship --from-session <session-slug>
   ```
   The `--from-session` flag reads `$SESSION_DIR/issues.md` for issue numbers and auto-sets `--contract` from `$SESSION_DIR/acceptance-contract.md`.

3. `/ship` handles the full pipeline: implement each issue via `/looper`, review PRs via `/pr-review-toolkit:review-pr`, fix findings autonomously, and merge in dependency order.

**Guided mode:** During team execution (Path A), add per-task approval before each agent starts work:
```
Agent X will work on: [task]. Proceed?
```
Options: Approve / Skip / Modify

---

## Phase 5D: Deep Audit

A persistent, self-healing audit system that strategically divides the codebase into audit zones, spawns specialist agents per zone, checkpoints and respawns on context limits, and iterates until convergence (zero new findings across a full pass).

**Triggered by:** Deep mode (automatic after Phase 4), Audit mode (direct after context scan), or user selecting "Deep audit" from Phase 4.4.

### 5D.1 Audit Planning

1. **Scan the codebase** to build an inventory of auditable files:
   - Use `git ls-files` to get tracked files (respects `.gitignore`)
   - Group files into **audit zones** by directory/module
   - Estimate file count and LOC per zone

2. **Define audit criteria** from the idea + interview:
   - What to look for (type conflicts, unused variables, logic errors, security, accessibility, etc.)
   - Severity levels: `critical`, `warning`, `info`
   - Scope: full codebase or specific directories

3. **Create audit artifacts:**
   ```bash
   mkdir -p $SESSION_DIR/audit/zones
   mkdir -p $SESSION_DIR/audit/checkpoints
   ```

4. **Write initial coverage map** to `$SESSION_DIR/audit/coverage.md`:
   ```markdown
   # Audit Coverage Map

   ## Audit Criteria
   - <criteria>

   ## Zones
   | Zone | Files | LOC | Status | Pass | Agent |
   |------|-------|-----|--------|------|-------|
   | src/components/ | 24 | 3200 | pending | - | - |
   ```

5. **Write audit state** to `$SESSION_DIR/audit/state.md` with: active flag, pass counter, total findings, convergence status.

6. **Write empty findings log** to `$SESSION_DIR/audit/findings.md`.

### 5D.2 Audit Execution

**Workflow backend (primary):** run the entire audit loop as a background Workflow. Read `~/.claude/skills/council/references/workflows/council-audit.template.js` and invoke the **Workflow tool** with that script verbatim, passing via `args`: `{ sessionDir, workspace, zones (from the coverage map), criteria, auditModel (audit tier from the routing table), maxPasses: 5, contextBlock }`. The script runs waves of up to 4 zone agents in parallel, a gap-detection judge between passes, loops until a pass yields zero new findings (or the pass cap / token budget is hit — noted as "budget-converged" in the report), and writes `audit/report.md`, the coverage map, the findings log, and per-zone reports — on-disk artifacts identical to the conductor-driven loop. The checkpoint system (5D.3) is **not needed** on this path; the workflow runs outside the conductor's context and is resumable in-session. On completion, continue at 5D.4 step 4 (commit + present results).

**Conductor-driven fallback (workflows unavailable):** spawn audit agents **in waves** of 2-4 zones at a time:

1. **Select zones** for this wave. Priority: `pending` > `needs-review` > previously-flagged. Skip `clean` zones.
2. **Spawn 2-4 `general-purpose` agents**, one per zone, with `model:` from the audit row of the [routing table](#cost-profiles--model-routing), audit criteria, and file list.
3. **Wait for all wave agents** to complete.
4. **Collect findings** from each zone report.
5. **Update coverage map and findings log.**
6. **Repeat** for next wave until all zones covered.

### 5D.3 Conductor Checkpoint System (fallback path only)

When approaching context limits (or after every 3 waves):

1. **Write checkpoint** to `$SESSION_DIR/audit/checkpoints/checkpoint-<N>.md` with coverage state, findings count, zones completed/remaining, and resume instructions.
2. **Print resume instructions:** `Context limit approaching. Checkpoint saved. To resume: /<command> --resume`
3. **On resume:** Read `audit/state.md`, find `active: true`, load latest checkpoint, continue spawning waves.

### 5D.4 Convergence Loop

After all zones in a pass are audited:

1. **Tally new findings** for this pass
2. **Check convergence:**
   - `new_findings_this_pass == 0` AND `pass >= 2` → **CONVERGED** — generate final report
   - `new_findings_this_pass > 0` → start next pass: reset flagged zones to `needs-review`, flag adjacent zones (import graph traversal)
3. **On convergence**, generate `$SESSION_DIR/audit/report.md`:
   - Summary (passes, findings, coverage)
   - Findings by severity (critical, warning, info)
   - Final coverage map
   - Prioritized recommendations

4. **Commit audit artifacts:**
   ```bash
   git -C $WORKSPACE add .claude/$THEME_ID/
   git -C $WORKSPACE commit -m "docs($THEME_ID): audit report — <N> findings across <N> passes"
   ```

5. **Present results** via `AskUserQuestion`:
   ```
   Audit Complete — Converged after <N> passes
   <N> total findings: <critical> critical, <warning> warnings, <info> info
   ```
   Options:
   - **Fix findings** — Spawn agents to fix issues (prioritized by severity)
   - **Review first** — Read the full report before deciding
   - **Export only** — Keep the report, end session

### 5D.5 Gap Detection (Between Passes)

Between passes, the conductor runs a gap detection sweep:
1. **Cross-reference findings** — trace callers of flagged functions
2. **Import graph traversal** — flag importing files' zones as `needs-review`
3. **Dead code detection** — find unreferenced exports
4. **Update coverage map** before starting next pass

---

## Session Management

### Session Directory Structure

```
$WORKSPACE/.claude/$THEME_ID/
  index.json                                  # Per-workspace session index
  sessions/
    <slug>-<YYYYMMDD-HHmm>/                  # Each session isolated
      session.md
      session-state.json                      # Live page state (contract item 5)
      session.html                            # Live session page (scribe output)
      render-session.py                       # Scribe copy, pinned per session
      session-page.template.html              # Template copy, pinned per session
      detail-*.md                             # Conductor detail asides
      interview-transcript.md
      interview-summary.md
      assembly.md
      deliberation/
        round1/*.md
        round2/*.md
        round3/*.md
      design.md
      design-sketch.md                        # Quick mode only
      meeting-notes.md                        # Meeting mode only
      plan.md
      prd.md
      acceptance-contract.md                # Acceptance contract (Phase 4.1b)
      test-stubs/                           # BDD test stubs generated from contract
      issues.md                             # GitHub issue map (Path E export)
      audit/                                  # Deep audit artifacts (Phase 5D)
        state.md                              # Audit loop state + pass history
        coverage.md                           # Zone coverage map
        findings.md                           # Cumulative findings log
        report.md                             # Final convergence report
        zones/                                # Per-zone audit reports by pass
        checkpoints/                          # Conductor context checkpoints
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
1. Read `$SESSION_DIR/session.md` to determine last completed phase, the session's `Profile:` (default `balanced` if absent — pre-v1.2 sessions), and `Backend:` (re-run the capability check if absent)
2. **Check for active audit:** Read `$SESSION_DIR/audit/state.md` if it exists
   - If `active: true`: Load the latest checkpoint from `audit/checkpoints/`, read `audit/coverage.md` and `audit/findings.md`, resume the audit loop from where it left off (Phase 5D continuation)
3. Read index to get session metadata
4. Resume from the next phase
5. Re-spawn agents as needed for remaining phases (use `agents` list from index)
6. If `$SESSION_DIR/session.html` exists, rerun the scribe and reopen it (contract item 3 open command); if the session predates the live page, set it up fresh per contract item 3

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

## Acceptance Contract
<full acceptance-contract.md, if exists>

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
2. **Teams backend only:** send `shutdown_request` to all remaining agents, then call `TeamDelete` to remove team resources (workflow/inline/sequential sessions have no team to clean up)
3. Update `$SESSION_DIR/session.md` with completion status
4. **Update index** — set `status: "completed"`, `phase` to final phase reached, update timestamp
5. **Update global registry** — set session status to `completed`, update workspace metadata
6. **Finalize the live page:** set `complete: true` in `session-state.json` and rerun the scribe (this drops the auto-refresh tag)

Artifacts remain in the workspace under `sessions/<session-id>/`. The session history is preserved for reference and future archival.
