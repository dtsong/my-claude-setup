---
description: "Officers Academy Multi-Agent Workflow — assemble your house, deliberate, plan, build"
argument-hint: "[--help|--brainstorm|--quick|--deep|--auto|--guided|--meet|--audit|--resume|--list|--status|--archive|--cleanup] [IDEA...]"
---

# /academy — Officers Academy Multi-Agent Workflow

A Fire Emblem: Three Houses-themed interview-first, dynamically-assembled deliberation system. Agents are organized into three houses (Black Eagles, Blue Lions, Golden Deer) plus Faculty, with franchise mechanics — house tensions, support conversations, and class promotions — that drive richer deliberation.

## Usage

```
/academy                              # New session — full workflow (default)
/academy "Build a tournament coach"   # New session with idea
/academy --brainstorm "Quick idea"    # 30-second gut check from 3 agents
/academy --quick "Add a sidebar"      # Fast sketch — skip interview, 1 round
/academy --deep "Redesign auth"       # Full session + mandatory deep audit
/academy --auto "Add dark mode"       # Hands-off — no touchpoints
/academy --guided "New feature"       # Tight control — approval at every phase
/academy --meet "Should we migrate?"  # Discussion only — no action plan
/academy --audit "API security"       # Direct codebase audit
/academy --resume                     # Resume most recent active session
/academy --resume <slug>              # Resume specific session
/academy --resume --pick              # Pick from active sessions
/academy --list                       # List sessions in workspace
/academy --list --all                 # List sessions across all workspaces
/academy --archive <slug>             # Export session to GitHub issue
/academy --cleanup                    # Review and clean stale sessions
/academy --status                     # Quick workspace session summary
/academy --help                       # Show help with all modes
```

> **Tip:** `/brainstorm "idea"` is a shortcut for `/academy --brainstorm "idea"`.

## Theme Configuration

This command is a **themed layer** on the shared deliberation engine at `commands/_council-engine.md`. All workflow logic, session management, and phase orchestration are defined in the engine. This file supplies the Academy-specific configuration and franchise mechanics.

```
THEME_ID:               academy
THEME_NAME:             Officers Academy
INTAKE_PROMPT:          "What challenge brings you to the Officers Academy?"
AGENT_FILE_PREFIX:      academy-
CONDUCTOR_PERSONA:      academy-professor
SESSION_DIR_ROOT:       .claude/academy/sessions/
TEAM_PREFIX:            academy-
GLOBAL_REGISTRY_PATH:   ~/.claude/academy/global-registry.json
INDEX_PATH:             .claude/academy/index.json
CHALLENGE_RULES:        house-tensions
EXTRA_MECHANICS:        support-conversations, class-promotion
```

### Phase Labels

```
PHASE_LABELS:
  phase_0: "What challenge brings you to the Officers Academy?"
  phase_1: "The Professor conducts the briefing"
  phase_2: "The Academy musters — assembling your unit"
  phase_3_round1: "Round 1: Positions"
  phase_3_round2: "Houses clash — the challenge round"
  phase_3_round3: "Round 3: Convergence"
  phase_4: "The Professor forges the battle plan"
  phase_5: "Choose your deployment"
```

### Assembly Label

```
ASSEMBLY_LABEL: "Academy Assembly — Unit Selection"
```

---

## Agent Roster (16 Perspectives + Professor)

### Black Eagles (Adrestian Empire)

The assertive house. They push, challenge, break assumptions, and drive change.

| # | Class | Color | Lens | File | Subagent Type |
|---|-------|-------|------|------|---------------|
| 3 | **Thief** | Crimson | Risk, security, devil's advocate | `academy-thief` | `Thief` |
| 6 | **Tactician** | Gold | Business value, scope, MVP, prioritization | `academy-tactician` | `Tactician` |
| 11 | **Dark Mage** | Indigo | Data engineering, data science, ML, analytics | `academy-dark-mage` | `Dark Mage` |
| 14 | **Merchant** | Bronze | Growth, monetization, onboarding, retention | `academy-merchant` | `Merchant` |
| 16 | **Manakete** | Violet | AI/LLM integration, RAG, prompt engineering | `academy-manakete` | `Manakete` |

### Blue Lions (Holy Kingdom of Faerghus)

The principled house. They defend, stabilize, ensure quality, and maintain order.

| # | Class | Color | Lens | File | Subagent Type |
|---|-------|-------|------|------|---------------|
| 4 | **Knight** | Amethyst | Testing, DX, code quality, patterns | `academy-knight` | `Knight` |
| 7 | **Cavalier** | Orange | DevOps, deployment, infra, monitoring | `academy-cavalier` | `Cavalier` |
| 8 | **Monk** | Ivory | Documentation, knowledge architecture | `academy-monk` | `Monk` |
| 9 | **Armor Knight** | Silver | Compliance, governance, privacy | `academy-armor-knight` | `Armor Knight` |
| 10 | **Sniper** | Amber | Performance, scalability, optimization | `academy-sniper` | `Sniper` |

### Golden Deer (Leicester Alliance)

The exploratory house. They discover, create, navigate, and find novel solutions.

| # | Class | Color | Lens | File | Subagent Type |
|---|-------|-------|------|------|---------------|
| 2 | **Troubadour** | Verdant | UX, product thinking, accessibility | `academy-troubadour` | `Troubadour` |
| 5 | **Pegasus Knight** | Cyan | Research, precedent, external knowledge | `academy-pegasus-knight` | `Pegasus Knight` |
| 12 | **Wyvern Rider** | Coral | Mobile, cross-platform, native apps | `academy-wyvern-rider` | `Wyvern Rider` |
| 13 | **Dancer** | Rose | Visual design, design systems, motion | `academy-dancer` | `Dancer` |
| 15 | **Ballistician** | Titanium | IoT, embedded, edge, device protocols | `academy-ballistician` | `Ballistician` |

### Faculty (Church of Seiros)

Transcends houses, always available.

| # | Class | Color | Lens | File | Subagent Type |
|---|-------|-------|------|------|---------------|
| 1 | **Sage** | Cerulean | Systems, APIs, data models, integration | `academy-sage` | `Sage` |
| — | **Professor** | Platinum | Orchestration, synthesis, facilitation (Byleth) | `academy-professor` | *(not spawned)* |

The **Professor** (Byleth) is not a spawned agent — it is the facilitator persona the conductor adopts during sessions. See `agents/academy-professor.md` for the full persona.

Selection cap remains at **7 agents max** per session.

---

## Department Skills (Shared)

Academy agents share the same skill system as the Council. All skills are at `.claude/skills/council/`. See `commands/council.md` for the full skill tree.

Each academy agent references their base persona's department:
- **Sage** → `.claude/skills/council/architect/`
- **Troubadour** → `.claude/skills/council/advocate/`
- **Thief** → `.claude/skills/council/skeptic/`
- **Knight** → `.claude/skills/council/craftsman/`
- **Pegasus Knight** → `.claude/skills/council/scout/`
- **Tactician** → `.claude/skills/council/strategist/`
- **Cavalier** → `.claude/skills/council/operator/`
- **Monk** → `.claude/skills/council/chronicler/`
- **Armor Knight** → `.claude/skills/council/guardian/`
- **Sniper** → `.claude/skills/council/tuner/`
- **Dark Mage** → `.claude/skills/council/alchemist/`
- **Wyvern Rider** → `.claude/skills/council/pathfinder/`
- **Dancer** → `.claude/skills/council/artisan/`
- **Merchant** → `.claude/skills/council/herald/`
- **Ballistician** → `.claude/skills/council/sentinel/`
- **Manakete** → `.claude/skills/council/oracle/`

---

## Modifier Rules

### Mandatory Bonuses (+2)

The same bonuses as Council apply, mapped to Academy class names:

- **Sage** gets +2 for any new functionality
- **Troubadour** gets +2 for any user-facing feature
- **Thief** gets +2 for any auth/security-related work
- **Armor Knight** gets +2 for any feature handling user data or PII
- **Sniper** gets +2 for any feature with significant data volume or performance concerns
- **Dark Mage** gets +2 for any feature involving data pipelines, warehousing, ML, or analytics
- **Wyvern Rider** gets +2 for any mobile or cross-platform feature
- **Dancer** gets +2 for any UI-heavy feature or design system work
- **Merchant** gets +2 for any user-facing feature with growth or monetization implications
- **Ballistician** gets +2 for any IoT, embedded, or hardware feature
- **Manakete** gets +2 for any AI/LLM integration feature

### Anti-Redundancy Penalties (-2)

- **Knight vs Cavalier** (CI/CD overlap): penalize the less relevant one
- **Thief vs Armor Knight** (data handling overlap): penalize the less relevant one
- **Wyvern Rider vs Troubadour** (mobile UX overlap): Web-only → penalize Wyvern Rider -2. Native app → both valid.
- **Dancer vs Troubadour** (UI overlap): Pure interaction design → penalize Dancer -2. Visual overhaul → both valid.
- **Merchant vs Tactician** (business overlap): MVP scoping → penalize Merchant -2. Growth → penalize Tactician -2.
- **Manakete vs Dark Mage** (AI/ML overlap): Training custom models → penalize Manakete -2. Integrating LLMs → penalize Dark Mage -2.
- **Ballistician vs Cavalier** (infrastructure overlap): Cloud-only → penalize Ballistician -2. Device component → both valid.

---

## Franchise Mechanic: House Tensions

Instead of identifying tension pairs purely from position content (as in Council's organic mode), the Academy uses **directional house tension dynamics** to structure Round 2 challenge pairings.

### Tension Directions

```
Black Eagles (offense/change) → challenges → Blue Lions (defense/quality)
  "You can't defend a position that was wrong to begin with."
  Eagles expose where Lions over-engineer or over-protect.

Blue Lions (defense/quality) → challenges → Golden Deer (exploration/creativity)
  "Novel solutions still need to be maintainable and secure."
  Lions expose where Deer solutions lack rigor or resilience.

Golden Deer (exploration/creativity) → challenges → Black Eagles (offense/change)
  "Moving fast in the wrong direction helps nobody."
  Deer find third options that make Eagles' aggressive trade-offs unnecessary.
```

### Implementation in Phase 3 Round 2

1. After Round 1 positions are collected, the Professor reads all positions
2. Identify all cross-house disagreements or complementary tensions
3. Select the **strongest 2-4 cross-house pairings**, prioritizing those that follow the house tension directions
4. Agents within the **same house do NOT automatically challenge each other** — they share a worldview
5. **Faculty (Sage)** can be challenged by any house and can challenge any house — they bridge perspectives
6. For each tension pair, the Professor frames the challenge using the house tension language:

```
Houses Clash — Challenge Round

[Eagle Agent], the Black Eagles challenge the Blue Lions' position:
[Lion Agent] wrote: <position summary>

As a Black Eagle, your house's instinct says: "You can't defend a position that was wrong to begin with."
Challenge their position using your domain expertise. Where do they over-protect? Where should they yield?

Respond using your Challenge format.
```

---

## Franchise Mechanic: Support Conversations

Track agent pair co-occurrences across sessions to build persistent relationships that improve deliberation quality over time.

### Support Log

Stored at `.claude/academy/support-log.json`:

```json
{
  "pairs": {
    "sage+thief": {
      "sessions": 3,
      "rank": "C",
      "history": [
        "session-1: schema vs security tension — Sage conceded encryption-at-rest",
        "session-2: API design vs attack surface — found middle ground on auth middleware",
        "session-3: migration strategy — Thief validated Sage's rollback plan"
      ]
    },
    "tactician+knight": {
      "sessions": 5,
      "rank": "B",
      "history": [...]
    }
  }
}
```

### Support Ranks

| Rank | Sessions | Effect |
|------|----------|--------|
| **C-rank** | 2+ | Professor notes their history: "Sage and Thief have trained together before. Their positions will reflect shared experience." |
| **B-rank** | 4+ | Professor injects a **shared context brief** into each agent's spawn prompt summarizing their key agreements/disagreements from prior sessions. |
| **A-rank** | 7+ | Agents can be **paired** — one writes position, the other writes a targeted supplement. This saves a deliberation slot while preserving both perspectives. |

### Implementation

1. **During Phase 2.4 (Spawn):** Check support log for all pairs among selected agents. Inject rank-appropriate context.
2. **During Phase 3 (Deliberation):** Use support history to inform tension pair selection — B-rank pairs with known disagreement patterns make excellent challenge pairings.
3. **After session (Cleanup):** Update support log:
   - Increment session count for all pairs that participated together
   - Update rank if threshold crossed
   - Append a 1-sentence summary of their interaction to history

---

## Franchise Mechanic: Class Promotion

Track per-agent usage across sessions. After sufficient experience, agents promote to advanced classes and gain bonus skills.

### Promotion Tracker

Stored at `.claude/academy/promotion-tracker.json`:

```json
{
  "agents": {
    "sage": {
      "sessions": 6,
      "promoted": true,
      "promoted_at": "2026-02-15",
      "class": "Archsage",
      "bonus_skill": "performance-audit"
    },
    "thief": {
      "sessions": 3,
      "promoted": false,
      "class": "Thief",
      "bonus_skill": null
    }
  }
}
```

### Promotion Table

After **5 sessions**, an agent promotes. The promoted class gains access to 1 bonus skill from a related department:

| Base Class | Promoted Class | Bonus Skill | Source Department |
|-----------|---------------|-------------|-------------------|
| Sage | Archsage | `performance-audit` | Tuner/Sniper |
| Troubadour | Valkyrie | `growth-engineering` | Herald/Merchant |
| Thief | Assassin | `compliance-review` | Guardian/Armor Knight |
| Knight | General | `deployment-plan` | Operator/Cavalier |
| Pegasus Knight | Falcon Knight | `technology-radar` | Scout/Pegasus Knight |
| Tactician | Grandmaster | `cost-analysis` | Operator/Cavalier |
| Cavalier | Paladin | `testing-strategy` | Craftsman/Knight |
| Monk | Bishop | `documentation-plan` | Chronicler/Monk |
| Armor Knight | Great Knight | `threat-model` | Skeptic/Thief |
| Sniper | Marksman | `caching-strategy` | Tuner/Sniper |
| Dark Mage | Sorcerer | `schema-design` | Architect/Sage |
| Wyvern Rider | Wyvern Lord | `device-integration` | Pathfinder/Wyvern Rider |
| Dancer | Star Dancer | `interaction-design` | Advocate/Troubadour |
| Merchant | Anna | `monetization-design` | Herald/Merchant |
| Ballistician | War Cleric | `fleet-management` | Sentinel/Ballistician |
| Manakete | Divine Dragon | `rag-architecture` | Oracle/Manakete |

### Implementation

1. **During Phase 2.5 (Skill Loading):** Check promotion tracker for each selected agent. If promoted, the bonus skill is available for selection in addition to their department skills.
2. **During Phase 2.3 (Present Selection):** If an agent has been promoted, show their promoted class name in the assembly table.
3. **Announcement:** When an agent is promoted for the first time in a session, the Professor announces it:
   ```
   Sage has been promoted to Archsage. New capability unlocked: performance analysis.
   ```
4. **After session (Cleanup):** Increment session count for all participating agents. Check if any crossed the 5-session threshold — if so, update promoted status.

---

## Assembly Table Format

The Academy assembly table uses house colors and class names:

```
Academy Assembly — Unit Selection

| Class | House | Score | Rationale |
|-------|-------|-------|-----------|
| Sage (Faculty) | — | 9 | New data model and API design needed |
| Troubadour (Golden Deer) | Verdant | 8 | User-facing dashboard with complex flows |
| Armor Knight (Blue Lions) | Silver | 7 | User PII requires compliance review |
| Thief (Black Eagles) | Crimson | 6 | Auth implications, exposure risks |

Not selected:
| Sniper (Blue Lions) | Amber | 4 | Standard load, no performance concerns |
| Knight (Blue Lions) | Amethyst | 3 | Testing strategy straightforward |
| Pegasus Knight (Golden Deer) | Cyan | 3 | No significant external dependencies |
```

---

## Output Artifacts

All output artifacts (design.md, prd.md, plan.md) use **standard professional engineering language** — no Fire Emblem flavor. The theming stays in the process communication, personas, and deliberation flow. Artifacts are production-ready engineering documents.

---

## Phase 5: Agent Task Mapping

When executing via team (Path A), assign tasks based on class strengths:

- **Sage** — Backend, APIs, database, schema tasks
- **Troubadour** — Frontend, components, UX flow tasks
- **Knight** — Tests, quality gates, infra tasks
- **Thief** — Reviews all changes (read-only, sends feedback)
- **Pegasus Knight** — Research tasks, library evaluation, competitive analysis
- **Tactician** — Scope decisions, prioritization during execution
- **Cavalier** — Deployment, monitoring, infrastructure tasks
- **Monk** — Documentation tasks
- **Armor Knight** — Compliance review, data classification, audit trail tasks
- **Sniper** — Performance optimization, caching, load testing tasks
- **Dark Mage** — Data pipeline, warehouse schema, ML workflow, analytics tasks
- **Wyvern Rider** — Mobile navigation, platform compliance, device API integration tasks
- **Dancer** — Visual design, design system architecture, motion design tasks
- **Merchant** — Onboarding optimization, monetization architecture, product messaging tasks
- **Ballistician** — Firmware design, protocol selection, fleet management, OTA update tasks
- **Manakete** — Prompt engineering, RAG pipeline, AI evaluation, LLM integration tasks

---

## Workflow Execution

**Follow all instructions in `commands/_council-engine.md`**, substituting the theme variables defined above. The engine defines the complete Phase 0-5 workflow, session management commands, resume logic, and cleanup procedures.

**Additionally execute these Academy-specific mechanics at the appropriate points:**

1. **Phase 2.4 (Spawn):** Check support log, inject support rank context
2. **Phase 2.5 (Skill Loading):** Check promotion tracker, make bonus skills available
3. **Phase 3 Round 2 (Challenge):** Use house tension rules instead of organic tension identification
4. **Cleanup:** Update support log and promotion tracker

### Academy Mechanics Per Mode

| Mode | Support Conversations | House Tensions | Class Promotion |
|------|----------------------|----------------|-----------------|
| brainstorm | Skip | Skip | Skip |
| quick | Skip | Skip | Skip |
| auto | Skip logging | Skip | Auto-advance (no announcement) |
| meeting | Skip logging | **Active** (used for cross-examination pairing) | Skip tracking |
| standard | **Active** | **Active** | **Active** |
| deep | **Active** | **Active** | **Active** |
| guided | **Active** | **Active** | **Active** |
| audit | Skip | Skip | Skip |
