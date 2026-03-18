# Skill-Level Model Routing & Token Budget Management Specification v1.0

## The Problem

Right now model selection happens at two extremes: either the user manually
picks a model for their entire session, or a routing system makes a global
decision per message. Neither is granular enough for skills.

Consider a frontend QA skill suite:
- **page-component-mapper**: Traces imports, reads file headers, builds a tree.
  This is mechanical work — Haiku handles it perfectly at 1/60th the cost of Opus.
- **css-layout-debugger**: Classifies layout issues, checks Tailwind configs,
  traces cascade. Analytical — Sonnet is the right fit.
- **ui-bug-investigator**: Reasons about state management bugs, hydration
  mismatches, race conditions. This genuinely needs Opus-level reasoning.

Without skill-level routing, the entire suite runs on whatever model the session
is using — usually Opus because that's what the user selected for the complex
task that triggered the suite. The mechanical tracing step burns Opus tokens
for work Haiku would do identically.

The second problem is budget awareness. Users hit weekly Opus limits and then
face a hard cliff — either wait or manually downgrade everything. Skills should
be able to degrade gracefully, routing to the best available model rather than
failing or burning premium capacity on tasks that don't need it.

---

## 1. Skill-Level Model Configuration

### 1.1 The `model` Frontmatter Block

Extend the SKILL.md frontmatter with a `model` configuration block:

```yaml
---
name: page-component-mapper
description: ...
model:
  # What this skill ideally wants
  preferred: haiku
  # What it can tolerate without quality loss
  acceptable: [haiku, sonnet]
  # The absolute minimum — quality may degrade below this
  minimum: haiku
  # Whether the user can override the preferred model upward
  allow_upgrade: true
  # Whether the system can downgrade below preferred under budget pressure
  allow_downgrade: true
  # Task-specific context for routing decisions
  reasoning_demand: low        # low | medium | high | variable
---
```

```yaml
---
name: ui-bug-investigator
description: ...
model:
  preferred: opus
  acceptable: [opus, sonnet]
  minimum: sonnet
  allow_upgrade: true
  allow_downgrade: true
  reasoning_demand: high
  # Optional: conditions that change the preferred model
  conditions:
    - when: "issue is a known pattern (exact CSS property fix, missing import)"
      downgrade_to: sonnet
    - when: "issue involves state management, hydration, or race conditions"
      hold_at: opus
---
```

### 1.2 Model Tier Definitions

Map abstract tiers to concrete models per platform:

```yaml
# pipeline/config/model-routing.yaml

tiers:
  haiku:
    claude_code: claude-haiku-4-5
    codex: codex-spark
    description: "Mechanical tasks — file tracing, pattern matching, formatting"
    cost_ratio: 1          # Baseline

  sonnet:
    claude_code: claude-sonnet-4-6
    codex: gpt-5.3-codex
    description: "Analytical tasks — classification, multi-factor decisions, standard coding"
    cost_ratio: 5          # ~5x haiku (Sonnet 4.6: $3/$15 per MTok)

  opus:
    claude_code: claude-opus-4-6
    codex: gpt-5.3-codex-xl    # hypothetical — map to best available
    description: "Adversarial security analysis, formal verification, vulnerability chain synthesis"
    cost_ratio: 25         # ~25x haiku (Opus: $15/$75 per MTok)

# Session defaults
defaults:
  coordinator: haiku       # Coordinators route, they don't reason
  specialist: sonnet       # Reasonable default for most specialist work
  reference_loading: haiku # Reading reference files is mechanical
```

### 1.3 Precedence Rules

When multiple signals suggest different models, resolve in this order:

1. **User explicit override** — "Use Opus for this" always wins
2. **Skill minimum** — Never go below the skill's declared minimum
3. **Budget constraint** — If the preferred model is unavailable due to limits,
   downgrade within the acceptable range
4. **Skill preferred** — Use the skill's preferred model when available
5. **Session default** — Fall back to the session-level model setting
6. **Platform default** — Fall back to the platform's default model

---

## 2. Dynamic Budget-Aware Routing

### 2.1 Budget Dimensions

Token budgets exist at multiple levels. The routing system should be aware of
all of them and degrade gracefully across each:

| Dimension | Scope | Signal Source | Typical Constraint |
|-----------|-------|---------------|--------------------|
| **Context window** | Single message | Token count in context | ~200K tokens (model-dependent) |
| **Session** | Current conversation | Cumulative tokens in this session | Varies by plan |
| **Daily** | Calendar day | Tokens consumed today across all sessions | Rate limits |
| **Weekly** | Rolling 7 days | Tokens consumed this week | Plan-level caps (especially Opus) |
| **Monthly** | Billing period | Total spend across all models | Cost budget |

### 2.2 Budget Zones

Define three zones that trigger different routing behaviors:

```
┌─────────────────────────────────────────────────┐
│  GREEN ZONE (0-70% of budget consumed)          │
│  Use preferred models for all skills.           │
│  No degradation.                                │
├─────────────────────────────────────────────────┤
│  YELLOW ZONE (70-90% of budget consumed)        │
│  Downgrade skills where allow_downgrade: true   │
│  and reasoning_demand is low or medium.         │
│  Hold opus for high reasoning_demand skills.    │
│  Notify user of budget status.                  │
├─────────────────────────────────────────────────┤
│  RED ZONE (90-100% of budget consumed)          │
│  Downgrade all skills to minimum tier.          │
│  Notify user with options to continue or stop.  │
│  If minimum is opus and opus is exhausted,      │
│  warn that quality may degrade and offer sonnet.│
└─────────────────────────────────────────────────┘
```

### 2.3 Degradation Cascade

When budget pressure forces a downgrade, apply this cascade:

```
Step 1: Downgrade coordinators to haiku (if not already)
        → Coordinators only route, haiku is sufficient
        → Saves: significant if coordinator was running on sonnet/opus

Step 2: Downgrade low reasoning_demand specialists to haiku
        → Mechanical tasks: file tracing, pattern matching, counting
        → Savings: ~8x per task vs sonnet, ~60x vs opus

Step 3: Downgrade medium reasoning_demand specialists to sonnet
        → Analytical tasks: classification, code review, standard fixes
        → Quality impact: minimal for well-structured skills

Step 4: Offer to downgrade high reasoning_demand specialists to sonnet
        → Complex debugging, architecture decisions
        → Quality impact: noticeable — notify user
        → User decides: accept degradation or pause until budget resets

Step 5: If all models at minimum and budget exhausted
        → Present options: wait for reset, switch to free tier, export context
```

### 2.4 Budget Estimation

Before executing a skill, estimate its token cost to make informed routing:

```yaml
# In SKILL.md frontmatter (optional but recommended)
model:
  preferred: sonnet
  estimated_tokens:
    input: 2000-5000      # Context sent to model
    output: 500-1500      # Expected response size
    tool_calls: 3-8       # Number of tool invocations
    total_estimate: 8000-25000  # End-to-end for a typical run
```

This lets the routing system calculate: "This skill typically costs ~15K tokens.
At sonnet pricing that's X. At haiku it's Y. We have Z budget remaining."

---

## 3. User Configuration Knobs

### 3.1 Session-Level Overrides

Users should be able to set routing preferences for their current session:

```yaml
# .claude/session-config.yaml (or equivalent runtime config)

model_routing:
  # Override all skills to a specific model
  force_model: null            # null = use skill preferences, or haiku/sonnet/opus

  # Budget conservation mode
  conservation_mode: auto      # off | auto | aggressive
  # off: always use preferred models
  # auto: degrade in yellow/red zones
  # aggressive: use minimum viable model for everything

  # Per-skill overrides for this session
  skill_overrides:
    page-component-mapper: sonnet   # "I want higher quality mapping today"
    ui-bug-investigator: sonnet     # "I'm okay with sonnet for debugging today"

  # Budget thresholds (override defaults)
  yellow_zone_threshold: 0.70
  red_zone_threshold: 0.90
```

### 3.2 Project-Level Defaults

Set routing defaults for a project in `CLAUDE.md` / `AGENTS.md`:

```markdown
## Model Routing Defaults

Default conservation mode: auto
Default specialist model: sonnet
Override: ui-bug-investigator always uses opus (complex codebase)
Override: page-component-mapper always uses haiku (pure tracing)
```

Or in a structured config file:

```yaml
# .claude/model-routing.yaml

defaults:
  conservation_mode: auto
  specialist: sonnet

overrides:
  ui-bug-investigator:
    preferred: opus
    minimum: sonnet
    reason: "Complex state management patterns in this codebase require deep reasoning"

  page-component-mapper:
    preferred: haiku
    minimum: haiku
    reason: "Pure import tracing, no reasoning required"
```

### 3.3 Inline Overrides

Users should be able to override model selection in their prompt:

```
"Debug this hydration issue using sonnet"
→ Overrides ui-bug-investigator's preferred: opus to sonnet

"Map this page's components — use opus for thorough analysis"
→ Overrides page-component-mapper's preferred: haiku to opus

"Run everything on haiku — I'm conserving budget"
→ Sets force_model: haiku for this request
```

The skill's `minimum` field still applies unless the user explicitly says
"ignore minimum" — which should trigger a quality warning.

---

## 4. Coordinator-Level Routing

### 4.1 The Coordinator as Router

Coordinators are already the entry point for skill suites. They're the natural
place to make model routing decisions because they see the full request before
dispatching to a specialist.

Updated coordinator template:

```markdown
---
name: frontend-qa-coordinator
description: ...
model:
  preferred: haiku
  minimum: haiku
  reasoning_demand: low
---

# Frontend QA Coordinator

## Purpose
Route frontend QA requests to the appropriate specialist skill at the
appropriate model tier.

## Routing Table

| Skill | Path | Default Tier | Upgrade Trigger | Downgrade Floor |
|-------|------|-------------|-----------------|-----------------|
| page-component-mapper | skills/page-component-mapper/ | haiku | Complex dynamic imports → sonnet | haiku |
| css-layout-debugger | skills/css-layout-debugger/ | sonnet | Animation/transition issues → opus | haiku |
| ui-bug-investigator | skills/ui-bug-investigator/ | opus | Known pattern match → sonnet | sonnet |
| component-fix-and-verify | skills/component-fix-and-verify/ | sonnet | Multi-file fix → opus | haiku |
| regression-test-generator | skills/regression-test-generator/ | sonnet | Complex interaction test → opus | haiku |

## Model Selection Procedure

Step 1: Classify the request → identify the target specialist skill.

Step 2: Check the routing table for the default tier.

Step 3: Evaluate upgrade/downgrade triggers:
  - If the request matches an upgrade trigger → use the upgraded tier
  - If budget is in yellow zone and skill allows downgrade → use downgrade floor
  - If budget is in red zone → use downgrade floor for all skills
  - If user specified a model → use that model (respecting minimum)

Step 4: Load the specialist SKILL.md and execute at the selected tier.

Step 5: Pass the selected model tier to the specialist in the handoff:
  `{"model_tier": "sonnet", "reason": "budget conservation — yellow zone"}`
```

### 4.2 Sub-Task Routing Within a Specialist

Some specialists have internal steps that vary in reasoning demand. The skill
can specify per-step model preferences:

```markdown
## Procedure

Step 1: Scan all files in the target directory for component declarations.
  Model: haiku (mechanical file scanning)
  - Use `grep -rn "export.*function\|export.*const" --include="*.tsx"`
  - Record component names and file paths

Step 2: Classify each component as server or client.
  Model: sonnet (requires reading file content and making a judgment)
  - Read first 10 lines of each file
  - Check for "use client" directive, client-only hooks, browser APIs

Step 3: Analyze component relationships and identify potential issues.
  Model: opus (requires reasoning about interactions)
  - Trace prop drilling chains
  - Identify circular dependencies
  - Flag server/client boundary violations
```

This is aspirational — current platforms don't support mid-skill model switching.
But structuring skills this way prepares for it and makes the reasoning demand
explicit for when platforms do support it.

---

## 5. Observability and Reporting

### 5.1 Per-Skill Token Tracking

Every skill execution should log:

```json
{
  "skill": "page-component-mapper",
  "model_requested": "haiku",
  "model_used": "haiku",
  "downgrade_reason": null,
  "tokens": {
    "input": 3200,
    "output": 850,
    "tool_calls": 5,
    "total": 8400
  },
  "cost_estimate": {
    "actual_model": 0.002,
    "if_sonnet": 0.016,
    "if_opus": 0.12,
    "savings_vs_opus": "98.3%"
  },
  "budget_status": {
    "zone": "green",
    "weekly_consumed_pct": 0.45,
    "session_consumed_pct": 0.12
  },
  "timestamp": "2026-02-14T15:30:00Z"
}
```

### 5.2 Session Summary

At the end of a session (or on demand), generate a routing summary:

```
Session Token Summary
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Skill                      Model    Tokens    Cost
──────────────────────────────────────────────────
frontend-qa-coordinator    haiku     1,200    $0.001
page-component-mapper      haiku     8,400    $0.002
css-layout-debugger        sonnet   12,300    $0.024
ui-bug-investigator        opus     45,600    $0.520
component-fix-and-verify   sonnet   18,900    $0.038
regression-test-generator  sonnet   15,200    $0.030
──────────────────────────────────────────────────
Total                              101,600    $0.615

Routing savings:
  If all opus:  $1.82  → actual: $0.615 → saved: 66.2%
  If all sonnet: $0.20  → actual: $0.615 → opus premium: $0.42

Budget status:
  Weekly opus: 45% consumed (green zone)
  Session: 12% of daily allocation
```

### 5.3 Routing Decision Audit

Log why each routing decision was made for debugging:

```
[ROUTE] ui-bug-investigator
  Preferred: opus
  User override: none
  Budget zone: green
  Upgrade triggers: none matched
  Downgrade triggers: none (green zone)
  → Decision: opus (preferred model, budget available)

[ROUTE] page-component-mapper
  Preferred: haiku
  User override: none
  Budget zone: yellow (weekly opus at 78%)
  → Decision: haiku (preferred model, no downgrade needed)

[ROUTE] css-layout-debugger
  Preferred: sonnet
  User override: "use haiku for everything"
  Skill minimum: haiku
  → Decision: haiku (user override, above minimum)
```

---

## 6. Cost Optimization Patterns

### 6.1 Cascade Execution Pattern

For tasks with uncertain complexity, start cheap and escalate:

```markdown
## Procedure

Step 1: Quick classification (haiku).
  - Read the error message and first 20 lines of the target file
  - Classify: KNOWN_PATTERN | NEEDS_ANALYSIS | COMPLEX

Step 2: Route by classification.
  - If KNOWN_PATTERN → apply the fix directly (haiku). Skip to Step 4.
  - If NEEDS_ANALYSIS → continue to Step 3 at sonnet.
  - If COMPLEX → continue to Step 3 at opus.

Step 3: Deep analysis (sonnet or opus per Step 2).
  - Full diagnostic procedure
  - Root cause identification

Step 4: Verify fix (haiku).
  - Run targeted tests
  - Confirm the issue is resolved
```

This pattern means simple bugs cost ~$0.002 (two haiku calls) while complex
bugs cost ~$0.53 (haiku + opus + haiku). Without the cascade, every bug
costs the opus price.

### 6.2 Pre-Screening Pattern

Use a cheap model to decide if the expensive model is needed:

```markdown
Step 1: Pre-screen with haiku.
  - Read the component file
  - Check: Does it use state? Does it have effects? Does it cross server/client boundary?
  - If all "no" → this is a simple presentational component, handle at haiku
  - If any "yes" → escalate to sonnet or opus based on complexity signals
```

### 6.3 Batch Mechanical Work Pattern

Accumulate mechanical tasks and run them in a single cheap-model call:

```markdown
Step 1: Collect all files to analyze (haiku).
  - List all .tsx files in the target directory
  - Read first 5 lines of each to check for "use client"

Step 2: Batch the results into a single analytical call (sonnet).
  - Pass the collected file metadata as structured input
  - Classify all components in one call rather than file-by-file
```

### 6.4 Context Compression for Downgrades

When a skill normally runs on opus but is downgraded to sonnet under budget
pressure, compensate by providing more structured context:

```markdown
## Degradation Adaptations

When running at sonnet instead of opus:
- Include explicit diagnostic checklist (opus infers, sonnet benefits from guidance)
- Provide 2-3 examples of similar past issues and their root causes
- Break complex reasoning into smaller, sequential steps
- Add verification checkpoints between reasoning steps

When running at haiku instead of sonnet:
- Reduce to pure mechanical instructions (no judgment calls)
- Provide exact patterns to match rather than descriptions
- Use scripts for any logic that requires multi-step reasoning
- Limit output to structured data only (no prose analysis)
```

This is a key insight: **the same skill can produce good results at a lower
model tier if the instructions compensate for the model's reduced capability.**
More structured instructions + smaller steps + explicit examples bridge the gap.

---

## 7. Integration Points

### 7.1 Frontmatter Schema Update

Add to the governance spec's §3.1 (SKILL.md Frontmatter):

```yaml
# New optional fields
model:
  preferred: haiku|sonnet|opus     # Default model for this skill
  acceptable: [list]               # Models that produce acceptable results
  minimum: haiku|sonnet|opus       # Lowest model that works
  allow_upgrade: bool              # Can user request a higher model?
  allow_downgrade: bool            # Can system downgrade under budget pressure?
  reasoning_demand: low|medium|high|variable
  estimated_tokens:                # Optional execution cost estimate
    input: range
    output: range
    tool_calls: range
    total_estimate: range
  conditions:                      # Optional upgrade/downgrade triggers
    - when: "description"
      downgrade_to: tier
    - when: "description"
      hold_at: tier
```

### 7.2 Frontmatter Validation Update

The `check_frontmatter.py` hook should validate:

- `preferred` is one of: haiku, sonnet, opus
- `acceptable` is a list containing `preferred`
- `minimum` is ≤ `preferred` in tier order (haiku < sonnet < opus)
- `reasoning_demand` is one of: low, medium, high, variable
- `conditions` entries have `when` + either `downgrade_to` or `hold_at`

Validation failures are **Warn** tier — model config is optional and advisory.

### 7.3 Coordinator Template Update

Add the routing table and model selection procedure to the coordinator template
in `pipeline/templates/skill-suite/SKILL.md`.

### 7.4 Observability Integration

The per-skill token log format (§5.1) integrates with existing observability:

- **Langfuse**: Add `model_requested`, `model_used`, `downgrade_reason` as
  span attributes on each skill execution trace
- **Jaeger**: Add `budget_zone` and `routing_decision` tags to spans
- **Custom dashboard**: Aggregate savings_vs_opus across sessions for ROI tracking

### 7.5 Budget Configuration

```yaml
# pipeline/config/model-routing.yaml

tiers:
  haiku:
    claude_code: claude-haiku-4-5
    cost_ratio: 1
  sonnet:
    claude_code: claude-sonnet-4-6
    cost_ratio: 5
  opus:
    claude_code: claude-opus-4-6
    cost_ratio: 25

budget_zones:
  yellow_threshold: 0.70
  red_threshold: 0.90

defaults:
  coordinator: haiku
  specialist: sonnet
  reference_loading: haiku
  conservation_mode: auto    # off | auto | aggressive

# Weekly budget allocation (for tracking, not hard enforcement)
weekly_budget:
  opus_messages: 45          # Approximate weekly Opus message limit
  opus_tokens: null          # Or specify token budget if known
  total_spend: null          # Or specify dollar budget
```

---

## 8. Implementation Phases

### Phase 1: Static Configuration (Immediate)

What you can do now with existing platforms:

- Add `model` block to SKILL.md frontmatter for documentation
- Add routing table to coordinator skills
- Update `check_frontmatter.py` to validate model config
- Add `model-routing.yaml` to pipeline config
- Document per-skill model recommendations

This phase is pure metadata — it doesn't change execution but establishes
the routing decisions and makes them reviewable.

### Phase 2: Manual Routing (Claude Code Today)

Claude Code supports model selection per-message. Use the coordinator to
recommend (but not enforce) model routing:

- Coordinator reads the skill's `model.preferred` and includes it in the
  handoff message: "Execute this skill. Recommended model: haiku."
- The agent or user selects the model accordingly
- Log the recommendation vs actual usage for tracking

### Phase 3: Budget-Aware Routing (Requires Platform Support)

When platforms support per-tool-call model selection:

- Implement the budget zone system
- Implement the degradation cascade
- Add session-level override config
- Generate session summaries

### Phase 4: Adaptive Routing (Requires Eval Integration)

Use eval results to refine routing decisions:

- Run each skill's eval cases at each model tier
- Record pass rates per tier
- Automatically set `minimum` based on the lowest tier that passes all must-pass cases
- Update `preferred` based on cost/quality tradeoff

---

## Appendix A: Model Routing Quick Reference

```
┌──────────────────────────────────────────────────────────┐
│         MODEL ROUTING QUICK REFERENCE                    │
├──────────────────────────────────────────────────────────┤
│                                                           │
│  TIER DEFAULTS                                            │
│  Coordinator .............. haiku (routing only)          │
│  Mechanical specialist .... haiku (tracing, matching)     │
│  Analytical specialist .... sonnet (classification, code) │
│  Reasoning specialist ..... opus (adversarial, formal)    │
│                                                           │
│  COST RATIOS                                              │
│  haiku = 1x  |  sonnet = ~5x  |  opus = ~25x             │
│                                                           │
│  BUDGET ZONES                                             │
│  Green (0-70%) ..... use preferred models                 │
│  Yellow (70-90%) ... downgrade low/medium demand skills   │
│  Red (90-100%) ..... downgrade all to minimum             │
│                                                           │
│  DEGRADATION ORDER                                        │
│  1. Coordinators → haiku                                  │
│  2. Low-demand specialists → haiku                        │
│  3. Medium-demand specialists → sonnet                    │
│  4. High-demand specialists → offer downgrade to user     │
│                                                           │
│  OVERRIDE PRECEDENCE                                      │
│  User explicit > Skill minimum > Budget > Skill preferred │
│  > Session default > Platform default                     │
│                                                           │
│  OPTIMIZATION PATTERNS                                    │
│  Cascade: cheap classification → escalate if needed       │
│  Pre-screen: haiku decides if opus is necessary           │
│  Batch: accumulate mechanical work for one cheap call     │
│  Compensate: more structure when downgrading models       │
│                                                           │
└──────────────────────────────────────────────────────────┘
```
