# Class Promotion — Skill Growth System

Reference for the Professor during Phase 2.5 (Skill Loading). This mechanic tracks per-agent session participation and unlocks bonus skills after sufficient experience.

## Concept

In Fire Emblem, characters promote to advanced classes after gaining enough experience, unlocking new abilities. In the Academy, agents promote after 5 sessions and gain access to a bonus skill from a related department.

## Promotion Tracker

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

## Promotion Table

| Base Class | Sessions | Promoted Class | Bonus Skill Gained | Source Department |
|-----------|----------|---------------|-------------------|-------------------|
| Sage | 5 | Archsage | `performance-audit` | tuner |
| Troubadour | 5 | Valkyrie | `growth-engineering` | herald |
| Thief | 5 | Assassin | `compliance-review` | guardian |
| Knight | 5 | General | `deployment-plan` | operator |
| Pegasus Knight | 5 | Falcon Knight | `technology-radar` | scout |
| Tactician | 5 | Grandmaster | `cost-analysis` | operator |
| Cavalier | 5 | Paladin | `testing-strategy` | craftsman |
| Monk | 5 | Bishop | `documentation-plan` | chronicler |
| Armor Knight | 5 | Great Knight | `threat-model` | skeptic |
| Sniper | 5 | Marksman | `caching-strategy` | tuner |
| Dark Mage | 5 | Sorcerer | `schema-design` | architect |
| Wyvern Rider | 5 | Wyvern Lord | `device-integration` | pathfinder |
| Dancer | 5 | Star Dancer | `interaction-design` | advocate |
| Merchant | 5 | Anna | `monetization-design` | herald |
| Ballistician | 5 | War Cleric | `fleet-management` | sentinel |
| Manakete | 5 | Divine Dragon | `rag-architecture` | oracle |

## Design Rationale

Each bonus skill comes from a **complementary** department — giving the agent a cross-disciplinary capability:

- **Sage → performance-audit:** Architects who understand performance constraints design better systems
- **Thief → compliance-review:** Security experts who understand compliance find more meaningful risks
- **Knight → deployment-plan:** Quality engineers who understand deployment design better test strategies
- **Cavalier → testing-strategy:** Operators who understand testing design more reliable pipelines
- **Armor Knight → threat-model:** Compliance experts who understand threats write better controls

## Implementation by Phase

### Phase 2.3: Present Selection — Show Promoted Classes

When displaying the assembly table, use the promoted class name if the agent has been promoted:

```
| Archsage (Faculty) | — | 9 | New data model and API design needed |
```

Instead of:
```
| Sage (Faculty) | — | 9 | New data model and API design needed |
```

### Phase 2.5: Skill Loading — Bonus Skills Available

During skill loading, for each promoted agent:

1. Load their normal department skills (from `.claude/skills/council/<base-agent>/`)
2. Also make their bonus skill available for selection
3. The bonus skill is loaded from `.claude/skills/council/<source-department>/<bonus-skill>/SKILL.md`
4. The bonus skill competes for selection alongside department skills — it's not automatically loaded

Example: Archsage (promoted Sage) has these skills available:
- `codebase-context` (always loaded for Architect-equivalent)
- `schema-design` (from architect department)
- `api-design` (from architect department)
- `performance-audit` (bonus skill from tuner department)

### Promotion Announcement

When an agent is promoted for the **first time** in a session (their session count just crossed 5), the Professor announces it during skill loading:

```
Sage has been promoted to Archsage! New capability unlocked: performance analysis.
The Archsage can now evaluate performance bottlenecks alongside architectural design.
```

Only announce once — if the agent was already promoted in a previous session, skip the announcement.

### Cleanup: Update Promotion Tracker

After the session ends:

1. Load `.claude/academy/promotion-tracker.json`
2. For each participating agent:
   - Increment `sessions` count
   - If `sessions >= 5` and `promoted == false`:
     - Set `promoted = true`
     - Set `promoted_at` to today's date
     - Set `class` to promoted class name
     - Set `bonus_skill` to the skill from the promotion table
3. Write updated tracker back

## Edge Cases

- **New agent:** If an agent doesn't exist in the tracker, create an entry with `sessions: 1, promoted: false, class: <base class>, bonus_skill: null`
- **Missing tracker file:** If `.claude/academy/promotion-tracker.json` doesn't exist, create it with an empty `agents` object
- **Bonus skill already loaded:** If the bonus skill is the same as a skill already selected from the agent's department, don't load it twice
