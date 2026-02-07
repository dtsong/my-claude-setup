# Officers Academy — Skill System

The Officers Academy is a Fire Emblem: Three Houses-themed variant of the Council deliberation system. It uses the **same shared engineering skills** as the Council (at `.claude/skills/council/`) but adds three franchise mechanics that enhance deliberation quality.

## House Structure

Agents are organized into three houses plus Faculty:

### Black Eagles (Adrestian Empire) — The Assertive House
Push, challenge, break assumptions, drive change.

| Class | Base Persona | Color | Department |
|-------|-------------|-------|------------|
| Thief | Skeptic | Crimson | `skeptic/` |
| Tactician | Strategist | Gold | `strategist/` |
| Dark Mage | Alchemist | Indigo | `alchemist/` |
| Merchant | Herald | Bronze | `herald/` |
| Manakete | Oracle | Violet | `oracle/` |

### Blue Lions (Holy Kingdom of Faerghus) — The Principled House
Defend, stabilize, ensure quality, maintain order.

| Class | Base Persona | Color | Department |
|-------|-------------|-------|------------|
| Knight | Craftsman | Amethyst | `craftsman/` |
| Cavalier | Operator | Orange | `operator/` |
| Monk | Chronicler | Ivory | `chronicler/` |
| Armor Knight | Guardian | Silver | `guardian/` |
| Sniper | Tuner | Amber | `tuner/` |

### Golden Deer (Leicester Alliance) — The Exploratory House
Discover, create, navigate, find novel solutions.

| Class | Base Persona | Color | Department |
|-------|-------------|-------|------------|
| Troubadour | Advocate | Verdant | `advocate/` |
| Pegasus Knight | Scout | Cyan | `scout/` |
| Wyvern Rider | Pathfinder | Coral | `pathfinder/` |
| Dancer | Artisan | Rose | `artisan/` |
| Ballistician | Sentinel | Titanium | `sentinel/` |

### Faculty (Church of Seiros) — Transcends Houses
| Class | Base Persona | Color | Department |
|-------|-------------|-------|------------|
| Sage | Architect | Cerulean | `architect/` |
| Professor | Steward | Platinum | *(conductor)* |

## Shared Skills

All 48 engineering skills are shared from `.claude/skills/council/`. No duplication. Edits to a SKILL.md are reflected in both `/council` and `/academy`.

## Academy-Specific Mechanics

Three franchise mechanics enhance deliberation beyond the base Council system:

1. **[House Tensions](./house-tensions.md)** — Structured cross-house challenge pairings in Phase 3 Round 2
2. **[Support Conversations](./support-system.md)** — Cross-session memory that builds persistent agent pair relationships
3. **[Class Promotion](./promotion-system.md)** — Per-agent growth that unlocks bonus skills after repeated participation
