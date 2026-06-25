# Council EE (Enterprise Edition) — archived

These agents and skills were part of this repo's local 22-perspective council roster.
The canonical open-source [`agentic-council`](https://github.com/dtsong/agentic-council)
release (v1.2.0) deliberately holds them back for a separate `agentic-council-ee`
spin-off, shipping a 19-perspective + Steward roster instead.

When this repo migrated to installing `agentic-council` as a managed Claude Code
plugin, these files were archived here rather than deleted, so they survive for a
future EE plugin without colliding with the v1.2.0 install.

## Contents

| Lens | Color | Domain |
|------|-------|--------|
| **Forge** | Graphite | Microarchitecture, silicon design, RTL security |
| **Foundry** | Copper | Constructive chip design, verification, SoC integration |
| **Accountant** | Emerald | Accounting domain expertise, professional standards |

- `agents/` — the three agent persona files
- `skills/` — their associated skill trees (`forge/`, `foundry/`, `accountant/`)

These are not symlinked into `~/.claude/` and are not loaded by Claude Code.
