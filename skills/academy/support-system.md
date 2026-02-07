# Support Conversations — Cross-Session Memory

Reference for the Professor during Phase 2.4 (Spawn) and Phase 3 (Deliberation). This mechanic tracks agent pair co-occurrences to build persistent relationships that improve deliberation quality.

## Concept

In Fire Emblem, Support Conversations are relationship-building dialogues between characters that unlock bonuses when they fight together. In the Academy, Support Conversations track which agent pairs have participated in sessions together and how their interactions evolved.

## Support Log

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
    }
  }
}
```

**Pair key format:** Agent names in alphabetical order, joined with `+`. Example: `sage+thief` (not `thief+sage`).

## Support Ranks

| Rank | Sessions Required | Effect |
|------|-------------------|--------|
| — | 0-1 | No effect. Agents interact as strangers. |
| **C** | 2+ | Professor notes shared history in context. |
| **B** | 4+ | Professor injects a shared context brief into spawn prompts. |
| **A** | 7+ | Agents can be paired for position + supplement (saves a deliberation slot). |

## Implementation by Phase

### Phase 2.4: Spawn — Inject Support Context

After the user approves the agent selection, before spawning:

1. Load `.claude/academy/support-log.json`
2. For each pair among selected agents, check their rank
3. Apply rank effects:

**C-rank:** Add a note to the session context:
```
Support Note: Sage and Thief have trained together 3 times before.
Their recent history: [1-sentence summaries from history array]
```

**B-rank:** Add a shared context brief to BOTH agents' spawn prompts:
```
Support Brief (B-rank): You and [other agent] have worked together 5 times.
Key patterns from your history:
- You tend to disagree on [topic] — [agent] usually pushes for X while you push for Y
- You've found common ground before on [topic] by [approach]
- Your last session ended with [outcome]
Use this shared history to make your deliberation more productive.
```

**A-rank:** During Phase 2.3 (Present Selection), note the A-rank pair and offer the option:
```
Sage and Thief have A-rank support (7+ sessions). They can be paired:
- Sage writes the position, Thief writes a targeted supplement
- This saves a deliberation slot while preserving both perspectives

Pair them, or keep separate?
```

### Phase 3: Deliberation — Leverage Support History

During Round 2 tension pair selection:
- B-rank pairs with known disagreement patterns make excellent challenge pairings
- A-rank pairs that have resolved similar tensions before can be noted in the challenge prompt:
  "You've debated this exact topic before. In session-4, you found middle ground on X. Can you do better this time?"

### Cleanup: Update Support Log

After the session ends:

1. Enumerate all pairs among participating agents
2. For each pair:
   - Increment `sessions` count
   - Update `rank` if threshold crossed (2→C, 4→B, 7→A)
   - Append a 1-sentence summary of their interaction to `history` array
   - If they didn't interact directly (weren't in a tension pair), still increment sessions but note "no direct interaction"
3. Write updated log back to `.claude/academy/support-log.json`

## History Summaries

Each history entry should be a single sentence capturing the essence of the pair's interaction:

- Good: "schema vs security tension — Sage conceded encryption-at-rest, Thief accepted incremental migration"
- Bad: "They participated in the session" (too vague)
- Bad: Three paragraphs of detail (too long — keep it scannable)

If agents didn't directly interact (weren't paired in Round 2), use: "co-participated, no direct challenge"

## Edge Cases

- **New pair:** If two agents haven't been in a session together before, create a new entry with `sessions: 1, rank: null, history: []`
- **Stale history:** If history array exceeds 10 entries, keep only the 5 most recent
- **Missing log file:** If `.claude/academy/support-log.json` doesn't exist, create it with an empty `pairs` object
