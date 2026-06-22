---
name: "enterprise-search-strategy"
department: "scout"
description: "Use when the council needs to surface organizational knowledge buried across multiple internal sources (wikis, design docs, ADRs, past tickets, postmortems, chat archives, code repos). Plans where to look, what to cross-reference, and how to synthesize findings into evidence the council can act on. Do not use for external market research (use competitive-analysis), library evaluation (use library-evaluation), or technology trend assessment (use technology-radar)."
version: 1
triggers:
  - "internal search"
  - "prior art internal"
  - "knowledge synthesis"
  - "what did we decide"
  - "find the doc"
  - "research strategy"
  - "discovery plan"
  - "across the org"
  - "across our codebase"
---

# Enterprise Search Strategy

## Purpose

Plan and execute a structured search across an organization's internal knowledge sources to surface prior decisions, abandoned attempts, related work, and tacit context that the council needs before deliberating. The output is evidence, not opinion.

## Scope Constraints

- Scopes searches across internal sources only (org-private wikis, design docs, ADRs, postmortems, ticket systems, code repos, chat archives, recordings).
- Does not assess external markets or competitors. Hand off to competitive-analysis for that.
- Does not evaluate libraries or vendors. Hand off to library-evaluation or technology-radar.
- Does not produce final design recommendations. Surfaces evidence the rest of the council interprets.

## Inputs

- Topic or decision the council is preparing to deliberate
- Known internal sources (or let the process discover them)
- Relevant date window (e.g., "last 18 months", "since the platform rewrite")
- People or teams whose context is likely involved

## Input Sanitization

No user-provided values are used in commands or file paths. Search queries are read-only operations against internal indexes.

## Procedure

### Step 1: Map the Internal Landscape

Identify which knowledge stores are likely to hold relevant context:
- Wiki and docs site (Confluence, Notion, internal Markdown repos)
- ADR or design-doc directories in the codebase
- Issue tracker (Linear, Jira, GitHub Issues) including closed and won't-fix items
- Postmortems and incident reviews
- Code repository history (commits, PRs, comments)
- Chat archives (Slack channels, Discord, Teams) where decisions get made informally
- Recorded meetings or transcripts if accessible

### Step 2: Plan the Search

For each store from Step 1:
- Draft 3 to 5 search queries covering the topic, related synonyms, abandoned codenames, and people most likely to have raised it.
- Note expected false-positive sources (overly broad keywords, common terms used in unrelated domains).
- Decide depth: skim recent results vs full historical sweep.

### Step 3: Execute and Triage

- Run searches; capture top hits per source with date, author, and a one-line "why this might matter".
- Mark each hit as: directly relevant, tangentially relevant, dead-end, or red-herring.
- Pull threads: when a hit references another doc or ticket, follow it before declaring done.

### Step 4: Cross-Reference and Synthesize

- Group hits by theme (e.g., "we tried this in 2024", "compliance flagged it", "performance concerns came up twice").
- Identify contradictions across sources (different teams holding different positions).
- Flag what is confirmed vs assumed vs hearsay.
- Note silence: topics conspicuously absent from any internal record (often signals tacit consensus or a real gap).

### Step 5: Package Evidence for the Council

- Write a one-page evidence brief: 5 to 10 highest-signal findings with source citations.
- For each, label: precedent, prior attempt, contradiction, gap, or open question.
- Recommend follow-up sources the council should pull from directly during deliberation.

### Progress Checklist

- [ ] Step 1: Internal landscape mapped
- [ ] Step 2: Search plan drafted per store
- [ ] Step 3: Searches executed and hits triaged
- [ ] Step 4: Findings cross-referenced and synthesized
- [ ] Step 5: Evidence brief packaged for the council

> **Compaction resilience:** If context was compacted, re-read this SKILL.md and check the Progress Checklist for completed steps before continuing.

## Handoff

- If a finding suggests systemic risk or compliance exposure, recommend loading guardian/compliance-review or skeptic/threat-model.
- If prior attempts surface that have technical depth, recommend loading architect/system-design to interpret the architectural implications.
- If the search reveals an external precedent (a competitor or open-source project tried this), hand off to scout/competitive-analysis.

## Output Format

### Internal Source Map

| Source | Coverage | Search Queries | Depth |
|--------|----------|----------------|-------|
| Wiki / Confluence | ... | ... | skim / deep |
| ADR repo | ... | ... | skim / deep |
| Issue tracker | ... | ... | skim / deep |
| Postmortems | ... | ... | skim / deep |
| Code repo | ... | ... | skim / deep |
| Chat archives | ... | ... | skim / deep |

### Top Findings

| # | Source | Date | Author | Relevance | One-line summary |
|---|--------|------|--------|-----------|------------------|
| 1 | ... | ... | ... | direct | ... |
| 2 | ... | ... | ... | tangential | ... |

### Evidence Brief

1. **Precedent:** [Finding] (source, date). Implication: ...
2. **Prior attempt:** [Finding] (source, date). What worked, what didn't: ...
3. **Contradiction:** [Team A says X, Team B says Y] (sources). Worth surfacing in council: ...
4. **Gap:** [Topic absent from internal record]. Likely meaning: ...
5. **Open question:** [Finding] (source). Council should resolve before proceeding.

### Recommended Follow-up Reads

- [Doc or ticket] — read in full before round 1 because ...
- [Person to consult] — has tacit context not in any doc

## Quality Checks

- [ ] At least 4 distinct internal sources searched
- [ ] Each source had a tailored query plan, not a single keyword sweep
- [ ] Threads pulled (referenced docs followed, not just top-level hits captured)
- [ ] Findings labeled as precedent / prior attempt / contradiction / gap / open question
- [ ] Sources cited with date and author for traceability
- [ ] Silence noted where conspicuous
- [ ] Evidence brief is concise (one page) and council-ready

## Evolution Notes
<!-- Observations appended after each use -->
