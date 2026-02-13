---
name: skill-matching
description: "Intelligent skill discovery and matching. Classifies user intent, scores skill relevance, and transparently proposes or auto-invokes skills. Supersedes the upstream using-superpowers matching rules."
---

# Skill Matching Protocol

Match skills to user intent using structured classification and confidence scoring instead of blanket invocation. This protocol replaces the upstream "1% rule" with intent-aware, transparent skill activation.

## Step 1: Intent Classification

Classify the user's message before evaluating skills:

| Intent | Signal words | Action |
|--------|-------------|--------|
| **QUESTION** | explain, what, why, how does X work, describe, tell me about | Skip skill matching. Respond directly. |
| **CONTINUATION** | yes, ok, continue, go ahead, looks good, next, do it | Do NOT re-evaluate skills. Continue current workflow. |
| **ACTION** | build, fix, create, review, deploy, test, add, implement, refactor, migrate, scaffold, generate, audit, harden, optimize | Proceed to Step 2 (scoring). |

**Edge cases:**
- "How do I build X?" — ACTION (intent is to build, not just understand)
- "What's wrong with this code?" — ACTION (intent is to fix/debug)
- "Can you review this?" — ACTION (review is an action)
- Short affirmatives after a skill is active — CONTINUATION

## Step 2: Confidence Scoring

For ACTION intents, score each potentially relevant skill:

| Signal | Points |
|--------|--------|
| User uses `/command` syntax | **Auto-invoke** (skip scoring) |
| Exact trigger phrase from skill description | +60 |
| Domain + action type match | +40 |
| Technology keyword mentioned | +20 |
| "Not for:" clause matches the request | **Exclude** (score = 0) |
| `[Council]` prefix and not in deliberation | **Exclude** (score = 0) |
| Generic verb only, no domain signal | -40 |
| Message under 10 words with no domain keyword | -20 |

**Scoring notes:**
- Start from 0, apply matching signals additively
- A skill needs at least one positive signal to be considered
- "Not for:" exclusions are hard stops — they override positive signals
- Council-prefixed skills are only active during `/council` or `/academy` deliberation

## Step 3: Tiered Response

| Confidence | Behavior | Example |
|------------|----------|---------|
| **>80** | Auto-invoke with announcement | `[Skill: tdd] Enforcing red-green-refactor on this implementation.` |
| **30-80** | Propose to user | `I think **web-security-hardening** applies here — it provides a structured security audit checklist. Use it? [Y/n]` |
| **<30** | Skip silently | Respond normally, no mention of skills. |

**Announcement format** (for auto-invoked skills):
```
[Skill: <name>] — <one-line reason>
```

Announce each skill once per session. If the user says "skip skill announcements", "no skills", or "quiet mode", stop announcing and stop proposing.

## Step 4: Composition Rules

When multiple skills score above threshold:

1. **Process skills first** — brainstorming, debugging, TDD determine HOW to approach the task
2. **Implementation skills second** — domain-specific skills guide execution
3. **Max 2 skills per response** without explicit user consent
4. **Workflow-changing skills always propose** — brainstorming and writing-plans get a proposal even at high confidence, because they redirect the entire workflow

## Preserved Principles

These carry forward from the upstream skill system:

### Skill Types
- **Rigid skills** (TDD, debugging): Follow exactly. Don't adapt away discipline.
- **Flexible skills** (patterns, conventions): Adapt principles to context.

The skill itself tells you which type it is.

### Red Flags (Rationalization Detection)

If you catch yourself thinking any of these, pause and check for skills:

| Thought | Reality |
|---------|---------|
| "This is just a simple question" | Classify intent first. Questions skip matching. Actions don't. |
| "I need more context first" | Skills tell you HOW to gather context. Check first. |
| "Let me explore the codebase first" | Skills tell you HOW to explore. Check first. |
| "This doesn't need a formal skill" | If a skill exists and scores >30, propose it. |
| "The skill is overkill" | Let the user decide. Propose, don't suppress. |
| "I'll just do this one thing first" | Check BEFORE doing anything. |

### User Instructions

User instructions say WHAT to do, not HOW. "Add X" or "Fix Y" doesn't mean skip skill workflows. The matching protocol determines whether a skill applies — user phrasing determines intent classification, not skill bypass.

## Quick Reference

```
User message → Classify intent
  QUESTION → respond directly
  CONTINUATION → continue current workflow
  ACTION → score skills → auto-invoke / propose / skip
```
