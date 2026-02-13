---
description: "Quick 3-agent gut check — fast takes from Architect, Advocate, Skeptic"
argument-hint: "[--help] [IDEA...]"
---

# /brainstorm — Quick Council

Fast feedback from 3 parallel perspectives. No files, no ceremony.

## Help Flag

If the argument is `--help`, show a brief usage summary and exit:
```
/brainstorm [--help] [IDEA...]
Quick 3-agent gut check — fast takes from Architect, Advocate, Skeptic
```
Then say: `Run /help brainstorm for full details.`

> **Tip:** This is also available as `/council --brainstorm` or `/academy --brainstorm`.

## Usage

```
/brainstorm add a speed tier sidebar to the calc page
/brainstorm should we migrate from Supabase to Drizzle?
/brainstorm $ARGUMENTS
```

## Instructions

When the user runs `/brainstorm`, follow these steps:

### 1. Capture the Idea

The user's idea is everything after `/brainstorm`. If no argument is provided, ask for one.

### 2. Build Context Block

Gather project context by scanning the workspace:

1. Detect workspace: `git rev-parse --show-toplevel` or `$PWD`
2. Read `$WORKSPACE/CLAUDE.md` for project conventions (if it exists)
3. Read `package.json` / `pyproject.toml` for tech stack (if they exist)
4. `ls` top-level directories for project structure
5. `git -C $WORKSPACE branch --show-current` for current branch
6. `git -C $WORKSPACE log --oneline -3` for recent commits

Assemble a compact context block:

```
PROJECT CONTEXT:
- Tech stack: <from scan>
- Key dirs: <from scan>
- Branch: <current branch>
- Recent commits: <last 3 one-liners>
- Project notes: <first few lines of CLAUDE.md>
```

If no project context is available, just include whatever you can gather and skip the rest.

### 3. Launch 3 Agents in Parallel

Launch all 3 Task agents in a **single message** (3 parallel tool calls). Each uses `subagent_type: "general-purpose"` and `model: "sonnet"`.

**Architect** (name: "Architect"):
```
You are Architect, giving a systems/technical perspective.

IDEA: <the user's idea>

<context block>

Give your take in 2-4 sentences. Focus on:
- Where this fits in the codebase (which files/directories/components)
- What you'd build and how it connects to existing code
- Any architectural considerations (state, data flow, performance)

Do NOT write code. Do NOT explore files. Just give your quick systems take based on the context provided.
```

**Advocate** (name: "Advocate"):
```
You are Advocate, giving a UX/product perspective.

IDEA: <the user's idea>

<context block>

Give your take in 2-4 sentences. Focus on:
- Is this good for users? What problem does it solve?
- What should the interaction feel like?
- What's missing from the user's perspective? What would make it great?

Do NOT write code. Do NOT explore files. Just give your quick UX take based on the context provided.
```

**Skeptic** (name: "Skeptic"):
```
You are Skeptic, giving a critical/risk perspective.

IDEA: <the user's idea>

<context block>

Give your take in 2-4 sentences. Focus on:
- What could go wrong? What's the hidden complexity?
- Is there unnecessary scope? What's overengineered?
- What's the simpler version / MVP?

Do NOT write code. Do NOT explore files. Just give your quick critical take based on the context provided.
```

### 4. Synthesize and Present

Once all 3 agents return, present results in this format:

---

## Quick Council: `<idea summary>`

**Architect** says: <their take>

**Advocate** says: <their take>

**Skeptic** says: <their take>

---

**Where they agree:** <1-2 sentences on consensus>

**Key tension:** <1 sentence on the main disagreement or tradeoff>

**Recommended next step:** <concrete suggestion — e.g. "small enough to just build", "worth a full /council session", "needs more research first", etc.>

---

### Important Rules

- Do NOT create any files or write any code
- Do NOT spawn a Team — use 3 independent Task agents (no TeamCreate/cleanup)
- Do NOT ask interview questions — just take the idea and run
- Keep the whole thing fast — agents should use sonnet model and return short takes
- The entire output should be inline in chat, nothing external
