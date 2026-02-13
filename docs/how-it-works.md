# How It Works

This document explains the automatic behaviors in `my-claude-setup` — what happens behind the scenes, when it triggers, and how to opt out.

## Skill Auto-Loading

**Trigger**: Claude receives a user message that matches a skill's description triggers.

**What happens**: Claude classifies the user's intent (question, continuation, or action). For action intents, it scores each installed skill against the request using trigger phrases, domain keywords, and exclusion clauses. High-confidence matches are auto-invoked with a one-line announcement. Medium-confidence matches are proposed to the user. Low-confidence matches are skipped silently.

**Visibility**: When a skill activates, Claude announces it:
```
[Skill: tdd] — Enforcing red-green-refactor on this implementation.
```

**Opt-out**: Say "skip skill announcements" or "quiet mode" to suppress announcements. Say "no skills" to disable skill matching for the session.

**Details**: See `skills/skill-matching/SKILL.md` for the full matching protocol.

## Workspace Context Injection

**Trigger**: Claude detects a git remote in the current working directory. The remote's repo name is matched against directories in `~/.claude/workspaces/`.

**What happens**: If a matching workspace directory exists (e.g., `~/.claude/workspaces/my-app/`), its context files are loaded into the session. These typically contain infrastructure maps, team conventions, deployment notes, and project-specific instructions.

**Visibility**: Workspace context is loaded silently. The content appears in Claude's system context but isn't explicitly announced.

**Opt-out**: Remove or rename the workspace directory. Workspace injection only happens when a matching directory exists.

**Details**: Workspace directories are auto-detected via `git remote get-url origin` — the repo name portion of the URL is used as the lookup key.

## Session Handover Auto-Loading

**Trigger**: Start of a new Claude Code session (configured in `CLAUDE.md`).

**What happens**: Claude checks for recent handover documents at `memory/HANDOVER-*.md` and reads the most recent one. Handovers contain decisions made, pitfalls discovered, and next steps from previous sessions.

**Visibility**: Claude reads the handover silently and uses it as context. You may notice Claude referencing prior session decisions.

**Opt-out**: Remove the handover check from your `CLAUDE.md`, or delete handover files you don't want loaded.

**Details**: Handovers are created manually via `/handover` or automatically by the PreCompact hook.

## PreCompact Auto-Handover Hook

**Trigger**: Claude Code's context window approaches its limit and triggers compaction.

**What happens**: Before compaction, the `pre-compact-handover.sh` hook runs automatically. It generates a handover document capturing the current session's state — what was done, key decisions, and what's in progress.

**Visibility**: The hook runs silently. A handover file appears at `memory/HANDOVER-<timestamp>.md`.

**Opt-out**: Remove the PreCompact hook entry from `hooks.json`, or remove `hooks/pre-compact-handover.sh`.

**Details**: See `hooks/pre-compact-handover.sh` for the hook implementation.

## CLAUDE.md Global Instruction Loading

**Trigger**: Every Claude Code session start.

**What happens**: Claude Code reads `~/.claude/CLAUDE.md` and applies its contents as system-level instructions. This file contains skill overrides, tool configuration (NVM sourcing), and personal preferences.

**Visibility**: Instructions are applied silently. Their effects are visible in Claude's behavior (e.g., skill announcements, NVM usage).

**Opt-out**: Edit or remove specific sections from `~/.claude/CLAUDE.md`. The file is a symlink to this repo, so edits here are reflected immediately.

**Details**: See `CLAUDE.md` in this repo for the current configuration.

## Summary

| Behavior | Trigger | Visibility | Opt-out |
|----------|---------|------------|---------|
| Skill auto-loading | Action-intent messages | `[Skill: name]` announcement | "quiet mode" or "no skills" |
| Workspace context | Git remote matches `workspaces/` dir | Silent | Remove workspace dir |
| Session handover loading | Session start | Silent (references prior decisions) | Remove from CLAUDE.md |
| PreCompact auto-handover | Context window compaction | Silent (creates file) | Remove hook from hooks.json |
| CLAUDE.md instructions | Session start | Silent (affects behavior) | Edit CLAUDE.md sections |
