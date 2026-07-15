# Skill/Command Loading, Workflow Tool, and Subagent Types (Deep Reference)

Verified against `skills/`, `commands/`, `agents/`, `commands/_council-engine.md`, and this authoring session's own tool preamble, 2026-07-02, HEAD `105427a`.

## Frontmatter loading: description now, body on invocation

Every `SKILL.md` and `commands/*.md` file starts with YAML frontmatter (`name`, `description`, commands optionally add `argument-hint`). Only the `description` field loads into every session's context up front; the body loads only when the skill/command is actually invoked. This is directly observable, not inferred: at the start of this authoring session, the system prompt listed every available skill and command by name only, no bodies, until a `Skill` tool call loaded one.

This is why `pipeline/scripts/skill-audit.py` tracks "always-loaded description cost" (summed tokens of every `description` field) as the metric worth watching: it's the permanent context tax, independent of whether a skill is ever invoked. Run it: `python3 pipeline/scripts/skill-audit.py --json` (verified 2026-07-02: 123 skills under `skills/`, ~5,966 tokens, zero duplicate names, zero identical bodies: re-run before citing, this drifts).

## `commands/*.md`: a second discovery surface, same pipeline

`commands/*.md` files are user-invocable via `/name` syntax but carry the same frontmatter shape and appeared in this session's tool preamble as separate entries alongside `skills/*/SKILL.md` entries: same loading mechanism, two source directories. Confirmed by exact correspondence: all 29 `commands/*.md` basenames (`ls commands/*.md | wc -l`) match one full block of this session's own available-skills list.

### Double-registration: `heavy-file-ingestion`, proven

`skills/heavy-file-ingestion/SKILL.md` (full skill: description, real body, `references/`, `scripts/`, `eval-cases/`) and `commands/heavy-file-ingestion.md` (4-line stub whose entire body is "invoke the `heavy-file-ingestion` skill") both appeared as **separate named entries** in this session's own list: both pay their own description-token cost every session, regardless of invocation. `skill-audit.py`'s ~5,966-token count is computed only over `skills/` (its default `--root`); it does **not** include `commands/*.md` description cost, so the true always-loaded surface is understated unless `commands/` is also passed as a root.

`council` and `ece` also shadow both a `commands/<name>.md` and a `skills/<name>/` directory, but that's a different pattern: `commands/council.md` is the primary orchestrating command, `skills/council/` is a large department-skill tree (68 `SKILL.md` files) loaded selectively, one or two at a time, mid-session: not an always-on monolithic description. Don't generalize "shadowing a skill dir name" as inherently wasteful; check whether the shadow is a single auto-loaded description (`heavy-file-ingestion`'s case) or a conditionally-loaded tree (`council`/`ece`'s case).

## Plugin- and marketplace-provided skills: namespaced loading

Plugin skills load namespaced as `<plugin-name>:<skill-name>`, observed directly as `claude-hud:configure`, `pr-review-toolkit:review-pr`, 14 `superpowers:*` entries, `terraform-skill:terraform-skill`, `frontend-design:frontend-design`, `skill-codex:codex`, and 5 `research-toolkit:*` entries sourced from the `research-toolkit-local` local-directory marketplace (`settings.json:155-160`), confirming local-directory marketplaces feed the same namespaced pipeline as GitHub-sourced ones. Not every enabled plugin necessarily surfaces namespaced skills (some may only add commands); this repo's evidence only establishes the pattern exists, not that it's universal.

## Governance enforcement on discovery-relevant frontmatter

`pipeline/hooks/check_frontmatter.py` requires `description` ≥10 words (`MIN_DESCRIPTION_WORDS = 10`, line 24, the enforced number; governance-spec prose elsewhere describes a 20-word guideline, but the hook's hard floor is 10), kebab-case `name`, and validates any `model` block against enum whitelists. Scope limit: `.pre-commit-config.yaml` scopes this hook to `^skills/.*\.md$` only. **`commands/*.md` and `agents/*.md` frontmatter is validated by nothing**; a malformed `description` there is caught by no committed hook.

## Workflow tool: version floor and args contract

`commands/_council-engine.md:34-46` ("Preflight: Orchestration Capability Check") is the fullest in-repo description:

- Stated version floor: Claude Code ≥ 2.1.154. Asserted by the engine's own prose, not independently confirmed against upstream release notes in this session. Treat as repo-stated, re-check if it matters for a compatibility decision.
- Detection is runtime-only and self-administered: the conductor runs `printenv CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS` and `printenv CLAUDE_CODE_DISABLE_WORKFLOWS` via Bash, and treats an actual failed workflow invocation as the definitive "unavailable" signal. No static capability query is relied on instead.
- Degradation: `workflow` modes go workflow → teams → sequential; `teams-preferred` phases go teams → workflow/sequential; `inline` modes need neither (plain `Task` calls only). The resolved backend is printed when it differs from preferred, and recorded in `session.md` under `Backend:`.

**Args-as-object, exact failure mode:** passing `args` as a JSON-encoded string causes the script's contract guard to throw `requires args: sessionDir, idea, roster[]`: the payload arrives as one string with none of the expected keys present (`commands/_council-engine.md:689`). Fixed defensively (not eliminated) by PR #56 / commit `01b6081`:

```js
// council-deliberation.template.js:35: tolerates a stringified payload,
// but the engine still instructs callers to pass a real object.
const _args = typeof args === 'string' ? JSON.parse(args) : (args || {})
```

Actual `args` shape used by both council templates: `{ sessionDir, workspace, idea, contextBlock, interviewTranscript, pairingRules, roster: [{name, agentType, model, color, skillContent}], rounds, maxPairs, challengeModel, guidedFeedback, startAtRound }`. The script body is read from disk and invoked verbatim: no template-string substitution; every session-specific value flows through `args` only.

## Subagent types: how `agents/*.md` becomes a spawnable type

Every file under `agents/` (38 total) has exactly two frontmatter fields, `name` and `description`, no `model:`. Example (`agents/council-architect.md:1-4`):

```yaml
---
name: "Architect"
description: "Council Blue Lens (system design, data models, APIs, integration patterns)"
---
```

(Paraphrased; the file's actual description uses different separator punctuation. Read `agents/council-architect.md` for the byte-exact frontmatter.)

The council roster table (`commands/council.md:78-100`) has a "Subagent Type" column whose values (`Architect`, `Advocate`, ...) are exactly the `name:` values of the corresponding `agents/council-*.md` files. When the engine spawns via the Task tool, it passes `subagent_type: <from roster table>` (`commands/_council-engine.md:622-628`): the literal string `"Architect"`.

**Verified vs. inferred:** the repo demonstrates the *convention*, author a persona file with a `name:` field, reference that exact name as `subagent_type` at every spawn site, extensively (23 council agent files, zero `model:` fields, one spawn-time routing table instead). Whether the platform mechanically resolves `subagent_type` by scanning `agents/*.md` for a matching `name:`, or via some other path, is **not verifiable from repo files alone**. That is platform-internal behavior the repo relies on without implementing. The repo's evidence it works is behavioral (documented sessions with per-agent round files implying successful spawns), not a static proof.

**Zero `model:` frontmatter is deliberate:** `grep -l "^model:" agents/*.md` → 0 matches. Model selection happens entirely at the Task-tool call site via the engine's per-phase, per-profile routing table: tier aliases only (`sonnet`/`opus`/`fable`/persistent), never a pinned `claude-*` ID (pinned IDs are forbidden at spawn sites, `commands/_council-engine.md:105`). Adding a new agent: `name` + `description` only, no `model:` field; add the routing decision to the engine's table instead.
