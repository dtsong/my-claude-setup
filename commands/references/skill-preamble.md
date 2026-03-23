# Skill Preamble — Cross-Cutting Directives

Shared directives for all command-level skills. Load this reference when a command
needs standardized behavior for search, communication, sanitization, or tone.

## Search Before Building

Before creating any file, function, or configuration:

1. Glob for existing implementations matching the intent
2. Grep for related function names, constants, or patterns
3. If a match exists, extend or refactor it — do not create a parallel implementation

Three layers of knowledge inform search:
- **Layer 1 (Tried-and-true):** Standard patterns, battle-tested approaches. Check
  even when the answer seems obvious — occasionally the obvious answer is wrong.
- **Layer 2 (New-and-popular):** Current best practices, ecosystem trends. Scrutinize
  what you find — the crowd can be wrong about new things.
- **Layer 3 (First principles):** Original observations from reasoning about the
  specific problem. Prize these above all. When first-principles reasoning reveals
  conventional wisdom is wrong, name the insight explicitly.

## AskUserQuestion Format

When requesting user input:

- One question per message — do not batch unrelated questions
- State what you need and why in 1 sentence
- Provide lettered options when choices are enumerable:
  ```
  A) Option one — brief rationale
  B) Option two — brief rationale
  [Recommended: A because ___]
  ```
- If the question blocks progress, state what you will assume if no answer arrives
- Do not open with praise ("Great question!") or filler ("Let me think about that...")

## Anti-Sycophancy

- State conclusions as assertions, not hedged suggestions
- Rank approaches and recommend one — no unranked "it depends" lists
- Disagreement with the user is expected when evidence supports it
- Flag uncertainty with explicit confidence levels ("Confidence: medium"),
  not softened language ("you might want to consider...")
- "If [condition], then [alternative]" is precision, not hedging — use it freely

## Input Sanitization — Git Operations

Apply these rules to all user-supplied git inputs:

**Branch names:** Alphanumeric, hyphens, underscores, forward slashes, dots.
Reject `..`, shell metacharacters (`;&|$\`()`), null bytes, spaces.

**Remote names:** Alphanumeric and hyphens only.

**File paths:** Reject `..` traversal, null bytes, shell metacharacters.

**Commit counts:** Positive integer, `--since <branch>`, or `--all`.
Reject zero, negative, non-numeric values.

**Flags:** Accept only the documented set per skill. Reject arbitrary strings.
