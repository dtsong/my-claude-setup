# Skill Trigger Reliability Specification v1.1

### Changes in v1.1

- Added **third-person description** requirement (§1.1, cross-ref from Governance §3.1)
- Added **navigation evals** as distinct eval category (§3.7) — tests how Claude
  traverses skill files during execution, not just trigger activation
- Added **Claude A/B development workflow** as the recommended authoring process (§4.4)
- Added **observation patterns** for monitoring in-skill behavior (§4.5)
- Updated trigger reliability checklist (§7) with new items

---

## The Problem

A skill that produces perfect output is worthless if it doesn't fire when it
should. Trigger reliability — the skill activating for the right requests and
staying silent for the wrong ones — is the most common failure mode in
production skill systems and the hardest to debug because it's invisible: the
user doesn't know a skill exists that could have handled their request better.

Claude Code's skill activation depends primarily on the `description` field in
SKILL.md frontmatter. The agent reads available skill descriptions and decides
whether to invoke one. This decision is probabilistic, context-dependent, and
sensitive to phrasing in ways that aren't immediately obvious.

### Observed Failure Modes

| Mode | Description | Frequency |
|------|-------------|-----------|
| **Silent miss** | Skill should fire but doesn't — agent handles request with general reasoning | Very common |
| **Partial activation** | Skill fires but agent doesn't follow the full procedure | Common |
| **Wrong skill fires** | Request triggers the wrong specialist in a suite | Common |
| **Competing activation** | Multiple skills match, agent blends instructions or picks randomly | Occasional |
| **Over-triggering** | Skill fires on requests it wasn't designed for | Occasional |
| **Coordinator bypass** | Agent loads a specialist directly, skipping the coordinator | Occasional |

The root causes cluster into three categories: **description problems** (the
trigger text doesn't match how users phrase requests), **routing ambiguity**
(multiple skills plausibly match), and **context interference** (other
instructions in CLAUDE.md or conversation history override the skill trigger).

---

## 1. Trigger Engineering

### 1.1 Anatomy of a High-Reliability Description

The `description` field is the single most important line in any SKILL.md.
It needs to accomplish three things simultaneously:

1. **Match user intent vocabulary** — use the words users actually say
2. **Differentiate from sibling skills** — be specific enough that only the
   right skill matches
3. **Overcome activation inertia** — be assertive enough that the agent
   actually invokes the skill rather than handling the request itself

```yaml
# ❌ Low-reliability description
description: "Helps with CSS issues"

# ❌ Better but still weak — too passive, missing user vocabulary
description: "Debug CSS and layout problems in React components"

# ✅ High-reliability description
description: >
  Use this skill when the user reports visual/layout bugs: elements
  misaligned, overlapping, wrong size, spacing issues, responsive
  breakpoints failing, Tailwind classes not applying, flexbox/grid
  not behaving as expected, or z-index stacking problems. Also use
  for: "it looks wrong", "the layout is broken", "styles aren't
  working", "CSS isn't applying". Do NOT use for functional bugs
  (clicks not working, data not loading) — those go to
  ui-bug-investigator.
```

The high-reliability version does several things the weak versions don't:

- **Starts with "Use this skill when"** — directly instructs the agent to
  activate, rather than describing what the skill does passively
- **Lists specific symptoms** in the user's vocabulary ("elements misaligned",
  "spacing issues", "looks wrong")
- **Includes quoted trigger phrases** — literal strings users commonly type
- **States negative boundaries** — "Do NOT use for functional bugs" prevents
  over-triggering and directs to the correct alternative
- **Names the alternative** — "those go to ui-bug-investigator" helps the
  agent route correctly when this skill is the wrong match

**Third-person requirement:** Descriptions are injected into the system prompt
alongside other skills' descriptions. Inconsistent point-of-view causes
discovery problems. Always write in third person or imperative voice:

- ✅ "Processes Excel files and generates reports"
- ✅ "Use this skill when the user reports visual bugs"
- ❌ "I can help you process Excel files"
- ❌ "You can use this to process Excel files"

See Governance Spec §3.1 for the full description requirements.

### 1.2 The Description Formula

Apply this structure to every skill description:

```
[Activation directive]: "Use this skill when..." or "Invoke this skill for..."

[Positive triggers]: Specific symptoms, task types, and user vocabulary
  that SHOULD activate this skill. Include both technical terms and
  casual phrasing.

[Quoted phrases]: 2-5 literal strings users commonly type that should
  trigger this skill. These act as exact-match anchors.

[Negative boundaries]: "Do NOT use for..." with specific exclusions
  that commonly cause misfires, naming the correct alternative skill.
```

### 1.3 Trigger Vocabulary Mining

The most common cause of silent misses is that the description uses technical
vocabulary while users use casual language (or vice versa).

**Technique: Build a trigger vocabulary map for each skill.**

For `css-layout-debugger`:
```
Technical terms           User casual phrasing
──────────────────────   ──────────────────────
flexbox                  "things aren't lining up"
grid layout              "the columns are wrong"
z-index                  "element is behind/hidden"
responsive breakpoint    "looks fine on desktop but broken on mobile"
Tailwind class           "the class isn't doing anything"
cascade/specificity      "my styles are being overridden"
box model                "too much space" / "no padding"
overflow                 "content is cut off" / "scrollbar appeared"
```

Include BOTH columns in the description. The technical terms catch experienced
developers; the casual phrasing catches everyone else.

### 1.4 Assertive vs. Passive Descriptions

Claude Code's skill activation has an "inertia" problem — the agent often
prefers to handle requests with its own general reasoning rather than loading
a skill. Passive descriptions make this worse because they describe the skill
like a Wikipedia entry rather than instructing the agent to use it.

```yaml
# Passive (low activation rate)
description: "A skill for debugging CSS layout issues in React components"

# Assertive (higher activation rate)
description: >
  ALWAYS use this skill for any visual or layout problem. This includes...
```

The word "ALWAYS" is strong medicine — use it when the skill should genuinely
fire for every request in its category. For skills with narrower triggers,
use "Use this skill when" or "Invoke this skill for" as the opening.

### 1.5 Description Length Sweet Spot

Too short and the description lacks the vocabulary to match diverse user
phrasing. Too long and key triggers get diluted.

**Target: 40-80 words.** This provides enough room for:
- 1 activation directive (5-8 words)
- 3-5 positive trigger categories with specifics (20-40 words)
- 2-4 quoted phrases (10-20 words)
- 1-2 negative boundaries with alternatives (10-15 words)

Descriptions under 20 words almost always have low activation rates.
Descriptions over 120 words show diminishing returns and can confuse
the routing decision.

### 1.6 Coordinator Description Engineering

Coordinator descriptions need special treatment because they're the entry
point for an entire suite. A coordinator that doesn't fire means none of
its specialists fire.

```yaml
# Coordinator: cast a wide net
description: >
  Use this skill for ANY frontend issue, bug, or question about the UI.
  This includes: visual bugs, layout problems, broken components,
  state management issues, rendering errors, test failures, CSS problems,
  performance issues, accessibility concerns, or any question starting
  with "why does this component..." or "the page is showing...".
  This is the entry point for all frontend QA work.
```

Key differences from specialist descriptions:
- **Broader trigger vocabulary** — covers the entire domain, not one niche
- **"ANY" and "ALL" language** — reduces the chance of the agent bypassing
  the coordinator to handle a request directly
- **"This is the entry point"** — explicitly instructs the agent to route
  through this skill, not skip to a specialist

---

## 2. Routing Optimization

### 2.1 The Disambiguation Problem

When two skills could plausibly handle a request, the agent either picks one
semi-randomly or blends them. This is the most common source of wrong-skill
activations.

**Solution: Explicit discrimination criteria in the coordinator.**

```markdown
## Classification Logic

Classify the user's request by PRIMARY symptom:

| If the user describes... | Route to | NOT to |
|--------------------------|----------|--------|
| Visual/layout problem (misaligned, wrong size, overlapping) | css-layout-debugger | ui-bug-investigator |
| Functional failure (click doesn't work, data missing, error thrown) | ui-bug-investigator | css-layout-debugger |
| Component not rendering at all | ui-bug-investigator | css-layout-debugger |
| Component renders but looks wrong | css-layout-debugger | ui-bug-investigator |
| Test failure with visual assertion | css-layout-debugger | regression-test-generator |
| Test failure with logic assertion | ui-bug-investigator | regression-test-generator |
| Request to add/modify tests | regression-test-generator | ui-bug-investigator |
| "Map the components" / "what's on this page" | page-component-mapper | ui-bug-investigator |

When ambiguous: Ask the user "Is this a visual/layout issue or a
functional/behavior issue?" before routing.
```

The "NOT to" column is critical. Without it, the agent only has positive
signal. With it, each row creates a **contrastive pair** that trains the
routing decision — "visual problems go HERE, not THERE."

### 2.2 Keyword Anchoring

For requests that use specific terms, add keyword-based routing shortcuts
to the coordinator:

```markdown
## Keyword Shortcuts

If the request contains these terms, route directly (skip full classification):

| Keywords | Route to |
|----------|----------|
| "tailwind", "css", "layout", "flexbox", "grid", "responsive", "margin", "padding", "z-index" | css-layout-debugger |
| "hydration", "state", "useState", "useEffect", "re-render", "race condition", "undefined is not" | ui-bug-investigator |
| "component tree", "component map", "what components", "trace imports" | page-component-mapper |
| "write test", "add test", "test coverage", "test for" | regression-test-generator |

If no keyword match → use the classification table above.
```

Keyword shortcuts create a fast path that bypasses the classification logic
for unambiguous requests. This reduces both token cost (less reasoning needed)
and routing errors (exact matches are more reliable than classification).

### 2.3 The "Catch and Redirect" Pattern

When a specialist starts executing and realizes the request belongs to a
different specialist, it should stop early and redirect rather than attempting
to handle something outside its scope:

```markdown
## Early Redirect Check (Step 1 in every specialist)

Before beginning the diagnostic procedure, verify this is the right skill:

- If the issue is purely visual/layout with no functional component
  → STOP. Output: {"redirect": "css-layout-debugger", "reason": "pure layout issue"}
- If the issue involves data flow, state management, or API calls
  → STOP. Output: {"redirect": "ui-bug-investigator", "reason": "functional issue"}
- If the user is asking to write or modify tests, not debug a bug
  → STOP. Output: {"redirect": "regression-test-generator", "reason": "test request"}

Only proceed past Step 1 if the request genuinely belongs to this skill.
```

This acts as a second routing layer — the specialist validates the
coordinator's routing decision before investing tokens in the full procedure.

### 2.4 Anti-Bypass Patterns

The agent sometimes skips the coordinator and loads a specialist directly,
especially when the user's request closely matches a specialist's description.
This breaks the routing logic and can cause wrong-skill activation.

**Pattern 1: Coordinator-first directive in CLAUDE.md**

```markdown
## Skill Routing

For frontend QA work, ALWAYS start with the frontend-qa coordinator skill.
Do NOT load specialist skills (css-layout-debugger, ui-bug-investigator, etc.)
directly. The coordinator handles classification and routing.
```

**Pattern 2: Self-referencing specialist descriptions**

```yaml
# In the specialist's frontmatter
description: >
  CSS layout debugging specialist. This skill is loaded BY the frontend-qa
  coordinator — do not invoke directly. If you're considering using this
  skill, use the frontend-qa coordinator instead which will route here
  if appropriate.
```

**Pattern 3: Specialist self-check**

```markdown
## Pre-Check
If this skill was loaded directly (not via the frontend-qa coordinator):
  Output a note: "This specialist should be invoked through the
  frontend-qa coordinator for proper routing. Proceeding, but
  classification may be suboptimal."
```

---

## 3. Eval Methodology

### 3.1 Three Eval Dimensions

Skill quality requires three distinct eval types, each testing a different
system:

| Eval Type | What It Tests | Failure Signal |
|-----------|--------------|----------------|
| **Trigger evals** (§3.2-3.6) | Does the skill activate for the right requests? | Silent misses, wrong skill fires |
| **Output evals** (Governance Spec §7) | Does the skill produce correct results? | Wrong output, incomplete analysis |
| **Navigation evals** (§3.7) | Does the agent traverse skill files effectively? | Missed references, partial reads, ignored content |

Trigger evals test activation. Output evals test execution quality.
Navigation evals test the structural effectiveness of your skill's file
organization. All three are necessary — a skill can pass output evals
(correct results when invoked correctly) while failing trigger evals
(doesn't activate for natural requests) and navigation evals (reads files
in suboptimal order, misses important references).

### 3.2 Why Trigger Evals Are Different

Standard skill evals test whether the skill produces correct output given
correct invocation. Trigger evals test whether the skill gets invoked at all
given a natural user request. They're testing a different system — the
activation decision, not the execution quality.

This means trigger evals need:
- **Natural language inputs** (how users actually phrase requests, not
  sanitized technical descriptions)
- **Expected activation outcomes** (which skill should fire, or none)
- **Negative cases** (requests that should NOT trigger the skill)
- **Ambiguous cases** (requests that could go either way, with acceptable
  routing options)

### 3.3 Trigger Eval Case Structure

```markdown
# Trigger Eval Case: [ID]

## Input
The exact user message, written in natural language as a user would type it.

## Expected Activation
- **Should fire:** [skill name] or [coordinator → specialist name]
- **Acceptable alternatives:** [list of skills that would also be okay]
- **Should NOT fire:** [list of skills this should not trigger]

## Classification
- **Trigger type:** exact_match | vocabulary_match | intent_match | ambiguous
- **Difficulty:** easy | medium | hard
- **Tests:** [which specific aspect of trigger reliability this case tests]

## Grading
- PASS: Expected skill fires
- PARTIAL: Acceptable alternative fires
- FAIL: Wrong skill fires, no skill fires, or should-not-fire skill activates
```

### 3.4 Trigger Eval Case Categories

Build eval cases across these categories for comprehensive trigger coverage:

**Category 1: Direct matches (should always pass)**
User phrasing that closely matches the skill's description vocabulary.

```markdown
# Case: direct-css-01
## Input
"The flexbox layout is broken on the dashboard page — items aren't aligning"
## Expected Activation
- Should fire: frontend-qa coordinator → css-layout-debugger
- Should NOT fire: ui-bug-investigator
## Classification
- Trigger type: exact_match (contains "flexbox", "layout", "aligning")
- Difficulty: easy
```

**Category 2: Casual phrasing (tests vocabulary breadth)**
The same intent expressed without technical terms.

```markdown
# Case: casual-css-01
## Input
"The sidebar looks weird, everything is jumbled up and overlapping"
## Expected Activation
- Should fire: frontend-qa coordinator → css-layout-debugger
- Should NOT fire: ui-bug-investigator
## Classification
- Trigger type: vocabulary_match ("looks weird", "jumbled", "overlapping")
- Difficulty: medium
```

**Category 3: Ambiguous requests (tests routing precision)**
Requests that could plausibly match multiple skills.

```markdown
# Case: ambiguous-01
## Input
"The component is showing wrong data and it's also misaligned"
## Expected Activation
- Should fire: frontend-qa coordinator (which should then ask for clarification
  or route to ui-bug-investigator as primary, with a note about the layout issue)
- Acceptable alternatives: css-layout-debugger (if it handles the visual aspect
  and notes the data issue for a different skill)
- Should NOT fire: page-component-mapper, regression-test-generator
## Classification
- Trigger type: ambiguous (both functional and visual symptoms)
- Difficulty: hard
```

**Category 4: Negative cases (tests over-triggering)**
Requests that should NOT activate the skill.

```markdown
# Case: negative-css-01
## Input
"Write a test for the login form validation"
## Expected Activation
- Should fire: frontend-qa coordinator → regression-test-generator
- Should NOT fire: css-layout-debugger, ui-bug-investigator
## Classification
- Trigger type: negative (for css-layout-debugger)
- Difficulty: easy
```

**Category 5: Edge cases (tests boundary conditions)**
Requests at the boundary between two skills' domains.

```markdown
# Case: edge-01
## Input
"The modal animation is janky and sometimes the close button doesn't respond"
## Expected Activation
- Should fire: frontend-qa coordinator → ui-bug-investigator
  (functional failure — button not responding — is the primary symptom)
- Acceptable alternative: css-layout-debugger
  (animation jank could be classified as visual)
- Notes: The coordinator should identify both symptoms and route to
  the one matching the primary concern
## Classification
- Trigger type: intent_match (requires understanding which symptom is primary)
- Difficulty: hard
```

**Category 6: Coordinator bypass attempts (tests routing discipline)**
Requests phrased in ways that might cause direct specialist activation.

```markdown
# Case: bypass-01
## Input
"Run the css-layout-debugger on the navbar component"
## Expected Activation
- Should fire: frontend-qa coordinator → css-layout-debugger
  (should still route through the coordinator even when the user names
  the specialist directly)
- Acceptable alternative: css-layout-debugger directly
  (if CLAUDE.md routing directive isn't strong enough)
## Classification
- Trigger type: exact_match (user names the skill)
- Difficulty: medium
- Tests: coordinator-first discipline
```

### 3.5 Trigger Eval Case Distribution

For each skill or skill suite, build eval cases with this distribution:

| Category | Count | Purpose |
|----------|-------|---------|
| Direct matches | 3-5 | Baseline — should always pass |
| Casual phrasing | 3-5 | Tests vocabulary breadth |
| Ambiguous requests | 2-3 | Tests routing precision |
| Negative cases | 3-5 per skill | Tests over-triggering |
| Edge cases | 2-3 | Tests boundary handling |
| Coordinator bypass | 2-3 | Tests routing discipline |

**Total: 15-25 trigger eval cases per skill suite.**

### 3.6 Trigger Eval Execution

Trigger evals are harder to automate than output evals because you're
testing activation, not content. Two approaches:

**Approach A: Conversation replay**
1. Create a fresh Claude Code session (or API conversation)
2. Load the skill suite into the agent's context
3. Send each eval case input as a user message
4. Observe which skill (if any) the agent invokes
5. Grade against the expected activation

**Approach B: Classification test**
1. Feed the coordinator SKILL.md to the model as a system prompt
2. Send each eval case input as a user message
3. Ask: "Based on the skill routing table, which specialist should handle this?"
4. Grade the routing decision

Approach A is more realistic but expensive (full agent invocation per case).
Approach B is cheaper and tests the routing logic in isolation, but doesn't
catch activation inertia problems (where the agent doesn't invoke any skill).

**Recommended: Use Approach B for rapid iteration on descriptions and routing
tables. Use Approach A periodically (weekly or before releases) for full
end-to-end trigger validation.**

### 3.7 Navigation Evals

Navigation evals test a distinct dimension: **how the agent traverses your
skill's files during execution.** Neither trigger evals (does it activate?)
nor output evals (is the result correct?) catch structural problems in how
the agent moves through your skill's file tree.

**What navigation evals detect:**

| Observation | What It Means | Fix |
|-------------|--------------|-----|
| Agent reads files in unexpected order | Skill structure isn't intuitive | Reorder references in SKILL.md, add clearer navigation cues |
| Agent fails to follow references | Links aren't prominent enough | Make references more explicit, use imperative "Read X now" |
| Agent reads the same file repeatedly | Content should be in SKILL.md | Promote frequently-accessed content to the main file |
| Agent never accesses a bundled file | File is unnecessary or poorly signaled | Remove the file or improve its reference in SKILL.md |
| Agent uses `head -100` instead of full read | Reference chain is too deep | Flatten to one-level-deep (see Governance Spec §2.5) |
| Agent skips procedure steps | Steps lack clear sequencing or are optional-looking | Strengthen imperative language, add "Do NOT skip" |

**Navigation eval case structure:**

```markdown
# Navigation Eval Case: [ID]

## Input
A request that should trigger the skill and exercise file navigation.

## Expected Navigation
- Files that SHOULD be read: [list in expected order]
- Files that should NOT be read: [list]
- Expected procedure path: [step sequence]

## Observation Points
- Does the agent read SKILL.md first?
- Does it follow the reference table to the correct file?
- Does it read the full file or use head/grep?
- Does it re-read any files? Which ones?
- Does it skip any procedure steps?

## Grading
- PASS: Agent reads expected files, follows procedure in order
- PARTIAL: Correct outcome but suboptimal navigation (extra reads, wrong order)
- FAIL: Missed critical reference file or skipped important steps
```

**How to run navigation evals:**

1. Use Approach A (conversation replay) — you need to see actual tool calls
2. Monitor which `Read` or `cat` commands the agent issues
3. Log the sequence of files accessed and commands used
4. Compare against expected navigation pattern

Navigation evals are expensive (full conversation replay required) but
high-signal. Run them when: restructuring a skill's file organization,
adding or removing reference files, or when output evals pass but users
report inconsistent quality (suggesting the agent sometimes misses context).

**Recommended frequency:** Run 3-5 navigation eval cases per skill when
reorganizing file structure. Add navigation checks to the periodic
Approach A trigger eval runs.

### 3.8 Trigger Eval Metrics

Track these metrics across eval runs to measure trigger reliability:

| Metric | Formula | Target |
|--------|---------|--------|
| **Activation rate** | Cases where any skill fires / total cases that should trigger a skill | ≥95% |
| **Correct routing rate** | Cases where the expected skill fires / cases where any skill fires | ≥90% |
| **Acceptable routing rate** | Cases where expected OR acceptable alternative fires / cases where any skill fires | ≥95% |
| **False positive rate** | Cases where a skill fires on a negative case / total negative cases | ≤5% |
| **Bypass rate** | Cases where specialist fires directly, skipping coordinator / total cases | ≤10% |

**Activation rate is the most important metric.** A skill that fires on the
right requests with 90% routing accuracy is far more useful than one with
perfect routing that only fires 60% of the time.

---

## 4. Development Workflow

### 4.1 The Description Refinement Loop

```
1. Write initial description using the formula (§1.2)
2. Build trigger eval cases (§3.3-3.5)
3. Run eval cases (Approach B for speed)
4. Analyze failures by category:
   - Silent misses → add the missing vocabulary to the description
   - Wrong routing → add contrastive pairs to the coordinator
   - Over-triggering → add negative boundaries to the description
   - Bypass → strengthen coordinator-first directive
5. Update description and routing logic
6. Re-run eval cases
7. Repeat until metrics hit targets
```

### 4.2 Failure-Driven Description Updates

Each eval failure type has a specific fix pattern:

**Silent miss on casual phrasing:**
```yaml
# Before
description: "Debug CSS flexbox and grid layout issues"
# Failed case: "everything is bunched together on the left side"

# After — added casual vocabulary
description: >
  Use this skill for layout problems: elements misaligned, overlapping,
  wrong size, spacing issues, "bunched together", "off to one side",
  "not centered", "too much space"...
```

**Wrong skill fires:**
```yaml
# Before
description: "Debug UI component issues"
# Stole requests from css-layout-debugger because "UI" is too broad

# After — narrowed to functional issues with explicit exclusion
description: >
  Use this skill for functional UI bugs: components not rendering,
  click handlers not firing, data not loading, state not updating,
  errors in console. Do NOT use for visual/layout issues (misaligned,
  wrong size, overlapping) — those go to css-layout-debugger.
```

**Over-triggering:**
```yaml
# Before
description: "Use for any issue with React components"
# Fired on requests to write tests, map components, review code

# After — explicit negative boundaries
description: >
  Use this skill for DEBUGGING functional bugs in React components.
  Do NOT use for: writing tests (→ regression-test-generator),
  mapping component trees (→ page-component-mapper), or code review.
```

**Coordinator bypass:**
```
# CLAUDE.md directive addition
For ANY frontend issue, bug, or UI question: ALWAYS invoke the
frontend-qa coordinator skill first. Never load css-layout-debugger,
ui-bug-investigator, or other frontend specialists directly.
```

### 4.3 A/B Testing Descriptions

When unsure which description wording will perform better, test both:

1. Write two description variants
2. Run the same trigger eval cases against each
3. Compare activation rates and routing accuracy
4. Keep the winner, discard the loser

```yaml
# Variant A: Technical-first
description: >
  Debug CSS layout, flexbox, grid, and responsive issues in React/Next.js.
  Use when elements are misaligned, overlapping, or incorrectly sized.

# Variant B: Symptom-first
description: >
  Use this skill when something LOOKS wrong on the page: misaligned,
  overlapping, wrong size, broken on mobile, "it looks off", or
  "the layout is messed up".

# Test both against the same eval cases, measure activation rate
```

In practice, symptom-first descriptions (Variant B) tend to outperform
technical-first descriptions because they match user vocabulary more broadly.

### 4.4 The Claude A/B Development Workflow

The most effective skill development process uses two Claude instances with
distinct roles. This works because Claude understands what agents need and
can anticipate failure modes from both sides.

**Claude A ("the architect"):** The instance you work with to design,
write, and refine the skill. Claude A helps create descriptions, procedures,
and file structure based on your domain expertise.

**Claude B ("the test agent"):** A fresh instance with the skill loaded,
used for real tasks. Claude B reveals gaps through actual usage because it
approaches the skill without the context of its creation.

**Workflow for new skills:**

```
1. Complete a task WITHOUT a skill
   Work through the problem with Claude A using normal prompting.
   Notice what context you repeatedly provide — table names, filtering
   rules, naming conventions, common patterns. This becomes the skill.

2. Ask Claude A to create the skill
   "Create a skill that captures this pattern. Include the table schemas,
   the rule about filtering test accounts, and the query patterns."
   Claude A understands skill structure natively.

3. Review for conciseness (§4.1 Test 1)
   "Remove the explanation about what win rate means — Claude already
   knows that. Keep the project-specific field definitions."

4. Improve information architecture
   "Organize this so table schemas are in a separate reference file.
   We might add more tables later."

5. Test with Claude B
   Give Claude B (fresh instance, skill loaded) actual tasks.
   Observe: Does it find the right information? Apply rules correctly?
   Navigate the file structure effectively?

6. Bring observations back to Claude A
   "Claude B forgot to filter test accounts on regional reports.
   The rule is in the skill but maybe not prominent enough."
   Claude A refines based on actual agent behavior.

7. Iterate until Claude B handles tasks reliably
```

**Workflow for improving existing skills:**

```
1. Use the skill with Claude B on real work
   Not test scenarios — actual tasks.

2. Observe Claude B's behavior
   Watch for: where it struggles, what it misses, which files it reads
   or ignores, whether it follows the full procedure.

3. Return to Claude A with specifics
   Share the current SKILL.md. Describe what you observed.
   "Claude B always reads the checklist three times. Is the reference
   not prominent enough in SKILL.md?"

4. Apply Claude A's refinements
   Update the skill based on Claude A's suggestions.

5. Test again with Claude B
   Same types of tasks, fresh instance.

6. Repeat observe → refine → test cycle
```

**Why this works:** Claude A provides agent-aware design expertise. You
provide domain expertise. Claude B provides ground truth on what actually
happens when the skill is used. The cycle closes the gap between what the
skill author intended and what the agent actually does.

### 4.5 Observation Patterns for In-Skill Behavior

As you develop skills, pay attention to how Claude actually uses them.
These observation patterns reveal structural problems that trigger evals
and output evals miss:

**Unexpected exploration paths:** Claude reads files in an order you didn't
anticipate. This usually means your SKILL.md structure isn't as intuitive
as you thought. Fix: reorder references to match the agent's natural
reasoning flow rather than your organizational logic.

**Missed connections:** Claude fails to follow references to important files.
The link exists but the agent doesn't see it or doesn't prioritize it.
Fix: use imperative language ("Read `references/patterns.md` now") rather
than passive mentions ("See patterns.md for details").

**Overreliance on certain sections:** Claude repeatedly reads the same file
or section. This content is critical enough that it should be in SKILL.md
rather than a separate reference file. Fix: promote the content to the
main file or duplicate the essential parts.

**Ignored content:** A bundled file that Claude never accesses across multiple
uses is either unnecessary or its purpose isn't signaled clearly enough in
SKILL.md. Fix: remove the file or make its trigger condition more explicit.

**Partial reads:** Claude uses `head -100` or `grep` rather than reading a
full reference file. This typically means the file is behind a reference-to-
reference chain (violating the one-level-deep rule in Governance Spec §2.5).
Fix: flatten the reference structure so the file is directly accessible from
SKILL.md.

**Step skipping:** Claude jumps past procedure steps, especially optional-
looking ones. Fix: strengthen imperative language, remove conditional
framing that makes steps look optional, or add "Do NOT skip" markers.

---

## 5. Advanced Patterns

### 5.1 Layered Trigger Reinforcement

Don't rely on the description alone. Reinforce triggers at multiple layers:

**Layer 1: CLAUDE.md project instructions**
```markdown
## Available Skills
- Frontend QA issues (visual bugs, component errors, layout problems)
  → Use the frontend-qa skill suite
- API debugging → Use the api-debugger skill
```

**Layer 2: Skill description (frontmatter)**
The primary trigger — engineered per §1.

**Layer 3: Coordinator classification logic**
Keyword shortcuts + classification table + contrastive pairs.

**Layer 4: Specialist early redirect**
Self-check that validates routing before executing.

Each layer catches what the previous layer missed. A request that doesn't
trigger the coordinator from its description might still get routed correctly
if the CLAUDE.md mentions the skill suite for that domain.

### 5.2 Seasonal Description Updates

User vocabulary evolves. New frameworks introduce new terminology. Edge
cases emerge from production usage. Schedule periodic description reviews:

```
Monthly:
- Review trigger eval metrics from the past 30 days
- Add any new user phrasings that caused silent misses
- Remove or update outdated terminology
- Re-run trigger eval suite to confirm no regressions

After major dependency updates:
- Update framework-specific vocabulary (e.g., new Next.js 15 terminology)
- Add new error message patterns users might report
- Re-run trigger evals
```

### 5.3 Cross-Suite Conflict Resolution

When multiple skill suites are installed (frontend QA + API debugging + code
review), their descriptions can conflict — a request like "the API response
is causing the UI to show wrong data" could match both frontend QA and API
debugging.

**Resolution pattern: Priority declarations in CLAUDE.md**

```markdown
## Skill Priority

When a request could match multiple skill suites:
1. If the user mentions a specific skill or domain → use that suite
2. If the symptom is in the UI (visible to the user) → frontend-qa
3. If the symptom is in data/API (visible in network/logs) → api-debugger
4. If the request is about code quality (not a bug) → code-review
5. When ambiguous → ask the user: "Is this a UI issue or a data/API issue?"
```

### 5.4 Dynamic Trigger Context

Some skills should fire in certain project contexts but not others. Use
CLAUDE.md to provide context-dependent activation:

```markdown
## Context-Dependent Skills

This project uses Next.js App Router with Tailwind CSS.
- For ANY styling issue, ALWAYS use css-layout-debugger (Tailwind-aware)
- For ANY routing issue, ALWAYS use the page-component-mapper first
  to understand the route → component mapping before debugging

This project does NOT use:
- Redux (do not suggest Redux-related debugging steps)
- CSS modules (all styling is Tailwind utility classes)
```

This contextual information helps the agent make better activation decisions
because it knows which skills are relevant to this specific project.

### 5.5 Trigger Telemetry

If you have observability infrastructure, log trigger decisions:

```json
{
  "event": "skill_trigger_decision",
  "user_message_preview": "the sidebar is overlapping the...",
  "skills_considered": ["frontend-qa-coordinator", "code-review"],
  "skill_activated": "frontend-qa-coordinator",
  "subsequent_routing": "css-layout-debugger",
  "confidence": "high",
  "trigger_type": "keyword_match",
  "matched_keywords": ["overlapping"],
  "session_id": "...",
  "timestamp": "..."
}
```

Aggregate this data to find:
- Which user phrasings cause silent misses (no skill activated)
- Which requests cause wrong routing (skill activated → redirect)
- Which descriptions have the lowest activation rates
- Which keyword shortcuts are doing the most work

---

## 6. Integration with Governance Pipeline

### 6.1 Pre-Commit Hook: `check_triggers.py`

**Tier:** Warn (advisory — doesn't block commits)

**Checks:**
1. Description exists and is ≥20 words
2. Description starts with an activation directive ("Use this skill",
   "ALWAYS use", "Invoke this skill")
3. Description contains at least one negative boundary ("Do NOT use for")
4. **Description is in third person** (no "I can", "I will", "you can",
   "you should" phrasing)
5. Coordinator descriptions contain "entry point" or "ALWAYS" language
6. Specialist descriptions in suites reference the coordinator
7. No two skills in the same suite have >60% vocabulary overlap in descriptions
8. **MCP tool references use `ServerName:tool_name` format** (no bare tool names)

**Output:**
```
⚠️  skills/frontend-qa/skills/css-layout-debugger/SKILL.md
   Description is only 12 words — target ≥40 for reliable activation
   Missing activation directive — start with "Use this skill when..."
   Missing negative boundary — add "Do NOT use for..." clause
   Description uses first person ("I can help") — use third person

⚠️  skills/data-pipeline/SKILL.md
   MCP tool reference "bigquery_schema" should be "BigQuery:bigquery_schema"
```

### 6.2 Trigger Eval Cases in the Eval Pipeline

Add trigger eval cases alongside output eval cases:

```
eval-cases/
├── evals.json                    # Output eval index
├── trigger-evals.json            # Trigger eval index
├── navigation-evals.json         # Navigation eval index (optional)
├── cases/
│   ├── 01-basic-mapping.md       # Output eval case
│   └── ...
├── trigger-cases/
│   ├── direct-match-01.md        # Trigger eval case
│   ├── casual-phrasing-01.md
│   ├── ambiguous-01.md
│   ├── negative-css-01.md
│   └── ...
└── navigation-cases/
    ├── nav-full-procedure-01.md  # Navigation eval case
    └── ...
```

```json
// trigger-evals.json
{
  "suite": "frontend-qa",
  "target_metrics": {
    "activation_rate": 0.95,
    "correct_routing_rate": 0.90,
    "acceptable_routing_rate": 0.95,
    "false_positive_rate": 0.05,
    "bypass_rate": 0.10
  },
  "cases": [
    {
      "id": "direct-match-01",
      "category": "direct_match",
      "difficulty": "easy",
      "file": "trigger-cases/direct-match-01.md"
    },
    {
      "id": "casual-phrasing-01",
      "category": "casual_phrasing",
      "difficulty": "medium",
      "file": "trigger-cases/casual-phrasing-01.md"
    }
  ]
}
```

### 6.3 CI Integration

Add a trigger eval stage to the eval workflow:

```yaml
# In .github/workflows/skill-eval.yml
- name: Run trigger evaluations
  run: |
    bash pipeline/scripts/run-trigger-evals.sh \
      --targets "${{ steps.targets.outputs.targets }}" \
      --model "${{ inputs.model || 'sonnet' }}" \
      --approach classification  # or 'full' for end-to-end
```

The trigger eval script:
1. Loads the coordinator SKILL.md as context
2. Sends each trigger eval case input
3. Records which skill the model routes to
4. Grades against expected activation
5. Produces a trigger reliability report with per-metric scores

### 6.4 Updated Governance Spec: Description Requirements

See Governance Spec §3.1 for frontmatter validation rules. Additional
trigger-specific checks:

```
description field requirements:
  - Minimum 20 words (Warn if under, Info if under 40)
  - Should start with activation directive
  - Should be written in third person (no "I" or "you")
  - Should contain at least one negative boundary for specialists
  - Coordinator descriptions should contain broad domain vocabulary
  - Specialist descriptions should NOT duplicate coordinator vocabulary
    (they should be more specific)
  - MCP tool references should use fully qualified ServerName:tool_name format
```

### 6.5 Updated Init Prompt: Trigger Eval Scaffolding

The init prompt should generate:
- `trigger-evals.json` template in eval-cases/
- 3 example trigger eval cases (one direct match, one casual, one negative)
- `navigation-evals.json` template (optional, for skills with complex file structures)
- `run-trigger-evals.sh` script
- `check_triggers.py` pre-commit hook

---

## 7. Trigger Reliability Checklist

Use this checklist when creating or reviewing skill descriptions:

### For every skill:
- [ ] Description is 40-80 words
- [ ] Description is in third person (no "I" or "you")
- [ ] Starts with activation directive ("Use this skill when...")
- [ ] Contains 3+ specific trigger symptoms/tasks in user vocabulary
- [ ] Contains 2-4 quoted casual phrases users might type
- [ ] Contains at least one "Do NOT use for..." boundary
- [ ] Names the correct alternative for excluded request types
- [ ] No vocabulary overlap >60% with sibling skill descriptions
- [ ] MCP tool references use `ServerName:tool_name` format

### For coordinators:
- [ ] Description covers the entire domain ("ANY frontend issue")
- [ ] Uses "ALWAYS" or "entry point" language
- [ ] Lists all sub-domains the suite covers
- [ ] Classification table has contrastive "NOT to" column
- [ ] Keyword shortcuts cover the most common 80% of requests
- [ ] Ambiguity handling defined (ask user or default route)

### For specialists in a suite:
- [ ] Description references the coordinator ("loaded BY the coordinator")
- [ ] Description is narrower than coordinator (specific niche, not broad domain)
- [ ] Early redirect check is Step 1 of the procedure
- [ ] Negative boundaries point to specific sibling skills by name

### For CLAUDE.md:
- [ ] Skill suite listed with domain description
- [ ] Coordinator-first routing directive present
- [ ] Context-dependent activation notes (frameworks, patterns used)
- [ ] Cross-suite priority order defined (if multiple suites)

### For development workflow:
- [ ] Skill developed using Claude A/B workflow (§4.4)
- [ ] Claude B tested on real tasks (not just eval cases)
- [ ] Navigation patterns observed and documented (§4.5)
- [ ] Trigger eval cases cover all 6 categories (§3.4-3.5)
- [ ] Navigation eval cases created for complex file structures (§3.7)
- [ ] Eval metrics meet targets (§3.8)
- [ ] Description refined through iterative loop (§4.1)

---

## Appendix A: Trigger Reliability Quick Reference

```
┌──────────────────────────────────────────────────────────┐
│         TRIGGER RELIABILITY v1.1 QUICK REFERENCE         │
├──────────────────────────────────────────────────────────┤
│                                                           │
│  DESCRIPTION FORMULA                                      │
│  [Activation directive]                                   │
│  + [Positive triggers in user vocabulary]                 │
│  + [2-4 quoted casual phrases]                            │
│  + [Negative boundaries naming alternatives]              │
│  = 40-80 words, third person, no "I"/"you"               │
│                                                           │
│  ACTIVATION BOOSTERS                                      │
│  ✓ Start with "Use this skill when..." or "ALWAYS use"   │
│  ✓ Include both technical and casual vocabulary           │
│  ✓ Quoted phrases: "it looks wrong", "broken on mobile"  │
│  ✓ Coordinator: "ANY", "ALL", "entry point"              │
│  ✓ CLAUDE.md: list skills with domain descriptions       │
│                                                           │
│  ROUTING PRECISION                                        │
│  ✓ Coordinator: contrastive table (route to / NOT to)    │
│  ✓ Coordinator: keyword shortcuts for common terms       │
│  ✓ Specialist: "Do NOT use for X → use Y instead"        │
│  ✓ Specialist: early redirect check as Step 1            │
│  ✓ CLAUDE.md: coordinator-first directive                │
│                                                           │
│  THREE EVAL DIMENSIONS                                    │
│  Trigger evals .... Does it activate? (≥95% rate)        │
│  Output evals ..... Is the result correct?               │
│  Navigation evals . Does it read the right files?        │
│                                                           │
│  TRIGGER EVAL METRICS (targets)                           │
│  Activation rate ............ ≥95%                        │
│  Correct routing rate ....... ≥90%                        │
│  Acceptable routing rate .... ≥95%                        │
│  False positive rate ........ ≤5%                         │
│  Bypass rate ................ ≤10%                        │
│                                                           │
│  DEVELOPMENT WORKFLOW                                     │
│  Claude A designs → Claude B tests → observe → refine    │
│                                                           │
│  REFINEMENT LOOP                                          │
│  Write → eval → analyze failures → update → re-eval      │
│  Silent miss → add vocabulary                             │
│  Wrong skill → add contrastive pairs                      │
│  Over-trigger → add negative boundaries                   │
│  Bypass → strengthen CLAUDE.md directive                  │
│                                                           │
└──────────────────────────────────────────────────────────┘
```
