# Skill Governance Specification v1.3

## Overview

This specification defines the standards, patterns, and enforcement mechanisms
for authoring, validating, and deploying AI agent skills. It applies to skills
targeting Claude Code, OpenAI Codex, and any SKILL.md-compatible agent platform.

This document is the **single source of truth**. All pipeline scripts, hooks,
and tooling derive their rules from this spec.

### Changes from v1.0 → v1.1 → v1.1.1 → v1.2

- Per-file token budgets reclassified from hard limits to **guideline targets**
- Suite context load ceiling remains the **only hard budget limit**
- Pre-commit budget checks changed from blocking to **warning**
- Added guidance on when to exceed budgets and how to document it
- Rebalanced enforcement to prioritize structural integrity over compression
- Added quality-over-compression principle to writing rules
- (v1.1.1) Security added as priority #2 in the optimization hierarchy
- (v1.1.1) Security rules added to enforcement tier mapping (all Hard tier)
- (v1.1.1) Security hook runs first in pre-commit and CI pipelines
- (v1.1.1) Full security spec referenced from §8.2 (`SKILL-SECURITY-SPEC.md`)
- (v1.2) Model tier annotations replaced with model routing configuration
- (v1.2) Frontmatter extended with `model` block for per-skill tier preferences
- (v1.2) Model routing spec referenced for budget-aware degradation

### Changes in v1.3

- Added **Degrees of Freedom** framework for calibrating instruction specificity (§4.5)
- Added **"Claude Already Knows This"** as first conciseness test (§4.1)
- Added **third-person description** requirement for frontmatter (§3.1)
- Added **one-level-deep reference rule** to prevent partial file reads (§2.5)
- Added **feedback loops and progress tracking** patterns (§5.1, §5.4)
- Added **verifiable intermediate outputs** (plan-validate-execute) pattern (§5.1)
- Added **compaction resilience** patterns for long procedures (§5.4)
- Added **time-sensitive content** deprecation rules (§4.6)
- Added **script robustness** requirements alongside security (§5.5)
- Added **MCP tool reference** format requirements (§9.4)
- Added **visual analysis** as a quality pattern (§5.1)
- Added **platform feature** integration: `context: fork` and shell preprocessing (§9.5)
- Updated enforcement tier mapping with new validation rules (§8.2)
- Updated pre-commit hooks with new checks (§8.3)

---

## 1. Core Principles

### 1.1 The Optimization Hierarchy

When authoring skills, these priorities apply in order. Higher priorities
override lower ones when they conflict.

1. **Output quality** — The skill produces correct, useful results
2. **Security** — The skill cannot be used to exfiltrate data, inject instructions, or escalate privileges
3. **Structural integrity** — Progressive loading, isolation, and handoff contracts
4. **Token efficiency** — Minimize instruction and execution token cost
5. **Compression** — Keep individual files compact

Most of the real token savings come from #3 (not loading multiple specialists)
and #4 (smart tool usage, targeted reading, structured handoffs). Aggressive
compression (#5) delivers diminishing returns and can degrade #1 if it removes
context that helps the agent make good decisions.

### 1.2 Budget Philosophy

**Guideline targets** set a reasonable default size for each file type. They
prevent unbounded growth and encourage structural discipline (extracting
checklists to reference files, moving logic to scripts). Exceeding a guideline
is acceptable when the extra content demonstrably improves agent performance.

**The context load ceiling** is the one hard limit. It caps the maximum tokens
of skill instructions present in the agent's context window at any point during
execution. This is the constraint that directly protects reasoning capacity.

**The distinction matters.** A specialist skill at 2,200 words that includes
edge case reasoning and produces better results is preferable to one squeezed
to 1,500 words that loses critical context. But three such skills loaded
simultaneously at 6,600 words would crowd out code and reasoning — which is
why the ceiling exists.

---

## 2. Skill Architecture

### 2.1 Progressive Loading Model

```
Layer 1: Coordinator          Always in context        Target: ≤800 tokens
          ↓ routes to
Layer 2: Specialist Skill     Loaded on demand          Target: ≤2,000 tokens
          ↓ references
Layer 3: Reference Files      Loaded within a step     Target: ≤1,500 tokens

Hard ceiling on simultaneous load: ≤5,500 tokens
```

**Rules:**
- Only one Layer 2 skill is loaded at a time
- Layer 3 files are loaded conditionally within a procedure step
- Eval cases and templates are never loaded during execution

### 2.2 Skill Types and Budget Targets

| Type | Description | Target | Warn At | Hard Limit |
|------|-------------|--------|---------|------------|
| **Coordinator** | Routes to specialists. Has a `skills/` subdirectory. | ≤800 tokens (~600 words) | >800 tokens | None (ceiling applies) |
| **Specialist** | Full procedure for one task type. Inside `skills/`. | ≤2,000 tokens (~1,500 words) | >2,000 tokens | None (ceiling applies) |
| **Standalone** | Single-purpose skill, no suite. | ≤2,000 tokens (~1,500 words) | >2,000 tokens | None (ceiling applies) |
| **Reference** | Checklist, lookup table, or pattern library. | ≤1,500 tokens (~1,100 words) | >1,500 tokens | None (ceiling applies) |
| **Suite ceiling** | Coordinator + largest specialist + largest reference | — | — | **≤5,500 tokens** |

Token estimation: `tokens ≈ words × 1.33`

### 2.3 When to Exceed a Target

Exceeding a per-file target is acceptable when:

- The extra content is **contextual reasoning** that helps the agent understand
  *why* a step matters, not just *what* to do — and removing it degrades output quality
- The content is **edge case handling** that prevents common failure modes you've
  observed in eval runs
- The content is **examples of good vs bad output** that calibrate the agent's judgment
- The file has been through eval iterations and the current length reflects what's
  needed for consistent performance

When exceeding a target, document it in `pipeline/config/budgets.json`:

```json
{
  "overrides": {
    "skills/frontend-qa/skills/ui-bug-investigator": {
      "specialist_max_words": 1800,
      "reason": "Diagnostic branching logic + edge case notes for hydration mismatches. Eval pass rate dropped from 85% to 60% when compressed to 1500 words."
    }
  }
}
```

### 2.4 Directory Structures

**Skill Suite:**
```
suite-name/
├── SKILL.md                        # Coordinator (Layer 1)
├── skills/
│   └── specialist-name/
│       ├── SKILL.md                # Specialist (Layer 2)
│       └── references/             # Reference files (Layer 3)
│           └── checklist.md
├── scripts/                        # Executable automation
├── templates/                      # Output templates
└── eval-cases/                     # Never loaded during execution
    ├── evals.json
    ├── trigger-evals.json
    └── cases/
```

**Standalone Skill:**
```
skill-name/
├── SKILL.md                        # Combined (Layer 1+2)
├── references/
├── scripts/
└── eval-cases/
```

### 2.5 Isolation and Reference Rules (Hard — Always Enforced)

- Specialist skills must NOT reference other specialists' SKILL.md or reference files
- Inter-skill data passes through the coordinator's handoff protocol as structured data
- Eval cases must NOT reside inside skill directories that could be auto-loaded
- Scripts are executed, not read into context

**One-level-deep reference rule:** All referenced files must be directly
reachable from the file the agent is currently executing. Reference files must
NOT contain references to other reference files. Claude may use partial reads
(e.g., `head -100`) on deeply nested references, resulting in incomplete
information and silent failures.

```
✅ SKILL.md → references/checklist.md          (1 hop — always fully read)
✅ SKILL.md → references/patterns.md           (1 hop — always fully read)
❌ SKILL.md → references/advanced.md → references/details.md   (2 hops — may be partially read)
```

If a reference file needs to point to additional detail, that detail should be
inlined or the SKILL.md should reference both files directly.

**Table of contents for large references:** Reference files over 100 lines
must include a table of contents at the top. This ensures the agent can see
the full scope of available content even when previewing, and can navigate
directly to the relevant section.

---

## 3. File Format Standards

### 3.1 SKILL.md Frontmatter

Required fields:
```yaml
---
name: skill-name          # Kebab-case identifier (max 64 chars)
                           # Lowercase letters, numbers, hyphens only
                           # No reserved words: "anthropic", "claude"
description: >            # Trigger description — when to use, what it does
  Comprehensive description with specific trigger phrases.
  Be slightly pushy about when to use this skill.
---
```

**Description requirements:**
- **Written in third person.** The description is injected into the system
  prompt alongside other skills' descriptions. Inconsistent point-of-view
  causes discovery problems.
  - ✅ "Processes Excel files and generates reports"
  - ✅ "Use this skill when the user reports visual bugs"
  - ❌ "I can help you process Excel files"
  - ❌ "You can use this to process Excel files"
- Minimum 20 words (Warn), target 40-80 words for reliable activation
- See `SKILL-TRIGGER-RELIABILITY-SPEC.md` for the full description formula

**Naming conventions:** Use gerund form (verb + -ing) for skill names. This
clearly describes the activity the skill provides.
- ✅ `processing-pdfs`, `analyzing-spreadsheets`, `debugging-css-layout`
- Acceptable: `pdf-processing`, `process-pdfs`
- ❌ `helper`, `utils`, `tools`, `documents`

Optional fields:
```yaml
version: 1.0.0
model:
  preferred: haiku|sonnet|opus       # Default model tier
  acceptable: [haiku, sonnet]        # Models producing acceptable results
  minimum: haiku                     # Lowest viable tier
  allow_downgrade: true              # System can downgrade under budget pressure
  reasoning_demand: low|medium|high  # Informs degradation priority
```

See `SKILL-MODEL-ROUTING-SPEC.md` for the full model configuration schema,
budget-aware routing, and degradation cascade.

No other frontmatter fields are permitted.

### 3.2 Coordinator SKILL.md Structure

Must contain exactly five elements, nothing else:

1. **Purpose** — One sentence
2. **Classification logic** — Decision tree or conditional block
3. **Skill registry** — Table: name, path, one-line purpose, model tier
4. **Load directive** — "Read ONLY the relevant specialist SKILL.md"
5. **Handoff protocol** — What structured data passes between skills

### 3.3 Specialist SKILL.md Structure

```markdown
---
name: ...
description: ...
---

# Skill Name

## Scope Constraints
[What this skill can and cannot access]

## Inputs
[3-5 lines. Required vs optional marked.]

## Input Sanitization
[How user-provided values are validated before use in commands/paths]

## Procedure
[Numbered steps. Imperative by default. Degrees of freedom calibrated
per step (§4.5). Reference file loads as explicit steps. Feedback loops
where validation is needed (§5.4).]

## Output Format
[One compact example. Variations annotated inline.]

## Handoff
[2-3 lines. Structured data only, no raw files.]

## References
[Table: path, load condition, content summary.]
```

### 3.4 Reference File Structure

- No preamble, meta-instructions, or conclusions
- One item per line
- Organized under short category headers
- **Table of contents required for files >100 lines**
- Must NOT contain references to other reference files (one-level-deep rule, §2.5)

---

## 4. Writing Rules

### 4.1 The Conciseness Hierarchy

Apply these tests in order when reviewing skill content:

**Test 1: "Claude already knows this."** The model is already highly capable.
Only add context it doesn't already have. Challenge each paragraph:

- "Does Claude really need this explanation?"
- "Can I assume Claude knows what this technology is?"
- "Am I teaching the model something it already learned in training?"

A skill that explains what PDFs are, how flexbox works, or what imports do is
wasting tokens on knowledge the model already has. Cut the explanation; keep
only the project-specific context Claude can't know without being told.

```
❌ "PDF (Portable Document Format) files are a common file format that
    contains text, images, and other content. To extract text..."

✅ "Use pdfplumber for text extraction:
    ```python
    import pdfplumber
    with pdfplumber.open('file.pdf') as pdf:
        text = pdf.pages[0].extract_text()
    ```"
```

**Test 2: "If I remove this, does the agent perform worse?"** This is the
empirical test. When you've observed through evals that a piece of context
improves results, it belongs in the skill regardless of word count impact.

**Test 3: "Can this sentence earn its place?"** Every sentence should either
instruct a specific action, provide context that improves decision quality,
or prevent a known failure mode with a targeted note.

The goal is **information density**, not minimum word count.

### 4.2 Procedure Sections

- **Default to imperative sentences.** "Read the file. Check for `use client`. Record the result."
- **Add contextual reasoning when it affects decisions.** "Resolve barrel exports
  to source files — barrel exports via index.ts mask the real file path, which
  breaks downstream analysis if you stop at the re-export layer." The second half
  of this sentence costs 25 words but prevents a common failure mode.
- **Inline conditionals for branching.** "If X → do A. Otherwise → do B."
- **One example per output format.** No redundant schema descriptions alongside examples.
- **Notes for edge cases.** "Note: components using `usePathname` are always client
  components even if their file lacks `use client` — the hook forces the boundary."

### 4.3 What to Cut vs What to Keep

**Always cut:**
| Pattern | Why It's Wasteful |
|---------|-------------------|
| "It is important to..." | Preamble — just state the action |
| "Basically / essentially / fundamentally" | Filler — adds zero information |
| "In order to" | Verbose — "to" works identically |
| "Keep in mind that..." / "Please note that..." | Meta-instruction — convert to inline Note: |
| "Let's / we can / we should" | Conversational — use imperative |
| "Feel free to" / "Don't hesitate to" | Casual — remove entirely |
| Schema described in prose AND shown as example | Duplication — keep only the example |
| Explanations of well-known concepts | Claude already knows this — see §4.1 Test 1 |

**Keep when it improves agent decisions:**
| Pattern | Why It Earns Its Place |
|---------|------------------------|
| "X because Y" in a procedure step | Agent understands consequences of skipping |
| Edge case notes ("Note: watch for Z") | Prevents known failure modes |
| Short good-vs-bad examples | Calibrates agent judgment on ambiguous cases |
| "Stop here if X — this is the root cause" | Early termination saves tokens downstream |
| Fallback instructions ("If A fails, try B") | Prevents dead-end states |
| Project-specific context Claude can't infer | Only way to inject domain knowledge |

### 4.4 Model Tier Selection

Skills should declare their model requirements in frontmatter. Map reasoning
demand to tiers:

| Tier | reasoning_demand | Use Case | Cost Ratio |
|------|-----------------|----------|------------|
| `haiku` | low | Deterministic tracing, file ops, pattern matching | 1x |
| `sonnet` | medium | Classification, multi-factor decisions, standard coding | ~8x |
| `opus` | high | Complex debugging, architecture, novel problem solving | ~60x |

Coordinators default to haiku (routing doesn't require reasoning).
The cascade execution pattern (haiku classify → escalate if needed) is
the highest-leverage optimization for skills with variable complexity.

See `SKILL-MODEL-ROUTING-SPEC.md` for budget zones, degradation cascade,
user override knobs, and cost optimization patterns.

### 4.5 Degrees of Freedom

Not every procedure step needs the same level of specificity. Match instruction
rigidity to the task's fragility and variability.

**Low freedom (exact instructions, no deviation):**
Use when operations are fragile, error-prone, or destructive. The agent
follows the exact command with no adaptation.

```markdown
Step 3: Run migration.
  `python scripts/migrate.py --verify --backup`
  Do not modify the command or add additional flags.
```

**Medium freedom (preferred pattern, some adaptation):**
Use when a known-good approach exists but context may require variation.
Provide the default with an escape hatch.

```markdown
Step 2: Extract text.
  Use pdfplumber (default). If the PDF is scanned/image-based,
  fall back to pdf2image + pytesseract for OCR.
```

**High freedom (direction, not prescription):**
Use when multiple approaches are valid and the best choice depends on context
the skill author can't predict. Give criteria, not commands.

```markdown
Step 4: Review for potential issues.
  Check for edge cases, error handling gaps, and deviations from
  project conventions. Prioritize issues by impact.
```

**Analogy:** A narrow bridge with cliffs on both sides needs exact instructions
(low freedom). An open field with no hazards needs general direction and trusts
the agent to find the best route (high freedom).

**Default assumption:** When uncertain, choose medium freedom. It provides
enough structure to prevent common failures while allowing the agent to
adapt to context it can see but you can't.

**Calibrate per step, not per skill.** A single procedure might need low
freedom for a database migration step, medium freedom for a data transformation
step, and high freedom for a review step.

### 4.6 Time-Sensitive Content

Do not include information that will become outdated without clear deprecation
signals. Skills referencing specific library versions, API endpoints, or
framework behaviors create invisible maintenance debt.

**Rules:**
- Do not use temporal references ("If you're doing this before August 2025...")
- Version-specific instructions must note which version they target
- Deprecated approaches go in a clearly marked section, not inline

**Pattern for handling deprecated approaches:**

```markdown
## Current method
Use the v2 endpoint: `api.example.com/v2/messages`

## Deprecated patterns
<details>
<summary>Legacy v1 API (deprecated 2025-08)</summary>
The v1 API used: `api.example.com/v1/messages` — no longer supported.
</details>
```

The collapsed section provides historical context without cluttering the
main instructions or confusing the agent about which approach to use.

---

## 5. Engineering Patterns

Patterns to embed in skills for quality, efficiency, and tool intelligence.
These patterns typically deliver more token savings during execution than
compressing the skill instructions themselves.

### 5.1 Quality Patterns

| ID | Pattern | When to Use |
|----|---------|-------------|
| Q1 | **Pre-flight context gathering** — Read project config before acting | Code generation, modification skills |
| Q2 | **Convention mirroring** — Read exemplar files, match style | Code generation skills |
| Q3 | **Output contracts** — Checkable conditions the output must satisfy | Skills whose output feeds other skills |
| Q4 | **Self-verification loop** — Check own work before presenting | All skills producing actionable output |
| Q5 | **Confidence signaling** — Rate findings HIGH/MEDIUM/LOW | Diagnostic, analytical skills |
| Q6 | **Negative space documentation** — Report what was checked and ruled out | Diagnostic, audit, review skills |
| Q7 | **Feedback loops** — Run validator → fix errors → repeat until clean | Skills with verifiable intermediate steps |
| Q8 | **Verifiable intermediate outputs** — Plan file → validate → execute | Batch operations, destructive changes |
| Q9 | **Visual analysis** — Convert output to image, verify visually | Frontend, PDF, layout, chart generation |

**Q7: Feedback loops.** When a procedure includes validation, structure it
as a loop rather than a linear sequence. This catches errors iteratively:

```markdown
Step 3: Edit document XML.
Step 4: Validate: `python scripts/validate.py unpacked_dir/`
  - If validation fails → review errors, fix, return to Step 4.
  - Only proceed when validation passes.
Step 5: Rebuild document.
```

The pattern is: action → validate → fix → re-validate → proceed. Without the
loop structure, the agent treats validation as a one-shot check and moves on
even when errors remain.

**Q8: Verifiable intermediate outputs.** For complex or destructive operations,
have the agent produce a structured plan file, validate it with a deterministic
script, then execute. This prevents the agent from applying 50 changes based
on its reasoning when a script can verify the plan is valid first.

```markdown
Step 2: Generate change plan.
  Produce `changes.json` with every modification:
  ```json
  [{"file": "path", "action": "modify", "field": "X", "old": "A", "new": "B"}]
  ```

Step 3: Validate plan.
  `python scripts/validate_changes.py changes.json`
  If validation fails → fix plan, re-validate.

Step 4: Apply validated plan.
  `python scripts/apply_changes.py changes.json`
```

This is particularly valuable for batch file modifications, form filling,
database updates, and any operation where rollback is expensive.

**Q9: Visual analysis.** When inputs or outputs can be rendered as images,
have the agent convert and visually verify. Claude's vision capabilities catch
layout problems, rendering errors, and visual regressions that text-based
analysis misses.

```markdown
Step 5: Visual verification.
  Convert output to image: `python scripts/render_preview.py output.pdf`
  Examine the rendered image. Verify layout matches expected format.
  If visual issues found → return to Step 3.
```

### 5.2 Efficiency Patterns (High Token Impact)

| ID | Pattern | Typical Savings |
|----|---------|-----------------|
| E1 | **Targeted file reading** — Read sections, not whole files | 500-2,000 tokens/file |
| E2 | **Progressive detail** — Shallow scan, then deep dive on relevant items | 1,000-5,000 tokens/run |
| E3 | **Output token discipline** — Diffs not files, no problem restatement | 500-3,000 tokens/response |
| E4 | **Structured handoffs** — JSON between skills, not prose | 200-800 tokens/handoff |
| E5 | **Early termination** — Exit when the answer is clear | 1,000-10,000 tokens/run |
| E6 | **Cache-friendly ordering** — Stable context prefix for KV-cache hits | Latency reduction |

### 5.3 Tool Intelligence Patterns

| ID | Pattern | Typical Savings |
|----|---------|-----------------|
| T1 | **Tool selection heuristics** — Right tool for each job | 100-500 tokens/operation |
| T2 | **Batched tool calls** — One call, many operations | 200-1,000 tokens/batch |
| T3 | **Pre-flight validation** — Cheap checks before expensive operations | 1,000-5,000 tokens on failed runs |
| T4 | **Fallback chains** — Plan B, C, D for tool failures | Eliminates dead-end user round-trips |
| T5 | **Output parsing discipline** — Filter tool output at source | 500-5,000 tokens/command |
| T6 | **Capability detection** — Detect available tools before planning | Prevents wasted procedure branches |
| T7 | **Incremental verification** — Verify per change, not at end | Cheaper failure isolation |

### 5.4 Resilience Patterns

| ID | Pattern | When to Use |
|----|---------|-------------|
| R1 | **Progress tracking** — Visible checklist the agent updates | Multi-step procedures (>5 steps) |
| R2 | **Compaction resilience** — Survive context window resets | Long procedures, multi-turn skills |
| R3 | **State recovery** — Resume from last known good state | Destructive operations, long pipelines |

**R1: Progress tracking.** For procedures with more than 5 steps, include a
progress checklist that the agent copies into its response and checks off as
it works. This creates visible state that both the user and agent can reference.

```markdown
## Procedure

Copy this checklist and update as you complete each step:
```
Progress:
- [ ] Step 1: Analyze input
- [ ] Step 2: Generate plan
- [ ] Step 3: Validate plan
- [ ] Step 4: Execute changes
- [ ] Step 5: Verify output
- [ ] Step 6: Generate report
```

Step 1: Analyze input.
  ...
```

**R2: Compaction resilience.** When the context window fills, Claude compacts
the conversation — replacing detailed history with a summary. If a skill is
mid-procedure when compaction occurs, the agent loses detailed step context.

Skills with long procedures should include recovery guidance:

```markdown
Note: If you've lost context of previous steps (e.g., after context
compaction), check the progress checklist above. Resume from the last
unchecked item. Re-read relevant reference files if needed.
```

The progress checklist (R1) is the primary compaction resilience mechanism —
the checked-off items survive as visible state even after the conversation
around them is summarized.

**R3: State recovery.** For destructive or irreversible operations, write
state to a recovery file at each checkpoint:

```markdown
Step 2: Save checkpoint.
  Write current state to `.skill-checkpoint.json`:
  `{"completed_steps": [1], "last_output": "...", "timestamp": "..."}`
  If resuming after interruption, read checkpoint and skip completed steps.
```

### 5.5 Script Robustness Requirements

Skills that include executable scripts must meet robustness requirements in
addition to the security requirements in `SKILL-SECURITY-SPEC.md`.

**Principle: Scripts solve problems; they don't punt to the agent.** A script
that crashes with an unhandled exception forces the agent to spend tokens
diagnosing the failure and generating a workaround. A script that handles
the error and provides a clear message lets the agent move forward.

**Requirements:**

- **Explicit error handling.** Scripts must handle foreseeable errors (file not
  found, permission denied, malformed input) with clear error messages, not
  bare exceptions.

```python
# ❌ Punt to agent
def process_file(path):
    return open(path).read()

# ✅ Handle errors
def process_file(path):
    try:
        with open(path) as f:
            return f.read()
    except FileNotFoundError:
        print(f"Error: {path} not found. Create the file first or check the path.")
        sys.exit(1)
    except PermissionError:
        print(f"Error: Cannot read {path}. Check file permissions.")
        sys.exit(1)
```

- **No undocumented constants.** Every magic number must have a comment
  explaining why that value was chosen. If you don't know the right value,
  the agent won't either.

```python
# ❌ Magic numbers
TIMEOUT = 47
RETRIES = 5

# ✅ Documented constants
REQUEST_TIMEOUT = 30   # HTTP requests typically complete within 30s
MAX_RETRIES = 3        # Most intermittent failures resolve by retry 2
```

- **Verbose error messages for agent self-correction.** Error messages should
  include enough context for the agent to fix the issue without reading the
  script source:

```python
# ❌ Vague
raise ValueError("Invalid field")

# ✅ Actionable
raise ValueError(
    f"Field '{name}' not found. Available fields: {', '.join(available_fields)}"
)
```

- **Dependency documentation.** Scripts must list required packages in SKILL.md
  and include installation commands. Do not assume packages are available.

```markdown
## Dependencies
Install required packages: `pip install pdfplumber pypdf`
```

### 5.6 Composition Matrix

| Skill Type | Must Have | Should Have | Consider |
|------------|-----------|-------------|----------|
| Code Generation | Q1, Q2, Q3, T1 | Q4, E1, E3, R1 | E6 |
| Diagnosis | E2, E5, Q5, Q6 | T2, T4, T5 | E3 |
| Fix & Verify | T3, T7, T4, T6, Q7 | Q4, E3, Q8 | T2 |
| Batch Operations | Q8, R1, R3, T7 | Q7, T3, E3 | R2 |
| Analysis/Mapping | E1, T2, T1, Q3 | E2, E4 | E6 |
| Test Generation | Q1, Q2, T6, Q4 | Q3, T4 | E3 |
| Frontend/Visual | Q1, Q9, T7, Q4 | Q7, R1 | E2 |
| Long Procedures | R1, R2, R3, Q7 | Q4, E5 | E3 |
| Coordinator | E4, E5, T6 | E3 | — |

**Key insight**: Patterns E1-E5 and T1-T5 typically save more tokens during
skill execution than any amount of SKILL.md compression. The resilience
patterns (R1-R3) prevent wasted work from interruptions. Prioritize embedding
these patterns over squeezing word count.

---

## 6. Refactoring Patterns

When a file significantly exceeds its target, apply in order:

1. **Extract checklists** — Move >10 items to `references/`. Savings: 300-800 tokens.
2. **Apply Test 1 (§4.1)** — Remove explanations of things Claude already knows. Savings: 200-1,000 tokens.
3. **Cut filler** — Remove patterns from the "Always cut" table (§4.3). Savings: 200-500 tokens.
4. **Deduplicate output specs** — Keep only the example. Savings: 150-400 tokens.
5. **Script mechanical work** — Move deterministic logic to scripts. Variable savings.
6. **Decompose** — Split into two specialists with coordinator. Last resort.

**Do NOT cut:**
- Contextual reasoning that prevents known failure modes
- Edge case notes validated by eval results
- Examples that calibrate agent judgment
- Fallback instructions that prevent dead-end states
- Progress checklists (R1) — these are resilience infrastructure, not content

When refactoring, re-run eval cases to confirm the refactored version performs
at least as well as the original. If eval pass rate drops, the cut removed
necessary content — restore it and document the override.

---

## 7. Eval Case Standards

### 7.1 Case Structure

```markdown
# Eval Case: [Name]

## Metadata
- Case ID, Tier (1-3), Route/Input, Estimated components

## Input
[JSON block with the skill's input parameters]

## Expected Output
[Concrete, checkable expectations — tables, trees, specific values]

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] [Specific, verifiable assertion]

### Should Pass (partial credit)
- [ ] [Secondary assertion]

### Bonus
- [ ] [Nice-to-have assertion]
```

### 7.2 Case Selection

- 5-7 cases per skill
- Tiered: 1-2 simple, 2-3 medium, 1-2 complex
- Must collectively cover all key scenarios for the skill's domain
- Include a "Raw Trace Log" section for traceability

### 7.3 Using Evals to Justify Budgets

Eval results are the arbiter of budget decisions. When a skill exceeds its
target, the process is:

1. Run evals at the current (over-target) length → record pass rate
2. Refactor to target length using the patterns in §6
3. Run evals again → compare pass rate
4. If pass rate holds → keep the shorter version
5. If pass rate drops → restore the longer version, document the override with the eval data

This makes budget decisions empirical rather than arbitrary.

### 7.4 Model-Aware Eval Runs

Skills should be tested with all model tiers declared in their `model.acceptable`
list. What works perfectly for Opus might need more detail for Haiku.

- Run eval cases at each acceptable tier
- If a skill passes on Opus but fails on Sonnet, the skill needs more
  explicit instructions (lower degrees of freedom) to compensate for
  reduced capability at the cheaper tier
- Document per-tier pass rates alongside budget overrides

This is how degradation adaptations (see `SKILL-MODEL-ROUTING-SPEC.md`) get
validated empirically rather than assumed.

---

## 8. Enforcement Tiers

### 8.1 Tier Classification

Every rule in this spec belongs to one of three enforcement tiers:

| Tier | Behavior | Purpose |
|------|----------|---------|
| **Hard** | Blocks commit and merge | Prevents structural breakage |
| **Warn** | Visible warning, does not block | Encourages best practices |
| **Info** | Reported in analysis, no warning | Awareness and tracking |

### 8.2 Rule-to-Tier Mapping

| Rule | Tier | Rationale |
|------|------|-----------|
| No sensitive path references without annotation | **Hard** | Prevents credential exposure |
| No prompt injection patterns without annotation | **Hard** | Prevents safety override attempts |
| No dangerous commands in scripts without declaration | **Hard** | Prevents arbitrary code execution |
| Script checksums match scripts.lock | **Hard** | Prevents tampering between review and execution |
| Frontmatter has required fields | **Hard** | Skill won't trigger without name + description |
| Referenced files exist on disk | **Hard** | Agent will fail at runtime if reference is missing |
| No cross-specialist references | **Hard** | Violates isolation, causes instruction blending |
| Suite context load ≤ ceiling | **Hard** | Directly protects reasoning capacity |
| Eval cases outside skill directories | **Hard** | Prevents accidental context pollution |
| Scripts are executable | **Hard** | Agent will fail at runtime otherwise |
| Commit message format | **Hard** | Enables changelog generation and filtered diffs |
| Reference files don't reference other reference files | **Hard** | One-level-deep rule prevents partial reads |
| Input sanitization before command use | **Warn** | Prevents injection through user input |
| Scope boundary alignment | **Warn** | Detects skills operating outside their purpose |
| Per-file token budget exceeded | **Warn** | Guideline — may be justified by quality needs |
| Prose patterns in procedure sections | **Warn** | Suggests tightening, but context may be valuable |
| Description in third person | **Warn** | Prevents discovery problems from POV inconsistency |
| Description ≥20 words | **Warn** | Short descriptions have low activation rates |
| Description starts with activation directive | **Warn** | Passive descriptions reduce trigger reliability |
| Description contains negative boundary | **Warn** | Missing boundaries cause over-triggering |
| Scripts have explicit error handling | **Warn** | Unhandled errors waste agent tokens on diagnosis |
| MCP tool references use fully qualified names | **Warn** | Bare tool names cause "tool not found" errors |
| No temporal references without version context | **Warn** | Creates invisible maintenance debt |
| Near budget (>90% of target) | **Info** | Awareness that headroom is shrinking |
| Unknown frontmatter fields | **Info** | Might indicate platform-specific additions |
| Reference file >100 lines without TOC | **Info** | Large files benefit from navigation aids |

See `SKILL-SECURITY-SPEC.md` for the full threat model and static analysis rules.

### 8.3 Pipeline Requirements

**Pre-Commit Hooks (Local, <2s):**

| Hook | Tier | What It Checks |
|------|------|----------------|
| `skill-security` | Hard | Sensitive paths, injection patterns, dangerous commands, script checksums |
| `skill-frontmatter` | Hard | YAML structure, required fields |
| `skill-references` | Hard | Referenced files exist on disk; no reference-to-reference chains |
| `skill-isolation` | Hard | No cross-specialist references |
| `skill-context-load` | Hard | Suite worst-case ≤ ceiling |
| `skill-triggers` | Warn | Description length, activation directive, third person, negative boundaries, vocabulary overlap |
| `skill-token-budget` | Warn | Word/token counts vs targets |
| `skill-prose-check` | Warn | Explanatory prose in procedures; well-known concept explanations |
| `skill-scripts` | Warn | Error handling, documented constants, dependency declarations |
| `skill-commit-msg` | Hard | Conventional commit format |

Note: Security hook runs first — fail fast on critical findings.

**CI Stage 1: Lint & Validate (Every Push, <30s)**
- Security scan (same checks as pre-commit, safety net for `--no-verify`)
- All hard-tier structural checks
- Budget report as step summary on PRs

**CI Stage 2: Static Analysis (PRs, <2min)**
- Security cross-file analysis (SKILL.md → reference file payload chains)
- Diff-aware security scan (flag newly introduced security patterns)
- Scope boundary heuristic analysis
- Reference depth analysis (flag reference-to-reference chains)
- Pattern compliance, portability check, context load report
- Post analysis as PR comment
- Critical security findings block merge

**CI Stage 3: Eval Execution (Merge / Manual, <30min)**
- Run eval cases against skills
- Grade against rubrics
- Detect regressions against stored baselines
- Run trigger eval cases (activation rate, routing accuracy)
- Run navigation evals where configured (see Trigger Reliability Spec §3.5)
- Upload results as artifacts

**CI Stage 4: Publish (Release Tags)**
- Package changed skills
- Create release
- Sync to target locations

### 8.4 Commit Message Convention

```
skill(name): description          — new skill or major change
skill-fix(name): description      — bug fix
skill-ref(name): description      — refactor (no behavior change)
skill-eval(name): description     — eval case changes
skill-docs(name): description     — documentation only
chore(pipeline): description      — pipeline/tooling changes
```

---

## 9. Cross-Platform Compatibility

### 9.1 Shared Elements (No Adaptation Needed)

- SKILL.md body content (procedures, checklists, decision trees)
- Reference files
- Scripts (bash/python)
- Directory structure and organization
- Eval cases and grading criteria
- Token budgets and progressive loading architecture

### 9.2 Platform-Specific Adaptations

| Element | Claude Code | Codex |
|---------|-------------|-------|
| Project instructions | `CLAUDE.md` | `AGENTS.md` |
| Skill metadata UI | Frontmatter only | `agents/openai.yaml` |
| Explicit invocation | Via description trigger | `$skill-name` or `/skills` |
| Implicit invocation control | Always on | `allow_implicit_invocation` in yaml |
| Model routing | Haiku / Sonnet / Opus | Codex-Spark / GPT-5.x-Codex |

### 9.3 Portability Rules

- Use generic language ("project instructions file") or note both filenames
- Avoid platform-specific tool syntax in SKILL.md bodies
- Use `python3` not `python` in scripts
- Keep `agents/openai.yaml` as an optional addition, not a requirement

### 9.4 MCP Tool References

Skills that invoke MCP (Model Context Protocol) tools must use fully qualified
tool names to avoid "tool not found" errors when multiple MCP servers are
available.

**Format:** `ServerName:tool_name`

```markdown
# ✅ Fully qualified — always resolves
Use the BigQuery:bigquery_schema tool to retrieve table schemas.
Use the GitHub:create_issue tool to create issues.

# ❌ Bare tool name — fails when multiple servers present
Use the bigquery_schema tool to retrieve table schemas.
```

Where `BigQuery` and `GitHub` are MCP server names, and `bigquery_schema` and
`create_issue` are the tool names within those servers.

**Validation rule (Warn tier):** Any skill referencing MCP tools should use
the `ServerName:tool_name` format. The `check_triggers.py` hook scans for
bare tool name patterns (e.g., "use the X tool" without a colon-separated
server prefix).

### 9.5 Platform Feature Integration (Claude Code)

Claude Code provides platform features that skills can leverage for improved
isolation and dynamic context. These are optional — skills should work without
them — but provide significant benefits when available.

**`context: fork` — Subagent isolation:**

Skills can declare `context: fork` in frontmatter to run in a forked subagent
with a separate context window. This provides actual isolation rather than
instruction-level isolation.

```yaml
---
name: deep-analysis
description: ...
context: fork
agent: code    # or: explore, plan
---
```

Benefits: specialist can't pollute the main conversation context; failures
in the specialist don't corrupt the parent session; natural token budget
enforcement (the fork has its own context window).

Evaluate whether your coordinator/specialist architecture should use `context: fork`
for specialists that perform extensive reading or generate large outputs.

**Shell preprocessing (`!command` syntax):**

Skills can use shell command preprocessing to inject live data before Claude
sees the prompt. The command runs first, its output replaces the placeholder,
and Claude receives actual data rather than instructions to gather it.

```markdown
## Current State
!git diff --cached --stat
!npm test 2>&1 | tail -20

## Procedure
Based on the staged changes and test results above, ...
```

This eliminates an entire tool-call round-trip for gathering context the skill
always needs. Use it for: current git state, test results, build output,
environment configuration, or any data the skill needs before it starts reasoning.

Note: shell preprocessing is Claude Code-specific. For cross-platform skills,
include the preprocessing as an optional first step with a fallback:

```markdown
Step 0 (if shell preprocessing unavailable): Run `git diff --cached --stat`
and `npm test 2>&1 | tail -20`. Record the output for subsequent steps.
```

---

## Appendix A: Quick Reference Card

```
┌──────────────────────────────────────────────────────────┐
│          SKILL GOVERNANCE v1.3 QUICK REFERENCE           │
├──────────────────────────────────────────────────────────┤
│                                                           │
│  PRIORITY ORDER                                           │
│  1. Quality  2. Security  3. Structure  4. Efficiency     │
│                                                           │
│  CONCISENESS HIERARCHY                                    │
│  Test 1: Claude already knows this → cut                  │
│  Test 2: Removing it hurts eval scores → keep             │
│  Test 3: Sentence earns its place (action/context/fix)    │
│                                                           │
│  DEGREES OF FREEDOM                                       │
│  Low: Fragile ops → exact commands, no deviation          │
│  Medium: Known pattern → default + escape hatch           │
│  High: Context-dependent → criteria, not commands         │
│  Calibrate per step, not per skill.                       │
│                                                           │
│  SECURITY (blocks commits)                                │
│  ✗ No credential/key/dotfile access without annotation    │
│  ✗ No injection patterns without annotation               │
│  ✗ No undeclared dangerous commands in scripts            │
│  ✓ Script checksums locked in scripts.lock                │
│  ✓ Scope Constraints section in every skill               │
│  ✓ Input Sanitization for user-provided values            │
│  Escape hatch: # SECURITY: <justification>                │
│                                                           │
│  BUDGET TARGETS (guidelines — warn, don't block)          │
│  Coordinator ................. ≤800 tokens (~600 words)   │
│  Specialist / Standalone ..... ≤2,000 tokens (~1,500 w)   │
│  Reference ................... ≤1,500 tokens (~1,100 w)   │
│                                                           │
│  HARD LIMIT                                               │
│  Suite context load ceiling .. ≤5,500 tokens              │
│                                                           │
│  STRUCTURAL RULES (blocks commits)                        │
│  ✓ Valid frontmatter with name + description              │
│  ✓ Description in third person                            │
│  ✓ All referenced files exist on disk                     │
│  ✓ One-level-deep references (no ref→ref chains)          │
│  ✓ No cross-specialist references                         │
│  ✓ Eval cases outside skill directories                   │
│  ✓ Suite context load under ceiling                       │
│                                                           │
│  DESCRIPTION QUALITY (warns on commit)                    │
│  ✓ ≥20 words (target 40-80)                              │
│  ✓ Starts with activation directive                       │
│  ✓ Contains negative boundaries                           │
│  ✓ Third person (not "I" or "you")                        │
│  ✓ MCP tools use ServerName:tool_name format              │
│                                                           │
│  RESILIENCE (for long procedures)                         │
│  ✓ Progress checklist for >5 step procedures              │
│  ✓ Compaction recovery note for multi-turn skills         │
│  ✓ State checkpoint for destructive operations            │
│                                                           │
│  SCRIPTS (warns on commit)                                │
│  ✓ Explicit error handling (no bare exceptions)           │
│  ✓ Documented constants (no magic numbers)                │
│  ✓ Verbose error messages for agent self-correction       │
│  ✓ Dependencies listed with install commands              │
│                                                           │
│  BUDGET DISPUTES                                          │
│  Run evals at both lengths. Eval pass rate decides.       │
│  Run evals at each model tier in acceptable list.         │
│  Document overrides with evidence in budgets.json.        │
│                                                           │
│  ENFORCEMENT TIERS                                        │
│  Hard = blocks commit  |  Warn = visible warning          │
│  Info = reported only  |  See §8.2 for full mapping       │
│                                                           │
└──────────────────────────────────────────────────────────┘
```

---

## Appendix B: Budget Configuration Schema

```json
{
  "coordinator_max_words": 600,
  "coordinator_max_tokens": 800,
  "specialist_max_words": 1500,
  "specialist_max_tokens": 2000,
  "reference_max_words": 1100,
  "reference_max_tokens": 1500,
  "standalone_max_words": 1500,
  "standalone_max_tokens": 2000,
  "max_simultaneous_tokens": 5500,
  "overrides": {
    "skills/path/to/specific-skill": {
      "specialist_max_words": 1800,
      "reason": "Documented justification with eval data"
    }
  }
}
```
