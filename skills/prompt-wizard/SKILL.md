---
name: "Prompt Wizard"
description: "Interactive wizard to craft effective prompts using Claude Code best practices"
triggers:
  - "prompt wizard"
  - "craft prompt"
  - "help me write a prompt"
  - "improve my prompt"
user_invocable: true
---

# /prompt-wizard - Craft Effective Prompts

An interactive wizard that applies Claude Code best practices to help you craft effective prompts for any task.

## Scope Constraints

- Read-only conversational skill: interviews user and generates prompt text
- Does not read, modify, or create project files
- Does not execute code or run any tools beyond user interaction

## Input Sanitization

- All user inputs (task descriptions, scope, context): free text, reject null bytes
- File paths referenced in context: reject `..` traversal, null bytes, and shell metacharacters
- URLs in external docs: validate well-formed URL format

## Modes

### 1. Create Mode (Default)
Walk through an interview to build a well-structured prompt from scratch.

### 2. Analyze Mode
Share an existing prompt and get suggestions for improvement.

---

## Interview Flow (Create Mode)

When the user invokes `/prompt-wizard`, run through these questions using the AskUserQuestion tool. Gather all answers before generating the final prompt.

### Step 1: Task Type

**Question:** "What type of task do you need help with?"

| Option | Description |
|--------|-------------|
| Feature | Add new functionality |
| Bug Fix | Fix broken behavior |
| Refactor | Improve code structure |
| Test | Write or improve tests |
| Documentation | Write docs or comments |
| Research | Explore codebase or investigate |

### Step 2: Complexity Level

**Question:** "How complex is this task?"

| Option | Description |
|--------|-------------|
| Simple | Single file, straightforward change |
| Medium | Multiple files, clear requirements |
| Complex | Architectural changes, many files |
| Unknown | Need to investigate first |

### Step 3: Verification Criteria

**Question:** "How should the result be verified?" (Multi-select)

| Option | Description |
|--------|-------------|
| Tests pass | Existing or new tests should pass |
| Type checks | TypeScript compilation succeeds |
| Visual check | UI looks correct in browser |
| Manual test | Specific manual verification steps |
| Builds successfully | No build errors |

### Step 4: Context Gathering

**Question:** "What context should Claude have?" (Multi-select)

| Option | Description |
|--------|-------------|
| Specific files | List files Claude should read |
| Error messages | Include error output |
| Screenshots | Reference visual examples |
| External docs | URLs to reference |
| Existing patterns | Point to similar code |

Based on selections, ask follow-up questions:
- If "Specific files": "Which files should Claude examine?"
- If "Error messages": "Please paste the error output"
- If "Screenshots": "Provide path or describe what it shows"
- If "External docs": "What URLs should Claude reference?"
- If "Existing patterns": "Where are similar implementations?"

### Step 5: Scope Boundaries

**Question:** "What should be IN scope for this task?"
(Free-form text input)

**Question:** "What should be OUT of scope?" (optional)
(Free-form text input)

### Step 6: Additional Materials (Optional)

**Question:** "Do you have any additional context to share?"

| Option | Description |
|--------|-------------|
| None | Ready to generate prompt |
| Code snippet | Include specific code |
| Requirements doc | Link to specs |
| Previous attempt | What was tried before |

---

## Generated Prompt Template

After gathering all answers, generate a prompt using this structure:

```markdown
## Task
[Clear, specific description of what needs to be done]

## Task Type
[Feature/Bug Fix/Refactor/Test/Documentation/Research]

## Context
[Files to read, patterns to follow, relevant background]

## Requirements
- [Specific requirement 1]
- [Specific requirement 2]
- [...]

## In Scope
[What this task includes]

## Out of Scope
[What this task explicitly excludes]

## Verification
[How to verify the task is complete]
- [ ] [Verification step 1]
- [ ] [Verification step 2]

## Additional Context
[Error messages, screenshots, links, etc.]
```

---

## Analyze Mode

When user shares an existing prompt or says "analyze my prompt":

### Analysis Checklist

Evaluate the prompt against these best practices:

1. **Specificity** - Is the task clear and specific?
2. **Context** - Are relevant files/patterns mentioned?
3. **Scope** - Are boundaries defined (in/out of scope)?
4. **Verification** - Is there a clear definition of done?
5. **Complexity** - Is the scope appropriate (not too broad)?
6. **Actionability** - Can Claude start immediately?

### Improvement Suggestions

Provide concrete suggestions to improve weak areas:

| Issue | Suggestion |
|-------|------------|
| Vague task | "Instead of 'fix the bug', try 'fix the login form validation that allows empty emails'" |
| No context | "Add: 'Examine src/auth/ for existing patterns'" |
| No scope | "Add what's in/out of scope to prevent over-engineering" |
| No verification | "Add: 'Verify by running npm test and checking the login UI'" |
| Too broad | "Break into smaller tasks: 1) investigate, 2) implement, 3) test" |

---

## Best Practices Applied

This wizard implements patterns from Claude Code best practices:

1. **"Let Claude Interview You"** - Structured questions gather complete context
2. **Clear Verification Criteria** - Every prompt includes how to verify success
3. **Scope Boundaries** - Explicit in/out of scope prevents scope creep
4. **Task Decomposition** - Complex tasks broken into manageable pieces
5. **Context Provision** - Relevant files and patterns explicitly mentioned

---

## Output Format

```
## Task
Fix login form to trim whitespace from email input.

## Task Type
Bug Fix

## Context
- Read `src/auth/login.ts` — authentication logic
- Read `src/components/LoginForm.tsx` — form component

## Requirements
- Trim whitespace before validation
- Show error for invalid email format

## Verification
- [ ] Existing tests pass
- [ ] Manual test: login with spaces succeeds
```

## Example Output

### Input (from interview)
- Task Type: Bug Fix
- Complexity: Medium
- Verification: Tests pass, Manual test
- Context: Specific files (src/auth/login.ts, src/components/LoginForm.tsx)
- Error: "Login fails silently when email contains spaces"
- In Scope: Fix validation, add error message
- Out of Scope: Refactoring auth system, adding new auth methods

### Generated Prompt

```markdown
## Task
Fix the login form to properly handle emails with leading/trailing spaces. Currently, login fails silently when users accidentally include spaces in their email.

## Task Type
Bug Fix

## Context
- Read `src/auth/login.ts` - authentication logic
- Read `src/components/LoginForm.tsx` - form UI component
- Follow existing validation patterns in these files

## Requirements
- Trim whitespace from email input before validation
- Show clear error message if email format is invalid
- Preserve existing validation for other fields

## In Scope
- Fix email validation in login form
- Add user-facing error message for invalid emails

## Out of Scope
- Refactoring the auth system
- Adding new authentication methods
- Changing the form styling

## Verification
- [ ] Existing tests pass (`npm test`)
- [ ] Manual test: Login with " user@example.com " (spaces) succeeds
- [ ] Manual test: Invalid email shows error message
- [ ] No TypeScript errors

## Additional Context
**Error reproduction:**
1. Go to /login
2. Enter " test@example.com " (with spaces)
3. Click login - fails silently with no error message
```

---

## Usage

```bash
# Start the wizard
/prompt-wizard

# Analyze an existing prompt
/prompt-wizard analyze
# Then paste your prompt when asked
```
