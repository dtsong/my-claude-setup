---
name: "Edge Case Enumeration"
department: "skeptic"
description: "[Council] Systematic edge case discovery using structured enumeration techniques. Used during council/academy deliberation only."
version: 1
triggers:
  - "edge case"
  - "boundary"
  - "empty state"
  - "concurrent"
  - "race condition"
  - "validation"
  - "malformed"
  - "overflow"
  - "unicode"
  - "null"
---

# Edge Case Enumeration

## Purpose
Systematically discover edge cases for proposed features using structured enumeration techniques.

## Inputs
- Feature specification or user story being analyzed
- Input fields and their expected types/formats
- State transitions and lifecycle of the feature
- User roles and permission model

## Process

### Step 1: Identify Input Boundaries
For each input: document the type, valid range, length constraints, format requirements, and whether it's required or optional.

### Step 2: Apply Boundary Value Analysis
For each input, enumerate:

- **Empty/null/undefined**: What happens with no input, null, undefined, empty string, whitespace-only?
- **Minimum and maximum values**: At the boundary, one below, one above
- **Just inside and just outside valid ranges**: Off-by-one errors, boundary transitions
- **Special characters**: Unicode (CJK, Arabic, RTL text), emoji, zero-width characters, combining characters, null bytes
- **Extremely long inputs**: Past max length, at max length, strings that look like numbers

### Step 3: Enumerate State Combinations
- **Empty state**: First use, no data created yet, fresh account
- **Partial state**: Incomplete setup, mid-operation interruption, partially filled forms
- **Full state**: At capacity limits, pagination boundaries, maximum items reached
- **Stale state**: Cached data from previous version, outdated references, deleted dependencies

### Step 4: Analyze Concurrent Scenarios
- **Same user simultaneous ops**: Double submit, rapid clicks, multiple tabs, back button after submit
- **Different users on same resource**: Concurrent edits, delete while viewing, permission change during session
- **Operations during deployment/migration**: Request in flight during deploy, schema change mid-operation

### Step 5: Consider Temporal Edge Cases
- **Timezone boundaries**: UTC midnight, DST transitions, user in different timezone than server
- **Session expiry mid-operation**: Token expires during long form fill, refresh token rotation
- **Long-running operations**: Timeout during processing, progress loss on reconnect, orphaned background jobs

### Step 6: Map Permission Edge Cases
- **Role transitions**: Admin demoted to user during active session, role upgrade without re-login
- **Shared resources with mixed permissions**: Viewer accessing editor's link, public/private toggle
- **Deleted/suspended user data**: References to deleted users, suspended account data visibility, orphaned content

## Output Format

### Edge Case Table

#### Input Edge Cases
| Input | Edge Case | Expected Behavior | Test Priority |
|---|---|---|---|
| [Field] | Empty/null | [Behavior] | P0/P1/P2 |
| [Field] | Max length + 1 | [Behavior] | P0/P1/P2 |

#### State Edge Cases
| State | Edge Case | Expected Behavior | Test Priority |
|---|---|---|---|
| Empty | No items, first load | [Behavior] | P0/P1/P2 |
| Stale | Cached reference to deleted item | [Behavior] | P0/P1/P2 |

#### Concurrency Edge Cases
| Scenario | Edge Case | Expected Behavior | Test Priority |
|---|---|---|---|
| Double submit | Rapid form submission | [Behavior] | P0/P1/P2 |

#### Temporal Edge Cases
| Scenario | Edge Case | Expected Behavior | Test Priority |
|---|---|---|---|
| Session expiry | Token expires mid-save | [Behavior] | P0/P1/P2 |

#### Permission Edge Cases
| Scenario | Edge Case | Expected Behavior | Test Priority |
|---|---|---|---|
| Role change | Admin demoted during session | [Behavior] | P0/P1/P2 |

### Priority Key
- **P0**: Will break in production, must handle before launch
- **P1**: Likely to occur, causes poor UX or data issues
- **P2**: Unlikely but possible, handle if time permits

## Quality Checks
- [ ] Every input field has boundary value analysis
- [ ] Empty/null/error states are covered for all inputs
- [ ] Concurrent scenarios are addressed for shared resources
- [ ] At least 5 edge cases per category (input, state, concurrency, temporal, permission)
- [ ] Each edge case has defined expected behavior
- [ ] P0 cases are flagged for immediate implementation

## Evolution Notes
<!-- Observations appended after each use -->
