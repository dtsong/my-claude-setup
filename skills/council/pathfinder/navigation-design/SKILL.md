---
name: navigation-design
department: "pathfinder"
description: "Use when designing navigation architecture for mobile or cross-platform features including screen hierarchy, deep linking schemes, and state preservation strategies. Covers stack navigation, modal flows, universal links, and process death recovery. Do not use for platform guideline compliance (use platform-audit) or hardware API integration (use device-integration)."
version: 1
triggers:
  - "navigation"
  - "deep link"
  - "universal link"
  - "tab bar"
  - "stack"
  - "routing"
  - "back button"
  - "state restoration"
  - "screen flow"
---

# Navigation Design

## Purpose

Design the navigation architecture for a mobile or cross-platform feature, including screen hierarchy, deep linking scheme, state preservation strategy, and transition animations.

## Scope Constraints

Reads feature requirements, user flows, and existing navigation code for architectural analysis. Does not modify files or execute code. Does not interact with app runtimes or navigation frameworks directly.

## Inputs

- Feature requirements and user flows
- Target platforms and framework (React Navigation, Flutter Navigator, SwiftUI NavigationStack)
- Existing navigation structure (if extending)
- Deep linking requirements (universal links, custom schemes)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Map the screen hierarchy
- [ ] Step 2: Define navigation patterns
- [ ] Step 3: Design deep linking scheme
- [ ] Step 4: State preservation strategy
- [ ] Step 5: Transition design
- [ ] Step 6: Edge case handling

### Step 1: Map the Screen Hierarchy

Identify all screens the feature requires. Organize into a hierarchy:
- **Root screens** (accessible from tab bar or drawer)
- **Stack screens** (pushed onto a navigation stack from a root)
- **Modal screens** (presented modally — confirmation dialogs, full-screen overlays)
- **Nested stacks** (sub-flows that have their own back history)

### Step 2: Define Navigation Patterns

For each transition between screens, specify:
- **Push/Pop** (standard stack navigation, swipe-back gesture)
- **Modal present/dismiss** (bottom sheet, full-screen modal)
- **Tab switch** (preserves stack state per tab)
- **Deep link entry** (navigates directly to a specific screen with params)

### Step 3: Design Deep Linking Scheme

Map feature screens to URL patterns:
- Universal link format: `https://app.example.com/feature/:id`
- Custom scheme format: `myapp://feature/:id`
- Define parameter handling and fallback behavior (web redirect, app install prompt)
- Handle authentication requirements for deep-linked screens

### Step 4: State Preservation Strategy

Design how navigation state survives:
- **Tab switches** — Each tab preserves its own stack
- **Backgrounding** — Navigation stack is serialized and restored
- **Process death** — Full state restoration from persistent storage
- **In-progress forms** — Draft data survives navigation events

### Step 5: Transition Design

Specify animations for each navigation event:
- Standard push/pop (platform default is usually correct)
- Modal presentation style (sheet, full-screen, custom)
- Shared element transitions (if applicable)
- Reduced-motion alternatives

### Step 6: Edge Case Handling

Address navigation edge cases:
- Back button from a deep link (where does the user go?)
- Notification tap while already on the target screen
- Multiple deep links in quick succession
- Authentication-gated screens (redirect to login, then return)

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what feature is being designed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

```markdown
# Navigation Architecture

## Screen Map
```
Tab Bar
├── Home (root)
│   ├── Feature Detail (push)
│   │   └── Edit Modal (modal)
│   └── Settings (push)
├── Search (root)
│   └── Result Detail (push)
└── Profile (root)
```

## Navigation Table
| From | To | Type | Gesture | Animation |
|------|----|------|---------|-----------|
| Home | Feature Detail | Push | Tap row | Slide left |
| Feature Detail | Edit | Modal | Tap button | Slide up |

## Deep Link Map
| URL Pattern | Target Screen | Params | Auth Required |
|-------------|--------------|--------|---------------|
| /feature/:id | Feature Detail | id | No |
| /feature/:id/edit | Edit Modal | id | Yes |

## State Preservation
| Event | Strategy | Storage |
|-------|----------|---------|
| Tab switch | Preserve stack | Memory |
| Background | Serialize nav state | AsyncStorage |
| Process death | Full restoration | Persistent |

## Edge Cases
- [Edge case and handling strategy]
```

## Handoff

- Hand off to platform-audit if navigation patterns need validation against iOS HIG or Material Design guidelines.
- Hand off to device-integration if deep link handling depends on hardware APIs such as NFC or push notification integration.

## Quality Checks

- [ ] Every screen is reachable from at least one navigation path
- [ ] Deep links have fallback behavior for unauthenticated and uninstalled states
- [ ] State preservation handles backgrounding, process death, and tab switches
- [ ] Back button behavior is defined for every screen including deep link entry
- [ ] Navigation patterns match platform conventions (iOS push vs Android fragment)
- [ ] Reduced-motion alternatives are specified for custom transitions

## Evolution Notes
<!-- Observations appended after each use -->
