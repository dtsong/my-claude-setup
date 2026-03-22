# Deepening Criteria

Evaluation rubric for identifying codebase architecture improvement opportunities. Based on concepts from "A Philosophy of Software Design" (John Ousterhout).

## Core Concept: Deep vs. Shallow Modules

A **deep module** has a small, simple interface hiding significant implementation complexity. A **shallow module** has a large or complex interface relative to its implementation — it shifts complexity to callers instead of absorbing it.

Goal: deepen shallow modules by simplifying their interfaces and absorbing more complexity internally.

## Criteria

### 1. Shallow Modules

**Signal:** Module exports many functions/classes but each does little. Callers must orchestrate multiple calls to accomplish one task. Passthrough methods that add no logic.

**Look for:**
- Files with 10+ exports where most are under 20 lines
- Functions that just forward to another function with minor param changes
- Classes where every method is a thin wrapper around a dependency
- "Manager" or "Service" classes that orchestrate but contain no logic

**Deepening action:** Merge related shallow modules into fewer, deeper ones. Combine passthrough layers. Move orchestration logic into the module that owns the data.

### 2. Unnecessary Abstractions

**Signal:** Abstraction layers that exist "just in case" rather than serving multiple concrete uses.

**Look for:**
- Interfaces with exactly one implementation
- Factory functions that create only one type
- Abstract base classes with a single subclass
- Generic wrappers around a specific library (when the library is unlikely to change)
- Separate "types" files re-exporting what could be co-located

**Deepening action:** Inline the abstraction. Use the concrete implementation directly. Extract an interface later when a second implementation actually appears.

### 3. Tight Coupling

**Signal:** Modules that cannot be understood, tested, or changed independently.

**Look for:**
- Circular imports (A imports B, B imports A)
- Modules importing 5+ siblings from the same directory
- Shared mutable state (global singletons, module-level variables mutated by multiple files)
- "Shotgun surgery" — changing one behavior requires touching 4+ files
- Test files that import from many unrelated source modules

**Deepening action:** Identify the real dependency direction and restructure. Extract shared concepts into a module that both depend on. Replace shared mutable state with explicit parameter passing.

### 4. Leaky Abstractions

**Signal:** Callers must understand internal implementation details to use a module correctly.

**Look for:**
- Functions that require callers to pass internal config or state objects
- Error messages that expose internal stack frames or implementation class names
- Return types that include internal data structures not documented in the API
- Comments warning "must call X before Y" — ordering dependencies that should be hidden

**Deepening action:** Hide internal details behind a simpler interface. Manage ordering internally. Return domain types, not implementation types.

### 5. Scattered Logic

**Signal:** Understanding one concept requires reading across many files with no clear home.

**Look for:**
- Business rules split across controller, service, validator, and model layers
- Feature logic spread across 5+ files with no unifying module
- Constants, types, and helpers for one feature living in generic "utils" or "shared" directories
- Pure functions extracted into separate files solely for testability

**Deepening action:** Co-locate related logic. Create a feature module that owns its types, validation, and business rules. Test through the module's public interface rather than extracting internals.

## Evaluation Output

For each candidate, assess:

| Dimension | Question |
|-----------|----------|
| **Depth ratio** | How much does the interface hide vs. expose? |
| **Change radius** | How many files must change for a typical feature in this area? |
| **Test clarity** | Is it obvious where and how to test this module? |
| **Newcomer cost** | How long to understand this area from scratch? |

Rate impact as **High** (eliminates confusion across the codebase), **Medium** (clarifies one area), or **Low** (minor cleanup).
