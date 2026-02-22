---
name: formalize
description: Formalize security properties in TLA+ from upstream analysis findings
---

# /soc-security:formalize

Formalize security properties as TLA+ specifications. This command activates the tlaplus-security-skill to translate security findings from any upstream skill into precise mathematical specifications with model checking guidance.

## Usage

```
/soc-security:formalize
/soc-security:formalize "Formalize the TDISP state machine safety property"
/soc-security:formalize --property safety --source TF-2026-001
```

## What Happens

1. **Property extraction:** Claude identifies security properties to formalize from upstream findings (threat model, microarch, SCA, kernel, or emerging HW findings).
2. **TLA+ module construction:** Builds a TLA+ specification with state variables, type invariants, initial state, and next-state relation.
3. **Security property formalization:** Expresses each property as a TLA+ temporal formula — safety as invariants, liveness with fairness assumptions, information flow as noninterference.
4. **Model checking guidance:** Provides TLC configuration — constants, symmetry sets, state constraints, estimated state space, and abstraction suggestions.
5. **Output generation:** Produces a formal security specification with explicit assumptions and limitations.

## Property Types

| Type | TLA+ Construct | Example |
|------|---------------|---------|
| Safety | `Invariant` or `[][...]_vars` | "Device never enters RUN without authentication" |
| Liveness | `<>[]P` or `[]<>P` with fairness | "Every authentication request eventually gets a response" |
| Invariant | State predicate | "Key material is never in plaintext outside the crypto boundary" |
| Fairness | `WF_vars(Action)` or `SF_vars(Action)` | "The scheduler eventually grants CPU to every domain" |
| Information flow | Noninterference formalization | "High-security actions do not affect low-security observations" |

## Output

The specification is saved as a `formal-security-spec` DocumentEnvelope with FormalSecSpec entities, each including TLA+ module text, assumptions list, limitations list, and TLC configuration.

## Next Step

After formalization:
- Run TLC model checker on the generated specification to verify properties
- Use violation traces (if any) to identify real security issues in the design
- Feed verified properties back into `/soc-security:verify` for implementation-level verification

## Skill Reference

This command invokes the [tlaplus-security-skill](../tlaplus-security-skill/SKILL.md). See also:
- [tlaplus-security-patterns.md](../tlaplus-security-skill/references/tlaplus-security-patterns.md) — TLA+ security pattern library
- [model-checking-guide.md](../tlaplus-security-skill/references/model-checking-guide.md) — TLC model checking guide
- [formal-methods.md](../shared-references/soc-security/domain-ontology/formal-methods.md) — formal methods ontology
