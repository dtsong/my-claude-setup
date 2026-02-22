# Eval Case: Tier Assignment — Simple Threat Set

## Metadata
- **Case ID:** VS-001
- **Tier:** 1 (simple)
- **Skill Route:** verification-scaffold-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Assign verification tiers to these threat findings from our boot ROM controller threat model and generate a verification scaffold plan.",
  "context": "Upstream ThreatFindings from TM-2026-005 (Boot ROM Controller, IoT SoC):",
  "threat_findings": [
    {
      "id": "TF-TM-2026-005-001",
      "title": "Unauthorized write to boot ROM address space",
      "strideCategory": "Tampering",
      "severity": "CRITICAL",
      "confidenceTier": "GROUNDED",
      "attackSurface": "bus-access-control",
      "verificationMethod": "SVA",
      "description": "An attacker with bus master access can issue write transactions to the boot ROM address range, corrupting immutable boot code."
    },
    {
      "id": "TF-TM-2026-005-002",
      "title": "Boot sequence stage skip via FSM corruption",
      "strideCategory": "Elevation of Privilege",
      "severity": "CRITICAL",
      "confidenceTier": "GROUNDED",
      "attackSurface": "boot-chain",
      "verificationMethod": "SVA",
      "description": "An attacker with fault injection capability can corrupt the boot FSM state, skipping authentication stages and booting unsigned firmware."
    },
    {
      "id": "TF-TM-2026-005-003",
      "title": "Boot measurement value leakage via debug port",
      "strideCategory": "Information Disclosure",
      "severity": "HIGH",
      "confidenceTier": "INFERRED",
      "attackSurface": "debug-interface",
      "verificationMethod": "review",
      "description": "An attacker with JTAG access can read boot stage measurement values from debug registers, enabling firmware fingerprinting."
    },
    {
      "id": "TF-TM-2026-005-004",
      "title": "Side-channel leakage during boot key comparison",
      "strideCategory": "Information Disclosure",
      "severity": "MEDIUM",
      "confidenceTier": "SPECULATIVE",
      "attackSurface": "side-channel",
      "verificationMethod": "test",
      "description": "An attacker with physical proximity can observe timing or power variations during boot key comparison to recover key material."
    }
  ]
}
```

## Expected Output
A verification scaffold plan with correct tier assignments:
- TF-001: Tier 1 (SVA, address range check)
- TF-002: Tier 1 (SVA, FSM transition guard)
- TF-003: Tier 2 or Tier 3 (review-based, debug interface)
- TF-004: Tier 3 (side-channel, physical measurement required)

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] TF-001 assigned to Tier 1 (verificationMethod=SVA, address range check pattern)
- [ ] TF-002 assigned to Tier 1 (verificationMethod=SVA, FSM transition guard pattern)
- [ ] TF-004 assigned to Tier 3 (side-channel always Tier 3 per assignment rules)
- [ ] Tier 3 items explicitly noted as NO SVA with rationale
- [ ] Confidence propagation correct: TF-004 (SPECULATIVE upstream) cannot produce anything above SPECULATIVE verification confidence

### Should Pass (partial credit)
- [ ] TF-003 assigned to Tier 2 or Tier 3 with justification (debug interface review is ambiguous)
- [ ] Output follows the Verification Scaffold Plan format with counts per tier
- [ ] Priority ordering: CRITICAL items (TF-001, TF-002) listed before HIGH (TF-003) before MEDIUM (TF-004)
- [ ] RTL signal status noted as NOT AVAILABLE, all assertions marked [TEMPLATE]

### Bonus
- [ ] Skill notes that TF-001 and TF-002 are both CRITICAL/GROUNDED and should be the highest priority for assertion development
- [ ] Skill identifies that TF-003 could be partially checked with SVA (debug register access control) even though the upstream method says "review"

## Raw Trace Log
