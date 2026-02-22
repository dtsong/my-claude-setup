# Eval Case: Multi-Threat Input — Mixed-Priority Threats with SPECULATIVE Findings

## Metadata
- **Case ID:** VS-004
- **Tier:** 3 (complex)
- **Skill Route:** verification-scaffold-skill
- **Estimated Complexity:** high

## Input
```json
{
  "user_prompt": "Process this full threat model output into a verification scaffold. Pay special attention to the SPECULATIVE findings — I want to understand how they flow through to verification confidence. Also flag any findings where the upstream confidence limits what we can claim about verification coverage.",
  "context": "Upstream ThreatFindings from TM-2026-012 (DICE Layer 2 Firmware Measurement Engine, Data Center SoC). Full DocumentEnvelope with 10 findings across all confidence tiers.",
  "threat_findings": [
    {
      "id": "TF-TM-2026-012-001",
      "title": "Firmware measurement bypass via TCB layer skip",
      "strideCategory": "Elevation of Privilege",
      "severity": "CRITICAL",
      "confidenceTier": "GROUNDED",
      "attackSurface": "boot-chain",
      "verificationMethod": "SVA",
      "description": "An attacker who controls Layer 1 firmware can skip the Layer 2 measurement step, extending trust to unmeasured firmware.",
      "standardsReferences": ["DICE 1.1 Section 6.2"]
    },
    {
      "id": "TF-TM-2026-012-002",
      "title": "CDI derivation with stale measurement register",
      "strideCategory": "Tampering",
      "severity": "CRITICAL",
      "confidenceTier": "GROUNDED",
      "attackSurface": "key-management",
      "verificationMethod": "SVA",
      "description": "The measurement register retains a previous firmware hash when the CDI derivation starts, producing a CDI that corresponds to old firmware."
    },
    {
      "id": "TF-TM-2026-012-003",
      "title": "SPDM measurement report includes unverified layers",
      "strideCategory": "Spoofing",
      "severity": "HIGH",
      "confidenceTier": "GROUNDED",
      "attackSurface": "bus-access-control",
      "verificationMethod": "simulation",
      "description": "The SPDM GET_MEASUREMENTS response includes hash values from layers that were not actually measured by the DICE engine."
    },
    {
      "id": "TF-TM-2026-012-004",
      "title": "Measurement register not locked after CDI derivation",
      "strideCategory": "Tampering",
      "severity": "HIGH",
      "confidenceTier": "GROUNDED",
      "attackSurface": "key-management",
      "verificationMethod": "SVA",
      "description": "After CDI derivation completes, the measurement register remains writable, allowing later firmware to retroactively alter the measurement."
    },
    {
      "id": "TF-TM-2026-012-005",
      "title": "Layer transition timing enables measurement TOCTOU",
      "strideCategory": "Tampering",
      "severity": "HIGH",
      "confidenceTier": "INFERRED",
      "attackSurface": "boot-chain",
      "verificationMethod": "SVA",
      "description": "A narrow timing window between firmware measurement and CDI derivation allows a DMA-capable agent to modify firmware after measurement but before the CDI locks in the hash."
    },
    {
      "id": "TF-TM-2026-012-006",
      "title": "Alias key pair generation from low-entropy TRNG",
      "strideCategory": "Information Disclosure",
      "severity": "HIGH",
      "confidenceTier": "INFERRED",
      "attackSurface": "key-management",
      "verificationMethod": "test",
      "description": "The TRNG used for alias key pair generation may have insufficient entropy during early boot when voltage rails are unstable."
    },
    {
      "id": "TF-TM-2026-012-007",
      "title": "Cross-layer information flow via shared measurement bus",
      "strideCategory": "Information Disclosure",
      "severity": "MEDIUM",
      "confidenceTier": "INFERRED",
      "attackSurface": "bus-access-control",
      "verificationMethod": "formal-analysis",
      "description": "Layer N+1 firmware can observe Layer N measurement values on the shared internal bus, leaking firmware identity information across trust layers."
    },
    {
      "id": "TF-TM-2026-012-008",
      "title": "Power glitch during CDI derivation corrupts output",
      "strideCategory": "Tampering",
      "severity": "MEDIUM",
      "confidenceTier": "SPECULATIVE",
      "attackSurface": "fault-injection",
      "verificationMethod": "test",
      "description": "A voltage glitch during the HMAC computation for CDI derivation could produce a predictable or all-zero CDI."
    },
    {
      "id": "TF-TM-2026-012-009",
      "title": "Timing side-channel in hash comparison during measurement verification",
      "strideCategory": "Information Disclosure",
      "severity": "MEDIUM",
      "confidenceTier": "SPECULATIVE",
      "attackSurface": "side-channel",
      "verificationMethod": "test",
      "description": "Variable-time comparison of firmware hash against expected measurement could leak information about the expected hash value."
    },
    {
      "id": "TF-TM-2026-012-010",
      "title": "Debug port access to intermediate DICE state",
      "strideCategory": "Information Disclosure",
      "severity": "LOW",
      "confidenceTier": "SPECULATIVE",
      "attackSurface": "debug-interface",
      "verificationMethod": "review",
      "description": "JTAG debug access during DICE Layer 2 execution could expose intermediate CDI values, UDS derivatives, or measurement state."
    }
  ]
}
```

## Expected Output
A complete verification scaffold for 10 findings demonstrating:
- Correct tier assignment across all findings
- Confidence propagation with SPECULATIVE upstream correctly capping downstream
- Mixed output: SVA templates (Tier 1), NL properties (Tier 2), spec-only (Tier 3)
- Explicit treatment of how SPECULATIVE confidence limits verification claims

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] All 10 findings mapped to verification items (none dropped)
- [ ] Tier assignments correct: TF-001, TF-002, TF-004, TF-005 -> Tier 1; TF-003 -> Tier 2; TF-006, TF-008, TF-009 -> Tier 3
- [ ] SPECULATIVE findings (TF-008, TF-009, TF-010) produce verification items with confidence capped at SPECULATIVE regardless of tier
- [ ] Tier 3 items (side-channel, fault injection) have NO SVA generated — explicit refusal with rationale
- [ ] Confidence propagation table showing upstream tier -> downstream confidence for every item
- [ ] Coverage mapping table with all 10 findings present

### Should Pass (partial credit)
- [ ] TF-007 assigned to Tier 2 or Tier 3 (information flow analysis is at minimum Tier 2)
- [ ] TF-010 assigned to Tier 2 or Tier 3 (review-based, debug interface)
- [ ] SVA templates for Tier 1 findings include INTENT and DOES NOT CHECK annotations
- [ ] Tier 2 NL properties include test scenarios (normal, attack, edge case)
- [ ] Caveat block specifically addresses the SPECULATIVE confidence limitation on coverage claims
- [ ] Priority ordering places CRITICAL/GROUNDED findings first

### Bonus
- [ ] Explicit narrative explaining that 3/10 findings are SPECULATIVE and cannot support verification coverage claims in a compliance context
- [ ] Skill identifies that TF-005 (TOCTOU) is a particularly challenging Tier 1 assertion because it involves timing between two asynchronous events
- [ ] Downstream handoff notes for compliance-pipeline-skill flag which verification items have limited evidentiary value due to SPECULATIVE upstream

## Raw Trace Log
