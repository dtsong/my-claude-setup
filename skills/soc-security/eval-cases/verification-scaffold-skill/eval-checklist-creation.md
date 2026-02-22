# Eval Case: Checklist Creation — Security Review Checklist with Coverage Annotations

## Metadata
- **Case ID:** VS-003
- **Tier:** 2 (medium)
- **Skill Route:** verification-scaffold-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Create a security review checklist from these threat findings. I need it formatted for our pre-tapeout security review gate. Include coverage annotations showing which threats are covered by Tier 1 assertions, which have Tier 2 NL properties only, and which are Tier 3 spec-only.",
  "context": "Upstream ThreatFindings from TM-2026-008 (Fuse Controller, Automotive SoC):",
  "threat_findings": [
    {
      "id": "TF-TM-2026-008-001",
      "title": "OTP fuse read-back of programmed secrets",
      "strideCategory": "Information Disclosure",
      "severity": "CRITICAL",
      "confidenceTier": "GROUNDED",
      "attackSurface": "key-management",
      "verificationMethod": "SVA",
      "description": "An attacker with debug access can read back programmed key fuses through the fuse controller APB interface if read-protect bits are not set."
    },
    {
      "id": "TF-TM-2026-008-002",
      "title": "Fuse programming voltage glitch enabling double-program",
      "strideCategory": "Tampering",
      "severity": "CRITICAL",
      "confidenceTier": "INFERRED",
      "attackSurface": "fault-injection",
      "verificationMethod": "test",
      "description": "An attacker with physical access can glitch the programming voltage to enable double-programming of one-time-programmable fuses, altering device identity or security configuration."
    },
    {
      "id": "TF-TM-2026-008-003",
      "title": "Lifecycle state transition bypass via fuse FSM corruption",
      "strideCategory": "Elevation of Privilege",
      "severity": "HIGH",
      "confidenceTier": "GROUNDED",
      "attackSurface": "boot-chain",
      "verificationMethod": "SVA",
      "description": "An attacker can corrupt the lifecycle FSM to skip from DEVELOPMENT to PRODUCTION_LOCKED state transition requirements, deploying debug-enabled production devices."
    },
    {
      "id": "TF-TM-2026-008-004",
      "title": "Fuse sense amplifier timing side-channel",
      "strideCategory": "Information Disclosure",
      "severity": "MEDIUM",
      "confidenceTier": "SPECULATIVE",
      "attackSurface": "side-channel",
      "verificationMethod": "test",
      "description": "An attacker with EM probe access can observe differential timing of fuse sense amplifier settling to distinguish programmed vs. unprogrammed fuses."
    },
    {
      "id": "TF-TM-2026-008-005",
      "title": "Cross-domain information flow via shared fuse bus",
      "strideCategory": "Information Disclosure",
      "severity": "HIGH",
      "confidenceTier": "INFERRED",
      "attackSurface": "bus-access-control",
      "verificationMethod": "formal-analysis",
      "description": "Non-secure bus masters can observe fuse read data intended for the secure domain due to insufficient bus isolation on the shared APB fuse read path."
    }
  ]
}
```

## Expected Output
A verification checklist formatted for pre-tapeout review with:
- Traceability table mapping every threat to a verification item and tier
- Coverage annotations (Tier 1/2/3) with clear visual distinction
- Gap analysis showing which threats lack automated verification
- Caveat block appropriate for a tapeout gate review audience

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Traceability table present with columns: Threat ID, Severity, Confidence, VI ID, Tier, Status
- [ ] All 5 threats mapped to verification items (no threats dropped)
- [ ] TF-001: Tier 1 (SVA, access control gate pattern)
- [ ] TF-002: Tier 3 (physical fault injection, NO SVA)
- [ ] TF-004: Tier 3 (side-channel, NO SVA)
- [ ] Coverage gap analysis explicitly identifies Tier 3 items as lacking automated verification

### Should Pass (partial credit)
- [ ] TF-003: Tier 1 (SVA, FSM transition guard)
- [ ] TF-005: Tier 2 or Tier 3 (formal information flow analysis, not expressible as simple SVA)
- [ ] Caveat block tailored to pre-tapeout gate review context (not generic boilerplate)
- [ ] Confidence propagation correct: TF-004 SPECULATIVE upstream caps verification confidence at SPECULATIVE
- [ ] Checklist includes review actions for Tier 3 items (what methodology, who reviews, what evidence)

### Bonus
- [ ] Checklist groups items by attack surface for the review board's consumption
- [ ] Coverage percentage calculated (e.g., "3/5 threats have Tier 1 or Tier 2 coverage; 2/5 require out-of-band verification")
- [ ] Skill recommends specific tools for Tier 3 gaps (GLIFT for information flow TF-005, DPA workbench for TF-004)

## Raw Trace Log
