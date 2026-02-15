---
name: physical-design-security
department: "forge"
description: "Use when reviewing physical implementation security for power domain coupling, timing-related leakage, clock domain crossing issues, and layout-level information exposure. Covers DPA/SPA resistance, EM emanation, fault injection countermeasures, and probing defenses. Do not use for RTL logic review (use rtl-security-review) or microarchitectural attack analysis (use microarch-analysis)."
version: 1
triggers:
  - "physical design"
  - "power domain"
  - "clock domain"
  - "timing closure"
  - "layout"
  - "tape-out"
  - "DPA"
  - "power analysis"
  - "EM emanation"
  - "fault injection"
---

# Physical Design Security

## Purpose
Review physical implementation for security vulnerabilities arising from power domain coupling, timing-related leakage, clock domain crossing issues, and layout-level information exposure.

## Scope Constraints

Reads physical design files, floorplans, and hardware specifications. Does not modify design files or execute EDA tools. Does not access foundry-specific restricted data.

## Inputs
- Physical design constraints and floorplan
- Power domain architecture (voltage islands, power gating, level shifters)
- Clock domain architecture (clock trees, domain crossings, gating)
- Security-sensitive blocks and their physical placement
- Threat model for physical attacks (invasive, semi-invasive, non-invasive)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Step 1: Review Physical Implementation Constraints
Map the physical design from a security perspective:
- Identify security-critical blocks and their placement relative to chip boundaries
- Review floorplan for isolation between security domains
- Check that sensitive blocks are not adjacent to untrusted I/O or analog blocks
- Verify that security-critical paths meet timing with margin (no hold violations that could cause glitches)

### Step 2: Identify Timing-Related Leakage
Assess timing paths for information leakage:
- Variable-latency operations in security-critical paths (data-dependent timing)
- Setup/hold violations that create intermittent behavior exploitable by fault injection
- Timing margin on security-critical paths (can voltage/temperature manipulation cause failures?)
- Early/late path analysis for security-relevant signals

### Step 3: Check Power Domain Isolation
Review power architecture for security:
- Power domain boundaries align with security domain boundaries
- Level shifters between security domains do not create information leakage paths
- Power gating sequences do not expose security state during transitions
- Decoupling capacitors and power grid design minimize data-dependent power signatures
- Isolated power supplies for security-critical blocks (crypto engines, key storage)

### Step 4: Verify Clock Domain Crossing Security
Review clock domain crossings (CDCs) near security logic:
- Synchronizers on all signals crossing between clock domains near security boundaries
- No metastability windows that could cause security checks to be bypassed
- Clock gating does not create windows where security monitors are inactive
- Glitch filters on security-critical asynchronous inputs

### Step 5: Assess Physical Attack Resistance
Evaluate the design against physical attack vectors:
- **Power analysis (DPA/SPA)**: Are crypto operations power-balanced? Are there masking countermeasures?
- **EM emanation**: Are sensitive blocks shielded? Is routing of key material minimized?
- **Fault injection**: Are voltage glitch detectors present? Are laser fault injection countermeasures in place?
- **Probing**: Are metal layers over key storage sufficient? Are mesh sensors present?

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, then resume from the earliest incomplete step.

## Output Format

### Physical Security Domain Map
```
┌─────────────────────────────────────┐
│ Power Domain: [Name]                │
│ Clock Domain: [Name]                │
│                                     │
│  ┌─────────┐     ┌──────────┐      │
│  │ [Block]  │────→│ [Block]  │      │
│  └─────────┘     └──────────┘      │
│         │ CDC                       │
│         ▼                           │
│  ┌─────────────┐                   │
│  │ [Sec Block]  │ ← Isolated power │
│  └─────────────┘                   │
└─────────────────────────────────────┘
```

### Physical Security Finding Table

| ID | Category | Location | Description | Severity | Recommendation |
|----|----------|----------|-------------|----------|----------------|
| P1 | Power leakage | Crypto engine | No power balancing on AES | High | Add dual-rail logic or masking |
| ... | ... | ... | ... | ... | ... |

### Residual Physical Risk Summary
- [Risk]: [Why accepted] — [Monitoring/detection approach]

## Handoff

- Hand off to rtl-security-review if RTL changes are needed for physical security findings.
- Hand off to microarch-analysis if microarchitectural mitigations are required based on physical analysis.

## Quality Checks
- [ ] All security-critical blocks are identified in the floorplan
- [ ] Power domain boundaries are verified to align with security domains
- [ ] Clock domain crossings near security logic are reviewed for metastability
- [ ] Timing margins on security-critical paths are assessed
- [ ] Physical attack resistance is evaluated (power analysis, EM, fault injection, probing)
- [ ] Power gating sequences are reviewed for security state exposure
- [ ] Recommendations include specific physical design changes

## Evolution Notes
<!-- Observations appended after each use -->
