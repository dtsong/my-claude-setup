# Eval Case: Standards-Derived Threat Extraction — CXL 3.1 IDE Key Management

## Metadata
- **Case ID:** TM-004
- **Tier:** 3 (complex)
- **Skill Route:** threat-model-skill
- **Estimated Complexity:** high

## Input
```json
{
  "user_prompt": "Extract threats from the CXL 3.1 specification Section 11 (Integrity and Data Encryption) for our IDE key management subsystem. We implement selective IDE with per-stream key granularity. The subsystem handles:\n\n- IDE key generation (TRNG-seeded AES-256-GCM keys)\n- Key programming via CXL.io configuration writes to IDE KM registers\n- Key rotation triggered by host-initiated IDE_KM K_SET_GO\n- IV management (96-bit IV with 32-bit counter, 64-bit salt per stream)\n- Key storage in tamper-resistant register file (16 key slots)\n\nI want every SHALL and MUST from CXL 3.1 Section 11 that applies to this subsystem negated into threat statements. Also cross-reference with SPDM 1.3 Section 10 for the authenticated key exchange dependencies.\n\nSoC family: Data Center. Technology domain: TDISP/CXL.",
  "context": "CXL 3.1 spec sections provided in the working directory as cxl31_section11.pdf. SPDM 1.3 spec available. Prior threat model TM-2025-042 covered CXL.io interface but not IDE key management specifically. The team needs this for an upcoming CXL Consortium compliance review."
}
```

## Expected Output
Standards-derived threat findings with:
- Explicit requirement negation (SHALL X -> threat: failure to X)
- Spec section references for every finding
- Cross-reference between CXL 3.1 and SPDM 1.3 requirements
- GROUNDED confidence for spec-derived threats
- Coverage of key lifecycle phases (generation, programming, rotation, IV management, storage)

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] At least 8 threat findings derived from explicit SHALL/MUST requirements
- [ ] Every finding references a specific CXL 3.1 Section 11 sub-section
- [ ] Confidence tier is GROUNDED for all spec-derived findings (directly supported by cited spec)
- [ ] IV management threats present — IV reuse/counter overflow is a critical AES-GCM failure mode
- [ ] Key rotation threats present — incomplete K_SET_GO handling leaves window with old keys
- [ ] Key programming threats present — unauthorized CXL.io config writes to IDE KM registers

### Should Pass (partial credit)
- [ ] Cross-reference with SPDM 1.3 Section 10 identifies dependency threats (key exchange without mutual auth)
- [ ] Requirement negation methodology is explicit (quote the SHALL, then negate it)
- [ ] Key lifecycle coverage: findings span generation, programming, rotation, IV management, and storage phases
- [ ] Findings distinguish between explicit requirements (SHALL -> GROUNDED) and implicit requirements (SHOULD -> INFERRED)
- [ ] Prior threat model TM-2025-042 referenced to avoid duplicating CXL.io findings

### Bonus
- [ ] Identifies a gap where CXL 3.1 Section 11 defers to implementation (no SHALL) but a threat still exists — marked as INFERRED
- [ ] Cross-references with NIST SP 800-38D for AES-GCM-specific IV/counter requirements beyond what CXL 3.1 specifies
- [ ] Notes that per-stream key granularity (16 slots) creates a key management scalability threat not addressed by the spec

## Raw Trace Log
