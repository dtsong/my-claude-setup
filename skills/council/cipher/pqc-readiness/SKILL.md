---
name: pqc-readiness
department: "cipher"
description: "Use when assessing a system's readiness for post-quantum cryptography migration, inventorying classical crypto usage, mapping NIST-standardized PQC replacements, and planning phased migration timelines. Covers key exchange, digital signatures, and hybrid mode needs. Do not use for classical crypto implementation review (use crypto-review) or protocol state machine analysis (use protocol-analysis)."
version: 1
triggers:
  - "post-quantum"
  - "PQC"
  - "Kyber"
  - "Dilithium"
  - "ML-KEM"
  - "ML-DSA"
  - "quantum"
  - "NIST PQC"
  - "crypto agility"
  - "hybrid mode"
  - "quantum-safe"
---

# PQC Readiness

## Purpose
Assess a system's readiness for post-quantum cryptography migration by inventorying classical crypto usage, mapping PQC replacements, evaluating implementation readiness, and planning migration timelines.

## Scope Constraints

Reads source code, dependency manifests, and crypto library documentation for quantum readiness assessment. Does not modify files or execute code. Does not access production cryptographic infrastructure or key stores.

## Inputs
- System architecture and crypto inventory
- Current algorithm usage (key exchange, signatures, encryption)
- Data sensitivity and protection timeline requirements
- Performance constraints and resource budgets
- Compliance and regulatory requirements

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Step 1: Inventory Classical Crypto
Catalog all classical cryptographic algorithms in use:
- **Key exchange**: RSA, ECDH, DH — key sizes, curves, usage contexts
- **Digital signatures**: RSA, ECDSA, EdDSA — key sizes, curves, usage contexts
- **Symmetric**: AES, ChaCha20 — key sizes (symmetric algorithms are quantum-resistant with doubled key size via Grover's, but inventory for completeness)
- **Hashing**: SHA-2, SHA-3 — output sizes (hash outputs need doubling for quantum resistance)
- Note: Focus on asymmetric algorithms as the primary migration targets

### Step 2: Map PQC Replacements
For each classical asymmetric algorithm, identify the NIST-standardized PQC replacement:
- **Key exchange**: RSA/ECDH → ML-KEM (Kyber) — FIPS 203
- **Digital signatures**: RSA/ECDSA → ML-DSA (Dilithium) — FIPS 204, or SLH-DSA (SPHINCS+) — FIPS 205
- Document key size increases, signature size increases, and performance differences
- Identify where larger key/signature sizes impact protocols, storage, or bandwidth

### Step 3: Assess Implementation Readiness
Evaluate the system's readiness for PQC adoption:
- Are PQC libraries available for target platforms? (liboqs, pqcrypto, BoringSSL PQ)
- Do protocol implementations support PQC algorithm negotiation? (TLS 1.3 + PQ, SPDM 1.3)
- Can key storage accommodate larger PQC keys?
- Can bandwidth/latency budgets absorb larger PQC messages?
- Are there hardware acceleration options for PQC on target platforms?

### Step 4: Plan Migration Timeline
Define a phased migration approach:
- **Phase 1 — Inventory**: Complete crypto inventory (current step)
- **Phase 2 — Hybrid mode**: Deploy hybrid classical+PQC for key exchange (protects against "harvest now, decrypt later")
- **Phase 3 — PQC signatures**: Migrate digital signatures to PQC (less urgent than key exchange)
- **Phase 4 — Full PQC**: Remove classical algorithms where possible
- Map timeline against quantum computing threat estimates and compliance deadlines

### Step 5: Identify Hybrid Mode Needs
Assess where hybrid mode (classical + PQC simultaneously) is needed:
- Long-lived encrypted data ("harvest now, decrypt later" threat)
- Certificate chains (hybrid certificates for backward compatibility)
- Protocol negotiation (fallback to classical for non-PQC peers)
- Performance-sensitive paths (hybrid adds overhead — where is it acceptable?)

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, then resume from the earliest incomplete step.

## Output Format

### Classical Crypto Inventory

| Algorithm | Usage | Key Size | Quantum Security | PQC Replacement | Migration Priority |
|-----------|-------|----------|-----------------|-----------------|-------------------|
| ECDH P-256 | Key exchange | 256-bit | Broken by Shor's | ML-KEM-768 | Critical — harvest risk |
| ... | ... | ... | ... | ... | ... |

### PQC Migration Impact Assessment

| Migration | Size Impact | Performance Impact | Protocol Changes | Readiness |
|-----------|------------|-------------------|------------------|-----------|
| ECDH → ML-KEM-768 | +800B handshake | +0.1ms | TLS extension needed | Library ready |
| ... | ... | ... | ... | ... |

### Migration Timeline

| Phase | Action | Target Date | Dependencies | Risk |
|-------|--------|-------------|-------------|------|
| Phase 1 | Complete crypto inventory | Immediate | None | Low |
| Phase 2 | Deploy hybrid key exchange | [Date] | Library support | Medium |
| ... | ... | ... | ... | ... |

### Residual Quantum Risk Summary
- [Risk]: [Timeline to exploit] — [Mitigation approach]

## Handoff

- Hand off to crypto-review if implementation-level crypto issues are found during inventory.
- Hand off to protocol-analysis if protocol changes are needed for PQC migration.

## Quality Checks
- [ ] All asymmetric crypto operations inventoried
- [ ] PQC replacements mapped to NIST-standardized algorithms
- [ ] Key/signature size increases quantified
- [ ] Implementation readiness assessed for target platforms
- [ ] Hybrid mode needs identified for "harvest now, decrypt later" scenarios
- [ ] Migration timeline defined with clear phases and dependencies
- [ ] Compliance requirements incorporated into timeline

## Evolution Notes
<!-- Observations appended after each use -->
