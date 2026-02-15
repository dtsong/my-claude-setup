---
name: crypto-review
department: "cipher"
description: "Use when reviewing cryptographic implementations for algorithm choice correctness, key management soundness, side-channel resistance, and crypto agility readiness. Covers symmetric and asymmetric operations, key lifecycle, and construction safety. Do not use for protocol-level analysis (use protocol-analysis) or post-quantum migration planning (use pqc-readiness)."
version: 1
triggers:
  - "crypto"
  - "encryption"
  - "decryption"
  - "AES"
  - "RSA"
  - "ECC"
  - "key management"
  - "AEAD"
  - "hash"
  - "HMAC"
  - "KDF"
  - "nonce"
  - "IV"
  - "digital signature"
---

# Crypto Review

## Purpose
Review cryptographic implementations for algorithm choice correctness, key management soundness, side-channel resistance, and crypto agility readiness.

## Scope Constraints

Reads source code, configuration files, and documentation for cryptographic implementation analysis. Does not modify files or execute code. Does not access key material, HSMs, or cryptographic secrets directly.

## Inputs
- System or component using cryptographic operations
- Cryptographic algorithms and modes in use
- Key management architecture (generation, storage, rotation, destruction)
- Data sensitivity classification and compliance requirements
- Performance constraints and target platforms

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Step 1: Inventory Crypto Operations
Enumerate all cryptographic operations in the system:
- Symmetric encryption (algorithm, mode, key size)
- Asymmetric operations (signing, key exchange, encryption)
- Hashing (algorithm, usage context — integrity, commitment, password)
- Key derivation (KDF, parameters, input entropy)
- Random number generation (source, seeding, reseeding)

### Step 2: Check Algorithm Choices
For each crypto operation, verify:
- Algorithm is current and not deprecated (no MD5, SHA-1 for security, DES, RC4)
- Mode is appropriate (AEAD preferred: AES-GCM, ChaCha20-Poly1305; no ECB, no unauthenticated CBC)
- Key size provides adequate security margin (AES-256 for long-term, AES-128 minimum)
- Parameters are correct (IV/nonce size, tag length, iteration counts for KDFs)
- Construction is standard (no custom padding, no hand-rolled MAC-then-encrypt)

### Step 3: Review Key Management
Assess the full key lifecycle:
- **Generation**: Keys generated from cryptographically secure RNG? Sufficient entropy?
- **Storage**: Keys stored in HSM/TPM/keystore? Never in plaintext config files or source code?
- **Distribution**: Key exchange uses authenticated channels? No key material in logs or error messages?
- **Rotation**: Rotation policy defined? Rotation does not cause service disruption?
- **Destruction**: Keys securely erased after use? Memory not swapped to disk with key material?

### Step 4: Assess Side-Channel Resistance
For security-critical crypto operations, check:
- Constant-time comparison for MACs and signatures (no early-exit on mismatch)
- Constant-time table lookups (no cache-timing-dependent S-box access)
- No branching on secret data
- Memory access patterns independent of key material
- Adequate blinding for RSA/ECC operations

### Step 5: Check Crypto Agility
Assess the system's ability to migrate algorithms:
- Are algorithm identifiers negotiated or hardcoded?
- Can algorithms be swapped without architectural changes?
- Is there a version/algorithm field in encrypted data formats?
- Can the system support hybrid mode (classical + PQC)?

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, then resume from the earliest incomplete step.

## Output Format

### Crypto Operations Inventory

| Operation | Algorithm | Mode | Key Size | Context | Status |
|-----------|-----------|------|----------|---------|--------|
| Data encryption | AES | GCM | 256-bit | Storage at rest | OK |
| ... | ... | ... | ... | ... | ... |

### Finding Table

| ID | Category | Description | Severity | Recommendation |
|----|----------|-------------|----------|----------------|
| C1 | Algorithm | SHA-1 used for integrity check | High | Migrate to SHA-256 |
| ... | ... | ... | ... | ... |

### Key Management Assessment
- **Generation**: [Assessment]
- **Storage**: [Assessment]
- **Rotation**: [Assessment]
- **Destruction**: [Assessment]

### Crypto Agility Score
- [ ] Algorithm identifiers negotiated: [Yes/No]
- [ ] Format supports versioning: [Yes/No]
- [ ] Hybrid mode possible: [Yes/No]

## Handoff

- Hand off to protocol-analysis if protocol-level vulnerabilities are identified during crypto review.
- Hand off to pqc-readiness if quantum migration planning is needed based on algorithm inventory.

## Quality Checks
- [ ] All crypto operations are inventoried
- [ ] No deprecated algorithms in security-critical paths
- [ ] AEAD mode used for all authenticated encryption
- [ ] Key management covers full lifecycle (generate, store, rotate, destroy)
- [ ] Side-channel resistance assessed for security-critical operations
- [ ] Nonce/IV management verified (uniqueness guaranteed)
- [ ] Crypto agility path exists for future algorithm migration

## Evolution Notes
<!-- Observations appended after each use -->
