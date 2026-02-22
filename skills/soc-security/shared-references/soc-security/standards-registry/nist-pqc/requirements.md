# NIST Post-Quantum Cryptography Standards — FIPS 203 (ML-KEM), FIPS 204 (ML-DSA), FIPS 205 (SLH-DSA)

## Specification Overview

| Field | Value |
|---|---|
| **Full Name** | NIST Post-Quantum Cryptography Standards: FIPS 203 (Module-Lattice-Based Key-Encapsulation Mechanism), FIPS 204 (Module-Lattice-Based Digital Signature Algorithm), FIPS 205 (Stateless Hash-Based Digital Signature Algorithm) |
| **Version** | FIPS 203/204/205 Final (2024) [FROM TRAINING] |
| **Organization** | National Institute of Standards and Technology (NIST) |
| **Scope** | Quantum-resistant cryptographic algorithms for key encapsulation and digital signatures suitable for hardware and software implementation |
| **Security Properties Addressed** | Quantum Resistance, Confidentiality, Authenticity, Non-Repudiation, Implementation Security |
| **Related Standards** | FIPS 140-3 (cryptographic module validation), NIST SP 800-227 (PQC migration), CNSA 2.0 (NSA PQC timeline), FIPS 186-5 (classical signatures) |

---

## Concept Summary

The NIST Post-Quantum Cryptography standards define three algorithms designed to resist attacks from both classical and quantum computers. FIPS 203 (ML-KEM, based on CRYSTALS-Kyber) provides key encapsulation using module-lattice problems, offering parameter sets at three security levels. FIPS 204 (ML-DSA, based on CRYSTALS-Dilithium) provides digital signatures using module-lattice problems. FIPS 205 (SLH-DSA, based on SPHINCS+) provides stateless hash-based digital signatures as a conservative alternative relying only on hash function security. For hardware implementations, these standards introduce new requirements around constant-time execution, rejection sampling, polynomial arithmetic, and entropy sources that differ substantially from classical cryptographic hardware.

**Key architectural principle:** PQC migration is not a drop-in replacement — lattice-based schemes have larger key and ciphertext sizes, different failure modes (decapsulation failure probability), and new side-channel attack surfaces (e.g., timing leakage in NTT operations, rejection sampling) that require dedicated hardware design consideration.

---

## Key Security Requirements

### ML-KEM Parameter Sets and Compliance (FIPS 203)

**REQ-PQC-001: ML-KEM Parameter Set Implementation**
Implementations must support at least one of the three approved ML-KEM parameter sets: ML-KEM-512 (NIST security level 1, 128-bit classical), ML-KEM-768 (NIST security level 3, 192-bit classical), or ML-KEM-1024 (NIST security level 5, 256-bit classical). The parameter set determines the module dimension (k), polynomial ring degree (n=256), and modulus (q=3329). Implementations must not deviate from the specified parameters.

- **Security properties:** Quantum Resistance, Confidentiality
- **Verification tier:** Tier 2 — protocol-level known-answer tests (KATs) for each parameter set
- **Cross-references:** CNSA 2.0 (ML-KEM-1024 required for national security systems), FIPS 140-3

**REQ-PQC-002: ML-KEM Decapsulation Failure Handling**
ML-KEM decapsulation includes an implicit rejection mechanism: when decapsulation detects an invalid ciphertext, it must return a pseudorandom shared secret derived from the secret key and ciphertext (rather than an error code). This prevents chosen-ciphertext attacks that exploit decapsulation failure oracles. The implementation must not leak whether decapsulation succeeded or failed through timing, error codes, or any other side channel.

- **Security properties:** Confidentiality, Quantum Resistance, Leakage Resistance
- **Verification tier:** Tier 1 — SVA assertions for constant-time decapsulation path; Tier 2 — KAT for implicit rejection
- **Cross-references:** REQ-PQC-008 (side-channel resistance), FIPS 203 Section 7.3

**REQ-PQC-003: ML-KEM Key Generation Entropy**
ML-KEM key generation requires 64 bytes (512 bits) of random input from an approved random bit generator (RBG) compliant with NIST SP 800-90A/B/C. The entropy source must be seeded before key generation begins. For hardware implementations, the RBG must be a DRBG backed by a hardware entropy source (TRNG) meeting NIST SP 800-90B requirements. The random input directly determines key security — insufficient entropy renders keys predictable.

- **Security properties:** Quantum Resistance, Confidentiality
- **Verification tier:** Tier 1 — SVA assertions for TRNG health checks before key generation; Tier 2 — entropy source validation
- **Cross-references:** FIPS 140-3 (RBG requirements), NIST SP 800-90B (entropy source)

### ML-DSA Parameter Sets and Compliance (FIPS 204)

**REQ-PQC-004: ML-DSA Parameter Set Implementation**
Implementations must support at least one of the three approved ML-DSA parameter sets: ML-DSA-44 (NIST security level 2), ML-DSA-65 (NIST security level 3), or ML-DSA-87 (NIST security level 5). The parameter set determines the module dimensions (k, l), polynomial ring degree (n=256), and modulus (q=8380417). Implementations must follow the specified rounding, hint, and challenge generation procedures exactly.

- **Security properties:** Quantum Resistance, Authenticity, Non-Repudiation
- **Verification tier:** Tier 2 — protocol-level KATs for each parameter set
- **Cross-references:** CNSA 2.0 (ML-DSA-87 required for national security systems), FIPS 140-3

**REQ-PQC-005: ML-DSA Rejection Sampling Correctness**
ML-DSA signature generation uses rejection sampling — the signer generates a candidate signature and checks whether it satisfies norm bounds; if not, the process is repeated with fresh randomness. The implementation must perform rejection sampling correctly without introducing bias. The number of rejection iterations must not be leaked through timing, and the implementation must handle the variable number of iterations in constant time (or with appropriate masking of the iteration count).

- **Security properties:** Authenticity, Leakage Resistance
- **Verification tier:** Tier 1 — SVA assertions for constant-time rejection loop; Tier 2 — statistical distribution testing
- **Cross-references:** REQ-PQC-008 (side-channel resistance), FIPS 204 Section 6

### SLH-DSA Parameter Sets and Compliance (FIPS 205)

**REQ-PQC-006: SLH-DSA Parameter Set Implementation**
Implementations must support at least one approved SLH-DSA parameter set. SLH-DSA provides parameter sets at three security levels in both "small" (shorter signatures, slower signing) and "fast" (faster signing, larger signatures) variants: SLH-DSA-128s/f, SLH-DSA-192s/f, and SLH-DSA-256s/f. Implementations must use the specified hash function (SHA-256 or SHAKE-256) consistent with the chosen parameter set.

- **Security properties:** Quantum Resistance, Authenticity, Non-Repudiation
- **Verification tier:** Tier 2 — protocol-level KATs for each parameter set
- **Cross-references:** FIPS 140-3, FIPS 205 Section 10 (parameter sets)

**REQ-PQC-007: SLH-DSA Stateless Operation Guarantee**
SLH-DSA is a stateless hash-based signature scheme — unlike XMSS/LMS, the signer does not need to maintain state between signature operations. However, the implementation must generate a random value for each signature operation to ensure security. Hardware implementations must not reuse randomness across signature operations, and the random input must come from an approved RBG. Failure to provide fresh randomness per signature compromises signature security.

- **Security properties:** Quantum Resistance, Authenticity, Freshness
- **Verification tier:** Tier 1 — SVA assertions for fresh randomness per signature; Tier 2 — KAT
- **Cross-references:** REQ-PQC-003 (entropy requirements), NIST SP 800-90A (DRBG)

### Implementation Security Requirements

**REQ-PQC-008: Side-Channel Resistance for PQC Hardware**
Hardware implementations of ML-KEM, ML-DSA, and SLH-DSA must resist side-channel attacks targeting PQC-specific operations: Number Theoretic Transform (NTT) computations, polynomial multiplication, rejection sampling loops, Keccak/SHA permutations during hashing, and comparison operations during decapsulation. Constant-time execution is required for all operations that process secret data. Implementation-specific countermeasures (masking, shuffling) must be documented and their effectiveness assessed.

- **Security properties:** Leakage Resistance, Confidentiality, Quantum Resistance
- **Verification tier:** Tier 1 — SVA assertions for constant-time datapath; Tier 3 — TVLA assessment per ISO 17825
- **Cross-references:** REQ-ISO17825-001 (TVLA methodology), REQ-ISO17825-012 (countermeasure evaluation)

**REQ-PQC-009: Fault Attack Resistance**
Hardware implementations must include countermeasures against fault injection attacks targeting PQC algorithms. Known fault attack surfaces include: skipping rejection sampling iterations in ML-DSA, corrupting NTT computations to recover secret keys, and inducing decapsulation failures in ML-KEM to bypass implicit rejection. Countermeasures must include redundant computation, result verification, or equivalent fault detection mechanisms.

- **Security properties:** Integrity, Quantum Resistance
- **Verification tier:** Tier 1 — SVA assertions for redundancy checks; Tier 3 — fault injection testing
- **Cross-references:** FIPS 140-3 Level 3+ (fault mitigation), Common Criteria FPT_FLS

### Hybrid and Migration Requirements

**REQ-PQC-010: Hybrid Mode (Classical + PQC)**
During the transition period, implementations should support hybrid key exchange and hybrid signatures that combine a classical algorithm (e.g., ECDH, ECDSA) with a PQC algorithm (e.g., ML-KEM, ML-DSA). The hybrid construction must ensure that the combined scheme is at least as secure as the stronger component — compromise of the classical algorithm alone must not compromise the overall security. The key combination function must be documented and must use approved methods (e.g., concatenation KDF per NIST SP 800-56C).

- **Security properties:** Quantum Resistance, Confidentiality, Authenticity
- **Verification tier:** Tier 2 — protocol-level validation of hybrid construction
- **Cross-references:** CNSA 2.0 (hybrid requirements during transition), NIST SP 800-227

**REQ-PQC-011: Migration Timeline Compliance**
Implementations must support migration timelines as defined by relevant authorities. CNSA 2.0 requires: PQC for software/firmware signing by 2025, PQC for key establishment by 2025, exclusive use of PQC (no hybrid) for most applications by 2033, and exclusive PQC for all national security systems by 2035. Hardware designs must support algorithm agility to accommodate timeline-driven updates.

- **Security properties:** Quantum Resistance
- **Verification tier:** Tier 2 — compliance review against migration milestones
- **Cross-references:** CNSA 2.0, NIST SP 800-227, OMB M-23-02

### Key Management and Lifecycle

**REQ-PQC-012: PQC Key Storage Requirements**
PQC keys are substantially larger than classical keys (ML-KEM-1024 public key: 1568 bytes; ML-DSA-87 public key: 2592 bytes). Hardware key storage must accommodate these sizes. Secret keys must be stored with the same protections as classical keys: hardware isolation, access control, and zeroization capability. Key storage must not introduce timing variability based on key values.

- **Security properties:** Confidentiality, Quantum Resistance
- **Verification tier:** Tier 1 — SVA assertions for key storage access control and zeroization
- **Cross-references:** FIPS 140-3 (key storage), REQ-PQC-001 (ML-KEM parameters)

**REQ-PQC-013: PQC Key Zeroization**
All PQC secret key material (secret keys, intermediate values including NTT representations, rejection sampling state, and shared secrets) must be zeroized immediately after use or upon a zeroization command. Hardware implementations must ensure that zeroization is complete and not subject to compiler or synthesis optimization that might skip the write. Zeroization must complete within a bounded time.

- **Security properties:** Confidentiality, Quantum Resistance
- **Verification tier:** Tier 1 — SVA assertions for zeroization of all secret registers and memory
- **Cross-references:** FIPS 140-3 (key zeroization), REQ-PQC-012 (key storage)

### Algorithm-Specific Hardware Requirements

**REQ-PQC-014: NTT Implementation Correctness**
The Number Theoretic Transform (NTT) is a core operation in ML-KEM and ML-DSA for efficient polynomial multiplication. Hardware NTT implementations must produce results that are bit-exact with the reference implementation for all inputs. The NTT must use the correct primitive root of unity and modular reduction for the specified prime (q=3329 for ML-KEM, q=8380417 for ML-DSA). Butterfly operations must not overflow intermediate precision.

- **Security properties:** Integrity, Quantum Resistance
- **Verification tier:** Tier 1 — SVA assertions for NTT output correctness; Tier 2 — exhaustive KAT against reference
- **Cross-references:** REQ-PQC-001 (ML-KEM parameters), REQ-PQC-004 (ML-DSA parameters)

**REQ-PQC-015: Keccak/SHA Hardware Accelerator Requirements**
ML-KEM, ML-DSA, and SLH-DSA make extensive use of SHA-3 (Keccak) and/or SHA-256 hash functions as core building blocks. Hardware implementations should include dedicated hash accelerators to meet performance requirements. The hash implementation must be FIPS 202/FIPS 180-4 compliant and must be validated independently. For SLH-DSA, which is hash-intensive, the hash accelerator throughput directly determines signing performance.

- **Security properties:** Integrity, Quantum Resistance
- **Verification tier:** Tier 1 — SVA assertions for Keccak permutation correctness; Tier 2 — hash KATs
- **Cross-references:** FIPS 202 (SHA-3), FIPS 180-4 (SHA-2), REQ-PQC-006 (SLH-DSA parameters)

---

## Verification Considerations

| Requirement | Tier | Verification Approach |
|---|---|---|
| REQ-PQC-001 | Tier 2 | Protocol: ML-KEM KATs for each supported parameter set match reference output |
| REQ-PQC-002 | Tier 1/2 | SVA: decapsulation path timing constant; KAT: implicit rejection output correct |
| REQ-PQC-003 | Tier 1/2 | SVA: TRNG health check before keygen; Protocol: entropy source validation |
| REQ-PQC-004 | Tier 2 | Protocol: ML-DSA KATs for each supported parameter set match reference output |
| REQ-PQC-005 | Tier 1/2 | SVA: constant-time rejection loop; Statistical: output distribution analysis |
| REQ-PQC-006 | Tier 2 | Protocol: SLH-DSA KATs for each supported parameter set match reference output |
| REQ-PQC-007 | Tier 1/2 | SVA: fresh randomness per signature; KAT: randomized signature correctness |
| REQ-PQC-008 | Tier 1/3 | SVA: constant-time datapath for secret operations; Lab: TVLA leakage assessment |
| REQ-PQC-009 | Tier 1/3 | SVA: redundancy checks in NTT/rejection; Lab: fault injection campaign |
| REQ-PQC-010 | Tier 2 | Protocol: hybrid construction produces correct combined output |
| REQ-PQC-011 | Tier 2 | Review: algorithm agility supports required migration milestones |
| REQ-PQC-012 | Tier 1 | SVA: key storage access control enforced; zeroization capability present |
| REQ-PQC-013 | Tier 1 | SVA: all secret registers and memory zeroized within bounded time |
| REQ-PQC-014 | Tier 1/2 | SVA: NTT butterfly correctness; KAT: bit-exact match against reference |
| REQ-PQC-015 | Tier 1/2 | SVA: Keccak permutation correctness; KAT: hash output matches FIPS vectors |

---

*[FROM TRAINING] Requirements are derived summaries, not verbatim specification text. Verify requirement details against FIPS 203, FIPS 204, FIPS 205 final standards, NIST SP 800-227, and CNSA 2.0 advisory. Last verified: 2026-02-13.*
