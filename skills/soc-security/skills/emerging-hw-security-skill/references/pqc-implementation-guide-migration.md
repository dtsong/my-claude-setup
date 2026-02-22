# PQC Hardware Implementation — SLH-DSA, Migration Strategy, and Side-Channel Considerations

## FIPS 205 — SLH-DSA (Stateless Hash-Based Digital Signature Algorithm)

Formerly SPHINCS+. Standardized August 2024.

### Hash Tree Traversal

SLH-DSA is based on hash-based signatures using Merkle trees (XMSS trees within a hypertree structure).

**Tree Traversal Security:**
- Signing requires traversal of a hypertree structure: FORS trees at the bottom, then multiple layers of XMSS trees
- The path through the tree depends on the message digest — this is public
- However, the secret seed used to generate one-time signing keys must not leak during tree node computation

**Hash Function Security:**
- SLH-DSA uses SHAKE-256 or SHA-256 (parameter-set dependent)
- Hardware hash acceleration must be side-channel resistant when processing secret seed material
- Intermediate hash values during tree node generation are secret — they derive one-time signing keys

### Stateless Security

Unlike XMSS (stateful), SLH-DSA is stateless — no state management is needed across signatures. This eliminates state-reuse attacks but introduces other considerations:

**Security Implications:**
- No risk of one-time key reuse (the primary risk in stateful hash-based schemes)
- Larger signatures (~7-49 KB depending on parameter set) increase processing time and potential SCA exposure window
- Randomized message compression (using optional randomness) provides protection against fault attacks on the message hash
- If the optional randomness is omitted (deterministic mode), the signing process is vulnerable to differential fault attacks on the message hash computation

### Timing on Tree Operations

**Tree Generation Timing:**
- FORS (Forest of Random Subsets) tree generation time depends on the message-derived indices — this is intentional and public
- XMSS tree traversal time is fixed for a given parameter set — must remain constant
- The hypertree authentication path computation should execute in constant time

**Hardware Implementation Considerations:**
- Hash unit must provide constant-time operation when processing secret inputs
- Memory access patterns during tree traversal must not reveal which nodes are authentication path nodes vs. computed intermediate nodes (or this distinction must be made non-secret by design)
- Signature generation time for SLH-DSA is significantly longer than ML-DSA (~100x depending on parameters) — longer observation window for SCA

---

## Hybrid Mode Security

Hybrid mode combines classical and post-quantum algorithms during the migration period.

### Classical + PQC Key Exchange

**Typical Hybrid Construction:**
- Perform classical ECDH key exchange to derive `K_classical`
- Perform ML-KEM encapsulation to derive `K_pqc`
- Combine: `K_final = KDF(K_classical || K_pqc)`

**Security Requirements:**
- If either component is broken, the other should still provide security (combinatorial security)
- The KDF must be domain-separated to prevent cross-protocol attacks
- Key sizes differ significantly: ECDH shared secret ~32 bytes, ML-KEM shared secret 32 bytes, but ML-KEM ciphertext ~1088-1568 bytes

**Hybrid Mode Threats:**

| Threat | Description | Severity |
|--------|-------------|----------|
| Downgrade attack | Attacker forces negotiation to classical-only mode | Critical |
| Implementation complexity | Dual key management increases bug surface | High |
| Side-channel on KDF | Combining step may leak individual key components | Medium |
| Protocol interaction | Classical and PQC handshake messages may interfere or create oracle | Medium |
| Backward compatibility | Legacy peers that cannot negotiate PQC may fall back insecurely | High |

### Migration Strategies

**Big-Bang Migration:**
- Replace all classical crypto with PQC simultaneously
- Lowest long-term complexity but highest deployment risk
- Requires all endpoints to support PQC before switch

**Phased Migration (Recommended):**
1. **Phase 1:** Add PQC capability, negotiate hybrid mode where both peers support it
2. **Phase 2:** Require hybrid mode for all new connections, allow classical for legacy
3. **Phase 3:** Deprecate classical-only mode, require PQC (hybrid or PQC-only)
4. **Phase 4:** Remove classical crypto code paths

**Algorithm Agility:**
- Hardware must support algorithm agility — ability to replace PQC algorithm if broken
- NTT unit should be parameterizable (different moduli, different polynomial degrees) or replaceable
- Crypto abstraction layer between hardware accelerator and protocol stack

---

## SCA Resistance Requirements for PQC

### DPA on NTT Butterfly

**Attack Model:**
- Attacker collects power traces during NTT computation
- Targets the multiply step: `a[i] * twiddle_factor` where `a[i]` is a secret coefficient
- Hypothesizes coefficient values and correlates with measured power

**Countermeasure: Boolean Masking**
- Split each coefficient into two shares: `a[i] = a'[i] XOR r[i]` where `r[i]` is random
- NTT operates on masked shares independently
- Unmasking occurs only at the final combination point (which must also be protected)
- First-order masking: protects against DPA but not higher-order attacks
- Second-order masking: protects against bivariate DPA, approximately doubles area overhead

**Countermeasure: Shuffling**
- Randomize the order of butterfly operations within each NTT layer
- Does not eliminate leakage but reduces signal-to-noise ratio
- Can be combined with masking for defense in depth
- Hardware implementation: random permutation network on butterfly input selection

### Fault Injection on CCA Transform

**Attack Model:**
- Target the FO transform re-encryption check in ML-KEM decapsulation
- Inject a fault (voltage glitch, laser) to skip the comparison step
- If successful, scheme degrades from CCA to CPA security — chosen-ciphertext attacks become possible

**Countermeasures:**
- Redundant computation: perform FO check twice with independent logic
- Infection countermeasure: if fault detected, corrupt output in a way that does not reveal secret
- Hardware fault detection: voltage/clock glitch detectors, laser light sensors
- Error-detecting codes on control flow: ensure comparison instruction actually executes

**Attack Model: Fault on NTT Computation**
- Inject fault during NTT to produce incorrect transform output
- Differential fault analysis (DFA): compare correct and faulted outputs to recover secret polynomial
- Bellcore-style attack adapted for lattice-based schemes

**Countermeasures:**
- Redundant NTT with comparison (double computation cost)
- Algebraic checks: verify NTT output satisfies expected polynomial relationships
- Randomized intermediate checks: verify a random subset of butterfly results mid-computation
