# Chiplet Security Model — Heterogeneous Compute, AI Accelerator & Security Boundaries

Covers CPU/GPU/NPU trust boundaries, shared memory security, AI accelerator isolation (weight protection, inference integrity, model confidentiality), and multi-die security boundary definitions.

**Primary consumer:** emerging-hw-security-skill (Phase 3 heterogeneous compute and AI accelerator analysis)

---

## Heterogeneous Compute Security

### CPU/GPU/NPU Trust Boundary Model

Heterogeneous SoCs integrate multiple compute element types with different security models.

**Trust Boundary Map:**

```
+-------------------+     +-------------------+     +-------------------+
|     CPU Die       |     |     GPU Die       |     |     NPU Die       |
|                   |     |                   |     |                   |
| - Full OS/kernel  |     | - GPU runtime     |     | - NPU firmware    |
| - MMU + SMMU      |     | - Shader memory   |     | - Weight memory   |
| - TEE (TrustZone/ |     | - GPU MMU         |     | - Activation mem  |
|   SEV/TDX)        |     | - No TEE (typical)|     | - No MMU (typical)|
| - DRAM controller |     | - Local HBM/GDDR  |     | - Local SRAM      |
|                   |     |                   |     |                   |
+--------+----------+     +--------+----------+     +--------+----------+
         |                         |                         |
         +------------+------------+------------+------------+
                      |                         |
              +-------v-------+         +-------v-------+
              | Interconnect  |         | Shared Memory |
              | (NoC / UCIe)  |         | (if present)  |
              +---------------+         +---------------+
```

**Trust Level Differences:**

| Element | Trust Model | Memory Protection | Isolation Mechanism |
|---------|-----------|-------------------|-------------------|
| CPU | Full OS trust model, TEE capable | MMU + SMMU/IOMMU | Process isolation, VM isolation, TEE |
| GPU | User-space driver trust, limited kernel | GPU MMU (vendor-specific) | Context isolation (vendor-specific) |
| NPU | Firmware-only, no OS | Often no MMU — relies on firmware access control | Firmware-enforced memory regions |
| DSP | Firmware-only, limited | MPU (Memory Protection Unit) if present | MPU regions, firmware access control |

**Cross-Element Trust Issues:**

| Issue | Description | Risk |
|-------|-------------|------|
| Trust asymmetry | CPU trusts GPU kernel driver; GPU has no mechanism to verify CPU intentions | GPU executes any workload submitted by CPU without validation |
| TEE boundary mismatch | CPU TEE (TrustZone/SEV) does not extend to GPU/NPU | Confidential data decrypted for GPU/NPU processing is exposed outside TEE |
| Privilege escalation path | GPU/NPU kernel driver runs in CPU kernel space | GPU/NPU driver vulnerability = CPU kernel compromise |
| Inconsistent access control | CPU uses SMMU; NPU uses firmware-based access control | Bypassing NPU firmware access control is easier than bypassing SMMU |

### Shared Memory Security Across Heterogeneous Elements

**Shared Memory Configurations:**

| Configuration | Description | Security Implication |
|--------------|-------------|---------------------|
| CPU-GPU shared virtual memory (SVM) | CPU and GPU share virtual address space via unified page tables | GPU can access any CPU memory mapped into shared space |
| CPU-NPU DMA buffer | CPU allocates DMA buffers for NPU input/output | Buffer must be pinned, access-controlled, and zeroized after use |
| GPU-NPU peer DMA | GPU and NPU transfer data directly without CPU involvement | Bypasses CPU-side access control entirely |
| Shared LLC | Last-level cache shared across CPU, GPU, NPU | Cache side-channel attacks across heterogeneous elements |

**Shared Memory Threats:**

| Threat | Description | Countermeasure |
|--------|-------------|---------------|
| Cross-element memory read | GPU reads CPU secure memory via shared address space | SMMU/IOMMU enforcement on all GPU DMA; no passthrough mode for security-sensitive memory |
| DMA buffer overrun | NPU writes beyond allocated DMA buffer into adjacent CPU memory | Hardware bounds checking on DMA descriptors; scatter-gather with per-entry bounds |
| Stale data in shared buffer | Previous context's data remains in shared buffer | Hardware zeroization on context switch; scrub DMA buffers before reallocation |
| Coherence protocol exploitation | Attacker uses coherence snoops to observe access patterns across elements | Coherence filter or partitioned coherence domain for security-sensitive traffic |
| Shared cache side-channel | Prime+Probe on shared LLC to observe GPU/NPU memory access patterns from CPU | Cache partitioning (CAT or equivalent) across heterogeneous elements |

---

## AI Accelerator Isolation

### Weight Protection

AI model weights represent significant intellectual property and may contain information about training data. Hardware must protect weight confidentiality.

**Weight Lifecycle:**

```
Weight Loading:
  Encrypted weights in storage ->
  Decrypted in NPU secure memory ->
  Distributed to MAC array weight buffers ->
  Used during inference/training ->
  Cleared from buffers after completion
```

**Weight Protection Requirements:**

| Requirement | Description | Implementation |
|-------------|-------------|----------------|
| Confidentiality at rest | Weights encrypted in DRAM/flash | AES-256 encryption with per-model keys |
| Confidentiality in transit | Weights encrypted during DMA from host to NPU | Encrypted DMA channel or in-NPU decryption |
| Confidentiality in use | Weights in NPU SRAM protected from external read | NPU memory not accessible via CPU debug, DMA, or JTAG |
| Integrity at rest | Weights authenticated in storage | HMAC or AEAD on weight blobs |
| Integrity in use | Weights not modified during inference | Write-protect weight memory regions during inference |
| Zeroization | Weights cleared when context ends | Hardware zeroization of weight SRAM and buffers on context switch |

**Weight Extraction Threats:**

| Threat | Attack Vector | Difficulty | Countermeasure |
|--------|--------------|------------|---------------|
| Debug port read | JTAG/SWD access to NPU internal SRAM | Low (if debug enabled) | Disable debug in production; fuse-blow debug access |
| DMA read from host | CPU issues DMA read to NPU weight memory | Medium | SMMU/IOMMU blocks host reads to NPU weight regions |
| Cold boot on SRAM | Power cycle and read SRAM data remanence | Medium-High | Rapid zeroization circuit on power-down; SRAM scrambling |
| Side-channel (power/EM) | Infer weights from power consumption during MAC operations | High | Masking on MAC array (very expensive); noise injection |
| Cache-timing | Observe weight access patterns via shared cache | Medium | Weight memory in non-cacheable region; dedicated NPU cache |
| Physical probing | Probe NPU die interconnects to read weight data | Very High | Shield layer, active mesh, tamper detection |

### Inference Integrity

Inference results must be correct — tampering with inference computation can have safety-critical consequences (e.g., autonomous driving, medical diagnosis).

**Inference Integrity Threats:**

| Threat | Attack Vector | Impact |
|--------|--------------|--------|
| Fault injection on MAC array | Voltage glitch during multiply-accumulate | Incorrect inference result |
| Input data tampering | Modified input activations via DMA buffer manipulation | Attacker-controlled inference output |
| Quantization attack | Exploit low-precision arithmetic to cause specific misclassification | Targeted adversarial output |
| Firmware tampering | Modified NPU firmware alters inference logic | Arbitrary inference behavior |

**Countermeasures:**
- Redundant inference (run twice, compare results) — expensive but effective
- Algorithmic checks: verify inference output satisfies expected statistical properties
- Hardware error detection: ECC on SRAM, parity on MAC array, CRC on activation buffers
- Signed firmware with secure boot for NPU firmware integrity
- Input validation: verify DMA buffer checksums before inference

### Model Confidentiality

Model architecture (layer structure, quantization, connectivity) may itself be confidential, beyond just the weights.

**Model Architecture Leakage Vectors:**

| Vector | What Leaks | Countermeasure |
|--------|-----------|---------------|
| Inference timing | Number of layers, layer types (conv vs. FC have different timing) | Constant-time inference padding (may waste cycles) |
| Memory access pattern | Layer connectivity, feature map sizes | Oblivious memory access (expensive) or fixed access pattern |
| Power profile | Layer types distinguishable by power consumption pattern | Power noise injection, power filtering |
| DMA transfer sizes | Model input/output dimensions, intermediate buffer sizes | Fixed-size DMA transfers with padding |
| Configuration registers | Model parameters programmed into NPU registers | Encrypt NPU configuration; restrict register readback |

---

## Security Boundary Definition for Multi-Die Packages

### Defining the Security Perimeter

For multi-die packages, the security boundary must be explicitly defined.

**Boundary Options:**

| Boundary Level | Scope | Trust Assumption | Example |
|---------------|-------|-----------------|---------|
| Package-level | Entire multi-die package is the security boundary | All dies within the package are trusted relative to each other | Single-vendor, tightly integrated MCM |
| Die-level | Each die is an independent security domain | Dies do not inherently trust each other | Multi-vendor chiplet package |
| IP-block-level | Security boundaries within a single die | Some IP blocks on a die are untrusted (e.g., third-party IP) | SoC with third-party GPU IP block |

### Security Boundary Enforcement

**Package-Level Boundary (All Dies Trusted):**
- D2D links need integrity (error detection) but not encryption
- Authentication at boot is sufficient; no runtime re-attestation needed
- Shared memory across dies has minimal access control overhead
- Threat model focuses on package-external attacks only

**Die-Level Boundary (Each Die Independent):**
- D2D links require authentication, integrity, and encryption
- Runtime attestation required for ongoing trust
- Shared memory requires SMMU/IOMMU enforcement per die
- Each die has independent secure boot, key storage, and firmware measurement
- Threat model includes inter-die attacks

**IP-Block-Level Boundary (Untrusted IP Within Die):**
- On-die interconnect requires access control (firewall/filter)
- Untrusted IP block has restricted memory map
- DMA from untrusted IP goes through SMMU/IOMMU
- Debug access to untrusted IP isolated from rest of die

### Cross-Boundary Data Flow Security

For each data flow that crosses a security boundary:

```
Cross-Boundary Data Flow Assessment
====================================

Flow: [Source] -> [Destination]
Boundary Crossed: [package / die / IP-block]
Data Classification: [public / confidential / secret]
Current Protection: [none / integrity / encryption / both]
Required Protection: [based on data classification and boundary level]
Gap: [if current < required, describe the gap]
```

**Minimum Protection by Boundary and Data Classification:**

| Data Classification | Package Boundary | Die Boundary | IP-Block Boundary |
|--------------------|-----------------|-------------|-------------------|
| Public | None | Integrity | Integrity |
| Confidential | Integrity | Integrity + Encryption | Integrity + Encryption |
| Secret | Integrity + Encryption | Integrity + Encryption + Access Control | Integrity + Encryption + Access Control |
