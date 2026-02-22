## Post-Quantum Cryptography (PQC) Threats

| Threat Area | Specific Threats | Target Component |
|---|---|---|
| Implementation SCA | DPA on NTT butterfly operations, SPA on polynomial multiplication, EM analysis of modular reduction | NTT unit, polynomial multiplier |
| Fault attacks on NTT | Fault injection during NTT to skip CCA transform, glitching decapsulation check | NTT unit, CCA transform logic |
| Key generation entropy | Insufficient entropy in lattice key generation, deterministic nonce failure in ML-DSA | TRNG, seed expansion, nonce generator |
| Hybrid mode risks | Downgrade attacks on classical+PQC negotiation, weakest-link in hybrid key exchange | Key exchange protocol, mode negotiation |
| Rejection sampling leakage | Timing leakage in ML-DSA rejection sampling, cache-timing on sample-and-reject loop | Signing engine, rejection sampler |

## Chiplet/UCIe Threats

| Threat Area | Specific Threats | Target Component |
|---|---|---|
| Die-to-die authentication | Spoofed chiplet identity, replay on UCIe authentication, MITM on D2D link | UCIe link layer, authentication module |
| Chiplet supply chain | Counterfeit die in multi-vendor package, tampered chiplet firmware, provenance verification failure | Package assembly, chiplet provisioning |
| Inter-die integrity | Data corruption on D2D link, integrity bypass on UCIe flit, replay of stale data | UCIe integrity engine, flit MAC |
| Shared memory across dies | Cross-die memory access without authorization, coherence protocol exploitation, shared cache side-channels | Memory controller, coherence fabric |

## Heterogeneous Compute Threats

| Threat Area | Specific Threats | Target Component |
|---|---|---|
| CPU/GPU/NPU trust boundaries | Privilege escalation across heterogeneous elements, mismatched trust levels, inconsistent access control | Interconnect, access control unit |
| Shared memory security | GPU reading CPU secure memory, NPU accessing GPU framebuffer, DMA without IOMMU | IOMMU/SMMU, memory fabric |
| Driver isolation | Malicious driver exploiting GPU/NPU kernel interface, driver-to-driver interference | Driver interface, kernel API surface |
| DMA between elements | Unrestricted DMA from accelerator to system memory, IOMMU bypass via accelerator-specific paths | DMA engine, IOMMU configuration |

## AI Accelerator Threats

| Threat Area | Specific Threats | Target Component |
|---|---|---|
| Model weight confidentiality | Weight extraction via debug interface, DMA read of weight memory, cold boot on weight SRAM | Weight memory, debug port, DMA controller |
| Inference integrity | Result tampering via fault injection, adversarial input causing accelerator malfunction | Inference pipeline, activation functions |
| Weight extraction via SCA | Power/EM analysis during inference to recover weights, cache-timing on weight access patterns | MAC array, weight buffer, cache hierarchy |
| NPU memory isolation | NPU accessing host memory without authorization, shared buffer overflows, weight memory not cleared between contexts | NPU memory controller, context switch logic |

## Migration Risk Tables

### Classical to Post-Quantum

| Risk Area | Description | Severity |
|---|---|---|
| Hybrid mode complexity | Dual key management, increased attack surface during coexistence | HIGH |
| Algorithm agility | Ability to swap PQC algorithms if chosen one is broken | MEDIUM |
| Key size increase | Larger keys expose new side-channel surfaces, increase memory pressure | MEDIUM |
| Harvest-now-decrypt-later | Data encrypted today may be decrypted by future quantum computers | HIGH |

### Monolithic to Chiplet

| Risk Area | Description | Severity |
|---|---|---|
| New trust boundaries | Previously internal signals now cross die boundaries | HIGH |
| Multi-vendor trust | Chiplets from different vendors require mutual authentication | HIGH |
| Supply chain expansion | More points of interdiction in multi-vendor supply chain | MEDIUM |
| Debug and test | Cross-die debug introduces new attack surfaces | MEDIUM |

### Homogeneous to Heterogeneous

| Risk Area | Description | Severity |
|---|---|---|
| Trust model mismatch | Different security models across CPU/GPU/NPU require reconciliation | HIGH |
| Shared memory complexity | Coherence protocols across heterogeneous elements increase attack surface | MEDIUM |
| Driver proliferation | More drivers mean more kernel attack surface | MEDIUM |
| Unified security policy | Enforcing consistent security policy across heterogeneous elements | HIGH |
