# Eval Case: Full Heterogeneous Compute Security Audit

## Metadata
- **Case ID:** EH-005
- **Tier:** 3 (complex)
- **Skill Route:** emerging-hw-security-skill
- **Estimated Complexity:** high

## Input
```json
{
  "user_prompt": "Conduct a full heterogeneous compute security audit for our edge AI SoC. This SoC integrates multiple compute paradigms with a PQC migration underway. Full details:\n\nCompute elements:\n1. CPU cluster: 4x ARM Cortex-A78 (application processor), TrustZone enabled\n2. GPU: Mali-G710, shared DRAM, SMMU-protected\n3. NPU: Custom 16-TOPS accelerator, dedicated SRAM (4MB), DMA to shared DRAM\n4. DSP: Custom DSP for sensor fusion, MMIO-controlled from CPU\n5. Security processor: ARM Cortex-M33 (TrustZone-M), runs secure boot + key management\n\nInterconnect:\n- AXI bus fabric with programmable firewall (TrustZone-aware, SMMU for GPU/NPU)\n- Shared DRAM: LPDDR5, 8GB, with TrustZone memory regions (TZASC)\n- No encryption on DRAM bus (plaintext)\n- Cache coherency: CPU-GPU coherent via ACE, NPU/DSP non-coherent\n\nPQC migration (in progress):\n- Replacing ECDSA P-256 with ML-DSA-65 for secure boot signature verification\n- Replacing ECDH P-256 with ML-KEM-768 for OTA (over-the-air) key exchange\n- Hybrid mode during transition: ECDH+ML-KEM concatenated\n- PQC operations run on security processor (SW implementation, no HW accelerator)\n- Migration timeline: hybrid mode 2026-2028, PQC-only 2029\n\nChiplet aspects:\n- SoC is monolithic (single die) but NPU IP block is third-party hard macro\n- NPU communicates via AXI slave interface — no dedicated security interface\n- NPU firmware loaded by CPU at boot — no secure boot chain for NPU firmware\n\nSecurity context:\n- Edge AI for autonomous vehicle perception pipeline\n- NPU processes LiDAR/camera sensor data — safety-critical\n- GPU renders driver display — safety-relevant\n- DSP fuses radar + ultrasonic — safety-critical\n- Threat model: remote attacker (OTA), local attacker (physical access to vehicle ECU)\n\nMaturity: early-adoption (NPU first-gen, PQC migration in progress).\nSoC family: Automotive Edge AI. Technology domain: Heterogeneous Compute, Post-Quantum Cryptography, AI Accelerator Security.",
  "context": "Multi-paradigm SoC: heterogeneous compute (CPU/GPU/NPU/DSP), PQC migration, third-party NPU IP. Automotive safety-critical application. Full security audit covering cross-compute isolation, PQC migration risk, NPU integrity, and interconnect security. Tier 3 complexity — multiple paradigm interactions."
}
```

## Expected Output
A comprehensive heterogeneous compute security audit covering:
- Cross-compute isolation findings for all compute element pairs
- PQC migration risk findings (hybrid mode, SW-only PQC on security processor)
- NPU third-party IP risks (no secure boot, no security interface)
- Interconnect security (AXI firewall, SMMU, TZASC configuration risks)
- DRAM bus plaintext exposure with safety-critical data in transit
- Paradigm interaction analysis (PQC x heterogeneous compute x AI accelerator)
- Migration readiness assessment for PQC timeline
- DocumentEnvelope with paradigm coverage table and migration risk summary

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains EmergingHWFindings covering at least 3 paradigms: heterogeneous-compute, post-quantum, and ai-accelerator
- [ ] At least 6 total findings across all paradigms
- [ ] Every finding has: paradigm, maturityLevel, confidenceTier, severity, research reference or `[FROM TRAINING]`
- [ ] Cross-compute isolation assessed for at least CPU-NPU and CPU-GPU pairs
- [ ] PQC migration risk assessed for hybrid mode ECDH+ML-KEM
- [ ] NPU firmware integrity risk identified (no secure boot chain for NPU)
- [ ] Paradigm coverage table present showing all analyzed paradigms

### Should Pass (partial credit)
- [ ] SMMU assessment for GPU and NPU — is it configured to enforce per-device address space isolation?
- [ ] TZASC assessment for DRAM region isolation — are safety-critical NPU/DSP regions protected from AP compromise?
- [ ] PQC SW implementation on Cortex-M33 assessed for performance feasibility — ML-DSA signature verification timing
- [ ] Non-coherent NPU/DSP memory access assessed for TOCTOU risks with shared DRAM
- [ ] NPU third-party hard macro assessed as a supply chain risk — untrusted IP block with DMA capability
- [ ] Migration readiness assessment present with timeline (hybrid 2026-2028, PQC-only 2029)
- [ ] Cross-paradigm interaction: PQC key exchange protects OTA channel, but NPU firmware update over OTA is unprotected during hybrid transition

### Bonus
- [ ] Identifies that cache coherency mismatch (CPU-GPU coherent, NPU non-coherent) creates potential for stale data in security-critical operations
- [ ] Assesses DSP sensor fusion integrity — if DSP is compromised, safety-critical perception data is corrupted
- [ ] Notes that ML-DSA-65 signature verification on Cortex-M33 without HW acceleration may cause boot time regression, impacting automotive boot time requirements
- [ ] Recommends NPU attestation mechanism: measured boot for NPU firmware with hash anchored in security processor
- [ ] Migration risk summary table present with risk levels for each migration path

## Raw Trace Log
