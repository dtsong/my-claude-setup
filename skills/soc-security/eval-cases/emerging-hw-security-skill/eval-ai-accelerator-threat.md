# Eval Case: AI Accelerator Security Threat Assessment

## Metadata
- **Case ID:** EH-004
- **Tier:** 2 (medium)
- **Skill Route:** emerging-hw-security-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Assess the security threat surface of our NPU (Neural Processing Unit) in a mobile SoC. Details:\n\nNPU architecture:\n- Custom matrix multiply engine: 8x8 systolic array, INT8/FP16 mixed precision\n- Local SRAM: 2MB unified weight/activation buffer\n- DMA engine: dedicated DMA for weight loading from DRAM to local SRAM\n- Activation memory: 512KB dedicated scratchpad for intermediate activations\n- Control interface: MMIO registers accessible from application processor (AP) via AXI\n- No memory encryption on weight buffer or activation scratchpad\n- No access control on DMA — AP can program DMA to read any DRAM address into NPU SRAM\n\nSecurity context:\n- NPU runs ML inference for face recognition (biometric authentication)\n- Model weights are proprietary (IP protection requirement)\n- Biometric feature vectors in activation memory are privacy-sensitive\n- NPU shares the DRAM bus with AP, GPU, and DSP (no bus isolation)\n- No TEE integration — NPU operates in Normal World only\n- No attestation mechanism for model integrity\n\nThreat actors:\n- Malicious app on the AP attempting to extract model weights or biometric data\n- Supply chain attacker who modifies model weights to introduce backdoor\n\nMaturity: early-adoption (custom NPU, first generation).\nSoC family: Mobile. Technology domain: AI Accelerator Security.",
  "context": "First-generation NPU in mobile SoC. No memory protection, no TEE integration, no attestation. Processes sensitive biometric data and proprietary model weights. Shared DRAM bus with no isolation. Multiple threat vectors from software and supply chain."
}
```

## Expected Output
EmergingHWFindings covering:
- Model weight extraction via unprotected DMA (malicious AP app reads weight buffer)
- Biometric feature vector leakage from activation scratchpad
- Lack of bus isolation enabling cross-component DRAM snooping
- Model integrity risk — no attestation means backdoored models undetectable
- DMA misconfiguration as a privilege escalation vector

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains at least 2 EmergingHWFindings for AI accelerator security risks
- [ ] Finding specifies paradigm as ai-accelerator
- [ ] Model weight confidentiality risk identified (unprotected weight buffer)
- [ ] Biometric data privacy risk identified (activation scratchpad exposure)
- [ ] Every finding has confidence tier, severity, and research reference or `[FROM TRAINING]`
- [ ] Maturity level documented as early-adoption

### Should Pass (partial credit)
- [ ] Unrestricted DMA engine identified as primary attack vector — AP can program it to exfiltrate any DRAM contents
- [ ] Lack of TEE integration flagged — NPU cannot participate in secure computation for biometric processing
- [ ] Model integrity risk assessed — no attestation mechanism means supply chain or runtime model replacement is undetectable
- [ ] Shared DRAM bus assessed for cross-component information leakage (GPU/DSP could observe NPU traffic patterns)
- [ ] Mitigation recommendations include: DMA firewall/IOMMU, memory encryption for weight/activation buffers, TEE integration, model attestation

### Bonus
- [ ] Notes that systolic array power consumption patterns may leak information about model architecture (model extraction via SCA)
- [ ] Identifies that INT8 quantized weights are smaller and faster to exfiltrate than FP16 — quantization reduces the attacker's bandwidth requirement
- [ ] Recommends TDISP-like mechanism for NPU device isolation if PCIe-attached, or SMMU/IOMMU for AXI-attached NPU

## Raw Trace Log
