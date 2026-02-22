# Eval Case: UCIe Interface Security Analysis

## Metadata
- **Case ID:** EH-003
- **Tier:** 2 (medium)
- **Skill Route:** emerging-hw-security-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Perform a security analysis of the UCIe interface implementation in our multi-chiplet AI inference SoC. Details:\n\nChiplet topology:\n- Host die: CPU + security processor (in-house, 3nm)\n- Accelerator die 0: NPU with 64 TOPS (third-party IP, packaged at our OSAT)\n- Accelerator die 1: NPU with 64 TOPS (same third-party IP, different production lot)\n- IO die: PCIe 6.0 + Ethernet (in-house, 5nm)\n\nUCIe implementation:\n- UCIe 1.1 with advanced packaging (silicon bridge)\n- Raw D2D bandwidth: 32 GT/s per lane, 16 lanes per link\n- IDE (Integrity and Data Encryption) implemented on Host-to-Accelerator links\n- IDE uses AES-256-GCM with per-link keys\n- IDE NOT implemented on Host-to-IO die link (performance concern — 200ns latency overhead)\n- Key establishment: SPDM 1.3 mutual authentication at boot\n- Key rotation: every 2^32 packets (AES-GCM IV exhaustion prevention)\n- Retimer: one retimer hop between Host and Accelerator die 0\n\nTrust model:\n- Host die: Root of Trust, fully trusted\n- Accelerator dies: authenticated via SPDM, trusted after authentication, third-party IP\n- IO die: trusted (in-house), no IDE (plaintext link)\n- Retimer: untrusted — third-party component in the link path\n\nMaturity: early-adoption. UCIe 1.1 spec (published 2023).\nSoC family: AI Inference. Technology domain: Chiplet/UCIe Architecture.",
  "context": "Multi-chiplet SoC with selective IDE deployment. IDE on accelerator links, no IDE on IO link. Untrusted retimer in the path. SPDM for authentication. Key rotation for GCM IV management. Medium complexity — need to assess IDE coverage gaps and retimer risks."
}
```

## Expected Output
EmergingHWFindings covering:
- Unprotected Host-to-IO link (no IDE) as a data exposure gap
- Retimer as an untrusted entity in the IDE-protected path — can it observe/modify traffic?
- SPDM mutual authentication effectiveness for third-party accelerator dies
- AES-GCM IV exhaustion risk with key rotation at 2^32 packets
- IDE latency vs. security trade-off on the IO link
- Cross-paradigm interaction if accelerator processes sensitive inference data

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains at least 2 EmergingHWFindings for UCIe security risks
- [ ] Finding specifies paradigm as chiplet-ucie
- [ ] Unprotected Host-to-IO link explicitly identified as a security gap
- [ ] Retimer trust status assessed — untrusted component in an IDE-protected link
- [ ] Every finding has confidence tier, severity, and research reference or `[FROM TRAINING]`
- [ ] Maturity level documented as early-adoption

### Should Pass (partial credit)
- [ ] IDE coverage gap analysis: Host-to-IO plaintext link can expose PCIe/Ethernet traffic including DMA data
- [ ] Retimer finding assesses whether IDE encryption is end-to-end (Host-to-Accelerator) or hop-by-hop — retimer observability depends on this
- [ ] AES-GCM IV management assessed: 2^32 packet limit is standard but key rotation mechanism must be atomic to avoid plaintext windows
- [ ] SPDM 1.3 authentication assessed for third-party die — what certificate chain anchors trust?
- [ ] Migration risk assessed: UCIe 1.1 spec is early-adoption, future revisions may change IDE requirements

### Bonus
- [ ] Notes that silicon bridge (advanced packaging) provides physical security advantages over organic substrate for interposition resistance
- [ ] Identifies that two accelerator dies from different production lots creates a supply chain verification challenge — each lot needs independent attestation
- [ ] Assesses whether IDE latency overhead (200ns) is actually security-justified for the IO link given the threat model

## Raw Trace Log
