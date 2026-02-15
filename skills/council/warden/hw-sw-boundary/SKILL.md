---
name: hw-sw-boundary
department: "warden"
description: "Use when reviewing the hardware/software security interface to verify hardware security feature enablement, IOMMU/SMMU DMA protection configuration, and HW/SW trust model coherence. Covers boot chain verification, memory protection, and control flow integrity features. Do not use for kernel configuration audit (use kernel-hardening) or isolation boundary analysis (use isolation-review)."
version: 1
triggers:
  - "IOMMU"
  - "SMMU"
  - "DMA"
  - "MTE"
  - "PAC"
  - "TrustZone"
  - "MMU"
  - "hardware security"
  - "device isolation"
  - "firmware"
  - "boot security"
---

# HW/SW Boundary

## Purpose
Review the hardware/software security interface to verify that hardware security features are correctly enabled by software, IOMMU/SMMU provides adequate DMA protection, and the HW/SW trust model is coherent and complete.

## Scope Constraints

Reads kernel configuration, firmware settings, device trees, and hardware documentation. Does not modify kernel configuration or firmware. Does not execute commands on production systems.

## Inputs
- Hardware platform specification (CPU features, IOMMU/SMMU, security extensions)
- Kernel/firmware configuration for hardware security features
- Device tree or ACPI tables defining hardware topology
- DMA-capable devices and their trust classification
- Boot chain architecture (ROM → bootloader → kernel)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Step 1: Map HW Security Features
Enumerate all hardware security features available on the platform:
- **Memory protection**: MMU, MTE (ARM), MPX (x86, deprecated), MPK (x86)
- **Control flow**: PAC (ARM), CET (x86), BTI (ARM), IBT (x86)
- **Isolation**: TrustZone (ARM), SGX/TDX (x86), SEV (AMD), PEF (POWER)
- **DMA protection**: IOMMU (x86), SMMU (ARM), DART (Apple)
- **Debug**: Debug authentication, secure debug, JTAG lockout
- **Tamper**: Secure boot, measured boot, anti-rollback counters

### Step 2: Verify Kernel Enables HW Features
For each hardware security feature, verify the kernel/firmware enables it:
- Is the feature compiled into the kernel (CONFIG option)?
- Is the feature enabled at runtime (boot parameter, sysfs, not just compiled)?
- Are the feature's parameters set to security-optimal values?
- Is the feature enabled for all relevant contexts (all cores, all processes)?
- Document any features present in silicon but disabled in software

### Step 3: Check IOMMU/SMMU Config
Review DMA protection configuration:
- Is IOMMU/SMMU enabled in the boot chain (firmware + kernel)?
- Are all DMA-capable devices assigned to IOMMU groups?
- Are devices in passthrough mode? (Passthrough = no DMA protection)
- Are IOMMU page tables configured with appropriate granularity?
- Is the IOMMU configured to block by default (deny untranslated DMA)?
- Are device-to-memory mappings minimal (least-privilege DMA)?

### Step 4: Assess DMA Protection
Evaluate the completeness of DMA protection:
- Can any device DMA to kernel memory?
- Can any device DMA to another device's memory?
- Are pre-boot DMA attacks mitigated (Thunderbolt, PCI hot-plug)?
- Is bounce buffering used for devices that need limited DMA?
- Are DMA buffers zeroed after use to prevent information leakage?

### Step 5: Review HW/SW Trust Model
Assess the coherence of the hardware/software trust model:
- Does the boot chain establish a valid root of trust?
- Are hardware security features relied upon without verifying their enablement?
- Does the software trust model match the hardware isolation boundaries?
- Are there assumptions about hardware behavior that are not guaranteed by the spec?
- Is the firmware update path secured (signed firmware, anti-rollback)?

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, then resume from the earliest incomplete step.

## Output Format

### HW Security Feature Matrix

| Feature | Available | Enabled (FW) | Enabled (Kernel) | Config | Status |
|---------|-----------|-------------|------------------|--------|--------|
| SMMU | Yes | Yes | Yes | No passthrough | PASS |
| MTE | Yes | N/A | No | — | FAIL — not enabled |
| PAC | Yes | N/A | Yes | APIA+APIB | PASS |
| ... | ... | ... | ... | ... | ... |

### DMA Protection Assessment

| Device | IOMMU Group | Mode | DMA Range | Risk | Recommendation |
|--------|-------------|------|-----------|------|----------------|
| NVMe SSD | Group 1 | Translated | 64MB region | Low | Acceptable |
| GPU | Group 3 | Passthrough | All memory | Critical | Enable translation |
| ... | ... | ... | ... | ... | ... |

### Trust Model Diagram
```
┌─────────────────────────────────────────┐
│ Hardware Root of Trust (ROM)            │
│  └→ Signed Bootloader                  │
│       └→ Signed Kernel                  │
│            ├→ SMMU enabled (DMA prot)   │
│            ├→ PAC enabled (CFI)         │
│            └→ MTE disabled ← GAP       │
└─────────────────────────────────────────┘
```

### HW/SW Trust Gap Summary

| Gap | Risk | Impact | Remediation | Priority |
|-----|------|--------|-------------|----------|
| MTE not enabled | Memory safety bugs exploitable | High | Enable MTE in kernel config | High |
| ... | ... | ... | ... | ... |

## Handoff

- Hand off to kernel-hardening if kernel configuration changes are needed based on HW/SW boundary findings.
- Hand off to isolation-review if isolation boundary issues are discovered during trust model review.

## Quality Checks
- [ ] All hardware security features enumerated for the platform
- [ ] Each feature verified as enabled in both firmware and kernel
- [ ] IOMMU/SMMU configuration reviewed for all DMA-capable devices
- [ ] No devices in passthrough mode without explicit justification
- [ ] Boot chain trust model verified from ROM to kernel
- [ ] Firmware update path secured (signatures, anti-rollback)
- [ ] HW/SW trust model is coherent (software assumptions match hardware guarantees)

## Evolution Notes
<!-- Observations appended after each use -->
