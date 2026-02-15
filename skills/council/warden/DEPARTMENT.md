---
name: "Warden Department"
executive: "Warden"
color: "Slate"
description: "OS kernel security, process isolation, privilege boundaries, HW/SW security interface"
---

# Warden Department — Slate Lens

The Warden's department of focused skills for reviewing isolation boundaries, auditing kernel hardening, and assessing the hardware/software security interface.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [isolation-review](isolation-review/SKILL.md) | Isolation boundary analysis and bypass testing | default | `isolation`, `container`, `namespace`, `seccomp`, `enclave`, `TEE`, `sandbox` |
| [kernel-hardening](kernel-hardening/SKILL.md) | Kernel security configuration audit | default | `kernel`, `syscall`, `KASLR`, `CFI`, `SMAP`, `SMEP`, `hardening` |
| [hw-sw-boundary](hw-sw-boundary/SKILL.md) | HW/SW security interface review | default | `IOMMU`, `SMMU`, `DMA`, `MTE`, `PAC`, `TrustZone`, `MMU` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Isolation, container, namespace, seccomp, enclave, TEE, sandbox, VM, privilege separation | isolation-review | High |
| Kernel, syscall, KASLR, CFI, SMAP, SMEP, hardening, kernel config, SELinux | kernel-hardening | High |
| IOMMU, SMMU, DMA, MTE, PAC, TrustZone, MMU, hardware security, firmware, boot security | hw-sw-boundary | High |
| Process isolation with kernel hardening scope | isolation-review then kernel-hardening | Medium |
| Hardware feature enablement with kernel config | hw-sw-boundary then kernel-hardening | Medium |

## Load Directive

Load one specialist skill at a time using the Skill tool. Read the classification logic table to select the appropriate specialist, then invoke the skill. Do not pre-load multiple specialists simultaneously.

## Handoff Protocol

When the specialist skill output reveals issues in another department's domain:
1. Complete the current skill's output format.
2. Note the cross-domain findings in the output.
3. Recommend loading the appropriate department and skill (e.g., "Hand off hardware security feature findings to forge/rtl-security-review for RTL-level verification").
