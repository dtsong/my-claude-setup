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

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
