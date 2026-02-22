---
name: kernel-sec
description: Run kernel security analysis for a SoC platform
---

# /soc-security:kernel-sec

Analyze kernel security configuration and HW/SW security interfaces. This command activates the kernel-security-skill to assess kernel hardening, isolation mechanisms, privilege escalation paths, and hardware security feature utilization.

## Usage

```
/soc-security:kernel-sec
/soc-security:kernel-sec "Review kernel security for our data-center Linux deployment with SR-IOV"
/soc-security:kernel-sec --family data-center --focus iommu,isolation
```

## What Happens

1. **Kernel configuration analysis:** Claude asks for the kernel config, deployed security features, and hardware platform details. Checks against CIS/KSPP benchmarks.
2. **Isolation boundary mapping:** Maps privilege levels, process isolation mechanisms, and HW/SW security boundaries.
3. **Attack surface enumeration:** Enumerates syscall surface, io_uring exposure, module surface, and debug interfaces.
4. **Privilege escalation path analysis:** Identifies paths from user to kernel, container escape paths, IOMMU bypass paths, and kernel-to-hypervisor paths.
5. **Output generation:** Produces a kernel security assessment with KernelSecFinding entities and kernel subsystem mapping.

## Analysis Areas

| Area | Coverage |
|------|---------|
| Memory protection | KASLR, KPTI, SMAP, SMEP, MTE, shadow stacks |
| Process isolation | seccomp-BPF, namespaces, cgroups, capabilities, Landlock |
| HW security interface | IOMMU/SMMU, DMA protection, MTE mode, PMP |
| Kernel integrity | dm-verity, IMA, EVM, module signing |
| Attack surface | io_uring, syscall surface, module loading, debug interfaces |

## Output

The assessment is saved as a `kernel-security-model` DocumentEnvelope with KernelSecFinding entities, privilege escalation path map, and hardening gap analysis.

## Next Step

After kernel security analysis, findings can feed into:
- `/soc-security:threat-model` — incorporate kernel findings into component threat models
- `/soc-security:comply` — map findings to Common Criteria kernel security requirements
- `/soc-security:formalize` — formalize isolation properties in TLA+

## Skill Reference

This command invokes the [kernel-security-skill](../kernel-security-skill/SKILL.md). See also:
- [kernel-hardening-checklist.md](../kernel-security-skill/references/kernel-hardening-checklist.md) — comprehensive hardening checklist
- [isolation-mechanism-catalog.md](../kernel-security-skill/references/isolation-mechanism-catalog.md) — isolation mechanism catalog
- [kernel-attacks.md](../shared-references/soc-security/threat-catalog/kernel-attacks.md) — kernel attack catalog (KERN-001 to KERN-015)
