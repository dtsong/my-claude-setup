---
name: kernel-hardening
department: "warden"
description: "Use when auditing kernel security configuration for memory protection, syscall surface reduction, control flow integrity, and integrity mechanisms against local and remote attack vectors. Covers CIS/KSPP benchmarks, KASLR, SMAP/SMEP, seccomp, and secure boot chain. Do not use for isolation boundary analysis (use isolation-review) or HW/SW interface review (use hw-sw-boundary)."
version: 1
triggers:
  - "kernel"
  - "syscall"
  - "KASLR"
  - "CFI"
  - "SMAP"
  - "SMEP"
  - "hardening"
  - "kernel config"
  - "seccomp"
  - "SELinux"
  - "integrity"
---

# Kernel Hardening

## Purpose
Audit kernel security configuration for memory protection, syscall surface reduction, integrity mechanisms, and overall hardening completeness against both local and remote attack vectors.

## Scope Constraints

Reads kernel configuration files, boot parameters, and system runtime settings. Does not modify kernel configuration or execute system commands. Does not access production kernels.

## Inputs
- Kernel configuration (Kconfig/.config or equivalent)
- Target platform and architecture (x86_64, ARM64, RISC-V)
- Threat model (local unprivileged attacker, remote attacker, physical attacker)
- Deployment context (server, embedded, mobile, desktop)
- Compliance requirements (STIG, CIS benchmarks)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Step 1: Audit Kernel Config
Review kernel configuration for security-critical options:
- **Memory protections**: KASLR, SMAP/SMEP (x86) or PAN/PXN (ARM), stack canaries, KASAN, KMSAN
- **Control flow**: CFI (Clang CFI, IBT, BTI), shadow call stacks, ROP mitigations
- **Exploit mitigations**: FORTIFY_SOURCE, HARDENED_USERCOPY, REFCOUNT_FULL, INIT_STACK_ALL
- **Module restrictions**: MODULE_SIG_FORCE, SECURITY_LOCKDOWN_LSM, LOCK_DOWN_KERNEL_FORCE_INTEGRITY
- **Debug surface**: Disable CONFIG_DEBUG_FS in production, restrict /proc and /sys exposure

### Step 2: Check Memory Protections
Verify that memory protection mechanisms are enabled and effective:
- ASLR entropy: kernel (KASLR), user (full ASLR), mmap randomization
- Page table isolation (KPTI/KAISER) enabled for Meltdown mitigation
- W^X enforcement: no pages simultaneously writable and executable
- Stack protections: guard pages, stack canaries, shadow stacks
- MTE (ARM) or memory tagging enabled where available
- SLAB hardening: SLAB_FREELIST_RANDOM, SLAB_FREELIST_HARDENED

### Step 3: Review Syscall Surface
Assess the kernel's syscall attack surface:
- Are unused syscalls disabled or filtered?
- Is seccomp-bpf available and used by critical services?
- Are dangerous syscalls restricted (kexec_load, ptrace, mount, unshare)?
- Are ioctl handlers for exposed devices audited?
- Is userfaultfd restricted (USERFAULTFD_SYSCTL)?
- Are unprivileged user namespaces disabled where not needed?

### Step 4: Verify Integrity Mechanisms
Check kernel integrity protections:
- Secure boot chain verified (UEFI Secure Boot → signed kernel → signed modules)
- dm-verity or equivalent for rootfs integrity
- IMA/EVM for runtime file integrity monitoring
- Kernel lockdown mode (integrity or confidentiality level)
- Module signature enforcement (no unsigned modules loaded)

### Step 5: Assess Hardening Completeness
Score the overall hardening posture:
- Compare against CIS Benchmark or KSPP recommendations
- Identify gaps between current config and target security profile
- Prioritize remediation by exploitability and impact
- Note performance trade-offs for each hardening recommendation
- Verify that hardening options are actually active at runtime (not just compiled in)

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, then resume from the earliest incomplete step.

## Output Format

### Kernel Hardening Scorecard

| Category | Config Option | Expected | Actual | Status | Impact |
|----------|-------------|----------|--------|--------|--------|
| Memory | CONFIG_RANDOMIZE_BASE (KASLR) | y | y | PASS | — |
| Memory | CONFIG_PAGE_TABLE_ISOLATION | y | n | FAIL | Meltdown exposure |
| ... | ... | ... | ... | ... | ... |

### Syscall Surface Assessment
- Total syscalls available: [N]
- Syscalls restricted by seccomp: [M]
- Dangerous syscalls unrestricted: [List]
- Recommendation: [Specific seccomp profile changes]

### Integrity Chain
```
UEFI Secure Boot → [Verified/Not Verified]
  └→ Signed Kernel → [Verified/Not Verified]
       └→ Signed Modules → [Verified/Not Verified]
            └→ dm-verity rootfs → [Verified/Not Verified]
                 └→ IMA/EVM runtime → [Verified/Not Verified]
```

### Hardening Gap Summary

| Gap | Risk | Remediation | Performance Cost | Priority |
|-----|------|-------------|-----------------|----------|
| KPTI disabled | Meltdown vulnerability | Enable CONFIG_PAGE_TABLE_ISOLATION | ~5% syscall overhead | Critical |
| ... | ... | ... | ... | ... |

## Handoff

- Hand off to isolation-review if isolation mechanism improvements are needed based on hardening audit.
- Hand off to hw-sw-boundary if hardware security features should be enabled to support kernel hardening.

## Quality Checks
- [ ] All major hardening categories audited (memory, CFI, syscall, integrity, modules)
- [ ] Configuration checked against a recognized benchmark (CIS, KSPP)
- [ ] Runtime state verified (not just compile-time config)
- [ ] Syscall surface reviewed for unnecessary exposure
- [ ] Integrity chain verified from boot to runtime
- [ ] Performance trade-offs documented for each recommendation
- [ ] Prioritized remediation plan provided

## Evolution Notes
<!-- Observations appended after each use -->
