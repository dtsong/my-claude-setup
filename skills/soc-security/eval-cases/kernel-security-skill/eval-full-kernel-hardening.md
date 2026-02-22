# Eval Case: Full Kernel Hardening Review Across Memory, Access, and Surface

## Metadata
- **Case ID:** KS-005
- **Tier:** 3 (complex)
- **Skill Route:** kernel-security-skill
- **Estimated Complexity:** high

## Input
```json
{
  "user_prompt": "Perform a full kernel hardening review for our ARM-based confidential computing server SoC. This system runs multi-tenant confidential AI workloads with strict isolation requirements. We need all five phases of the kernel security analysis.\n\nKernel: Linux 6.8.15, aarch64\nDistro: Custom Yocto-based, minimal\nHypervisor: KVM with cloud-hypervisor (rust-based VMM)\nLSM: SELinux (enforcing) + Landlock (enabled)\nContainer runtime: kata-containers (VM-isolated containers)\n\nKernel config (abbreviated — security-relevant options):\n# Memory Protection\nCONFIG_RANDOMIZE_BASE=y\nCONFIG_ARM64_PTR_AUTH=y\nCONFIG_ARM64_BTI=y\nCONFIG_ARM64_MTE=y\nCONFIG_KASAN=n (disabled for production)\nCONFIG_KFENCE=y\nCONFIG_INIT_ON_ALLOC_DEFAULT_ON=y\nCONFIG_INIT_ON_FREE_DEFAULT_ON=y\nCONFIG_STACKPROTECTOR_STRONG=y\nCONFIG_SHADOW_CALL_STACK=y\nCONFIG_CFI_CLANG=y\n\n# Access Control\nCONFIG_SECURITY_LOCKDOWN_LSM=y\nCONFIG_LOCK_DOWN_KERNEL_FORCE_CONFIDENTIALITY=y\nCONFIG_MODULE_SIG_FORCE=y\nCONFIG_KEXEC=n\nCONFIG_KPROBES=n\nCONFIG_BPF_UNPRIV_DEFAULT_OFF=y\nCONFIG_SECURITY_LANDLOCK=y\n\n# Attack Surface\nCONFIG_IO_URING=n\nCONFIG_DEVMEM=n\nCONFIG_FTRACE=n\nCONFIG_PERF_EVENTS=y\nCONFIG_BPF_SYSCALL=y\nCONFIG_BPF_JIT=y\nCONFIG_BPF_JIT_ALWAYS_ON=y\nCONFIG_USERFAULTFD=y\nCONFIG_USER_NS=y\n\n# IOMMU\nCONFIG_ARM_SMMU_V3=y\nCONFIG_IOMMU_DEFAULT_DMA_STRICT=y\nCONFIG_VFIO=y\nCONFIG_VFIO_PCI=y\n\nBoot params: lockdown=confidentiality arm64.nosme=1 arm64.nomte=0 iommu.strict=1 kpti=1\n\nHardware:\n- ARM Neoverse V2 (ARMv9.0-A)\n- PAC (Pointer Authentication), BTI (Branch Target Identification), MTE (Memory Tagging Extension)\n- SME (Scalable Matrix Extension) — disabled via boot param\n- ARM SMMUv3 with RME (Realm Management Extension) support\n- CCA (Confidential Compute Architecture) — hardware present but not yet enabled in kernel\n- TrustZone EL3 + RME Realms at R-EL2\n\nCapabilities: kata-containers VMs run with minimal caps (CAP_NET_BIND_SERVICE only)\nSeccomp: kata-agent applies restrictive profile (default deny, ~60 allowed syscalls, no io_uring/ptrace/mount/bpf)\n\nDeployment: Multi-tenant confidential AI cloud, ARM CCA target platform\nCompliance: CIS Level 2, KSPP recommendations\nSoC family: data-center\nTechnology domain: confidential-ai",
  "context": "Full 5-phase kernel hardening review on a well-hardened system. This is a mature configuration with many best practices already applied. The skill should identify remaining gaps and areas for improvement rather than listing obvious failures. Key areas: ARM CCA not enabled (major gap for confidential compute), perf_events still accessible, BPF JIT always-on, userfaultfd enabled, user namespaces enabled, SME disabled. Kata-containers provide VM isolation for containers. All five phases should be exercised."
}
```

## Expected Output
A complete 5-phase kernel security analysis producing:
- Phase 1: Kernel config audit against CIS Level 2 and KSPP with high pass rate
- Phase 2: Isolation boundary mapping including kata-containers VM isolation, SELinux, Landlock, and SMMU
- Phase 3: Remaining attack surface enumeration (perf, BPF, userfaultfd, user namespaces)
- Phase 4: Privilege escalation paths in a well-hardened environment
- Phase 5: DocumentEnvelope with KernelSecFinding entities, subsystem coverage table, and confidence summary

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] All five phases of the kernel security analysis are executed and reported
- [ ] ARM CCA not enabled flagged as a significant gap — hardware present but not leveraged for confidential compute
- [ ] High CIS/KSPP pass rate acknowledged — this is a well-hardened system, not a failing one
- [ ] Remaining attack surfaces identified: perf_events, BPF JIT, userfaultfd, user namespaces
- [ ] Kernel subsystem coverage table present with ANALYZED/NOT ANALYZED markings for all subsystems
- [ ] KernelSecFinding entities produced for each finding with full schema compliance
- [ ] Every finding documents HW/SW interface context — ARM-specific features (PAC, BTI, MTE, CCA) assessed

### Should Pass (partial credit)
- [ ] Memory protection assessed positively: PAC, BTI, MTE, shadow call stacks, CFI, KFENCE, init-on-alloc/free
- [ ] Lockdown=confidentiality assessed as strong — prevents most kernel tampering from userspace
- [ ] kata-containers VM isolation assessed as superior to namespace-only container isolation for multi-tenant
- [ ] SMMUv3 strict mode with VFIO assessed for DMA protection of GPU pass-through
- [ ] SME disabled via boot param assessed — rationale needed (side-channel concern or unused)
- [ ] BPF_JIT_ALWAYS_ON assessed — JIT required means JIT spray attacks relevant, but unprivileged BPF disabled mitigates
- [ ] Escalation paths analysis reflects hardened environment — fewer viable paths, higher prerequisites

### Bonus
- [ ] ARM CCA/RME Realm architecture assessed — what enabling it would provide for confidential AI isolation
- [ ] Landlock + SELinux layered LSM interaction assessed for defense-in-depth
- [ ] Cloud-hypervisor (rust-based VMM) assessed for reduced attack surface vs. QEMU
- [ ] userfaultfd assessed as kernel exploitation primitive (heap manipulation via controlled page faults)
- [ ] Comparison to KSPP ideal configuration with delta items listed

## Raw Trace Log
