# Eval Case: Privilege Escalation Attack Surface Analysis

## Metadata
- **Case ID:** KS-004
- **Tier:** 2 (medium)
- **Skill Route:** kernel-security-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Analyze the privilege escalation attack surface of our compute server SoC running a KVM hypervisor workload. The system hosts confidential AI training VMs with GPU pass-through.\n\nKernel: Linux 6.6 LTS, x86_64\nHypervisor: KVM with QEMU 8.2\nLSM: SELinux (enforcing, targeted policy)\n\nKernel config:\nCONFIG_KVM=y\nCONFIG_KVM_INTEL=y\nCONFIG_VFIO=y\nCONFIG_VFIO_PCI=y\nCONFIG_BPF_SYSCALL=y\nCONFIG_BPF_JIT=y\nCONFIG_BPF_UNPRIV_DEFAULT_OFF=y\nCONFIG_IO_URING=y\nCONFIG_SECURITY_LOCKDOWN_LSM=y\nCONFIG_LOCK_DOWN_KERNEL_FORCE_INTEGRITY=n\nCONFIG_LOCK_DOWN_KERNEL_FORCE_CONFIDENTIALITY=n\nCONFIG_MODULE_SIG_FORCE=y\nCONFIG_KEXEC=y\nCONFIG_KEXEC_FILE=y\nCONFIG_KPROBES=y\nCONFIG_FTRACE=y\nCONFIG_PERF_EVENTS=y\nCONFIG_DEVMEM=y\nCONFIG_STRICT_DEVMEM=y\n\nBoot params: lockdown=none kvm-intel.nested=1\n\nHardware: Intel Xeon with VT-x, VT-d, SGX, TME-MK, TXT\nEnabled: VT-x, VT-d, nested virtualization\nDisabled: SGX (not used), TME-MK (not configured), TXT (not used)\n\nDeployment: Multi-tenant confidential AI, GPU pass-through via VFIO, nested virtualization enabled.\nSoC family: data-center\nTechnology domain: confidential-ai",
  "context": "Privilege escalation surface analysis across all four escalation categories (user-to-kernel, container escape, IOMMU bypass, kernel-to-hypervisor). Key issues: lockdown=none despite LSM compiled in, nested virtualization enabled, kexec enabled, debug interfaces (kprobes/ftrace/perf) accessible, /dev/mem present with only STRICT_DEVMEM, unused security features (SGX, TME-MK, TXT). All four Phase 4 sub-steps should be exercised."
}
```

## Expected Output
A comprehensive privilege escalation analysis covering all four categories:
- User-to-kernel: debug interfaces, BPF JIT, io_uring, kexec
- Container escape: (if containers present within VMs)
- IOMMU bypass: VFIO pass-through, nested virtualization DMA
- Kernel-to-hypervisor: VMEXIT handler, nested virt, emulated devices, KVM ioctl

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output covers all four privilege escalation categories from the skill's Phase 4
- [ ] lockdown=none flagged as HIGH/CRITICAL — kernel lockdown LSM compiled but disabled via boot param
- [ ] Nested virtualization (kvm-intel.nested=1) flagged as expanding hypervisor attack surface
- [ ] kexec enabled flagged as kernel code execution path (can load arbitrary kernel)
- [ ] Debug interfaces assessed: kprobes, ftrace, perf_events — all accessible without lockdown
- [ ] KernelSecFinding entities produced with source/target privilege levels for each escalation path

### Should Pass (partial credit)
- [ ] /dev/mem with STRICT_DEVMEM assessed — still allows access to non-RAM regions (PCI MMIO, ACPI)
- [ ] BPF JIT enabled but unprivileged BPF disabled (BPF_UNPRIV_DEFAULT_OFF) — assessed as partial mitigation
- [ ] io_uring assessed for user-to-kernel escalation surface
- [ ] VFIO GPU pass-through assessed for IOMMU bypass through DMA from guest-controlled GPU
- [ ] Unused security features (SGX, TME-MK, TXT) flagged as missed defense-in-depth opportunities
- [ ] Module signing enforced (MODULE_SIG_FORCE=y) assessed as positive control

### Bonus
- [ ] Nested virtualization specific attack: L2 guest -> L1 guest -> host via VMEXIT handler chain
- [ ] TME-MK assessed as critical missing protection for confidential AI workload (memory encryption)
- [ ] SELinux targeted policy assessed for KVM/QEMU confinement effectiveness
- [ ] Specific escalation chain documented with entry point, mechanism, and prerequisites

## Raw Trace Log
