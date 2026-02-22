# Kernel Hardening Checklist — Attack Surface Reduction, Debugging Restrictions, and Network/HW Hardening

## Contents

- [3. Attack Surface Reduction](#3-attack-surface-reduction)
  - [3.1 Kernel Module Signing](#31-kernel-module-signing)
  - [3.2 Kexec Restrictions](#32-kexec-restrictions)
  - [3.3 io_uring Restrictions](#33-io_uring-restrictions)
  - [3.4 Sysctl Hardening](#34-sysctl-hardening)
  - [3.5 BPF Restrictions](#35-bpf-restrictions)
  - [3.6 userfaultfd Restrictions](#36-userfaultfd-restrictions)
- [5. HW Security Interface](#5-hw-security-interface)
  - [5.1 IOMMU Enablement](#51-iommu-enablement)
  - [5.2 SMMU Configuration (ARM)](#52-smmu-configuration-arm)
  - [5.3 DMA Protection](#53-dma-protection)
  - [5.4 MTE Mode Configuration](#54-mte-mode-configuration)
  - [5.5 CET / Shadow Stack (x86)](#55-cet--shadow-stack-x86)
  - [5.6 Pointer Authentication (arm64)](#56-pointer-authentication-arm64)
- [Quick Reference: Priority Configuration](#quick-reference-priority-configuration)

## 3. Attack Surface Reduction

### 3.1 Kernel Module Signing

- **Description:** Cryptographically signs kernel modules at build time and optionally enforces signature verification at load time, preventing unsigned or tampered modules from being loaded.
- **Kconfig:** `CONFIG_MODULE_SIG=y`, `CONFIG_MODULE_SIG_FORCE=y` (enforcement), `CONFIG_MODULE_SIG_SHA512=y`
- **Verification:** `cat /proc/sys/kernel/modules_disabled` and `zcat /proc/config.gz | grep MODULE_SIG`
- **Security Impact:** HIGH — Without module signing enforcement, an attacker with root can load arbitrary kernel modules to install rootkits, keyloggers, or bypass all security controls. `CONFIG_MODULE_SIG_FORCE=y` is required; `CONFIG_MODULE_SIG=y` alone only warns.

### 3.2 Kexec Restrictions

- **Description:** Controls whether kexec can be used to load and boot a new kernel from the running kernel. Unrestricted kexec allows bypassing secure boot, kernel lockdown, and all runtime security controls.
- **Kconfig:** `CONFIG_KEXEC=n` (disable entirely) or `CONFIG_KEXEC_SIG=y` (require signed images)
- **Verification:** `zcat /proc/config.gz | grep KEXEC`
- **Security Impact:** HIGH — kexec with unsigned images allows replacing the running kernel with an attacker-controlled one, bypassing secure boot chain, kernel lockdown, and all integrity protections.

### 3.3 io_uring Restrictions

- **Description:** Controls access to io_uring, which provides a high-performance asynchronous I/O interface but exposes a large kernel attack surface with high historical CVE density.
- **Kconfig:** `CONFIG_IO_URING=n` (disable entirely if not needed)
- **Sysctl:** `kernel.io_uring_disabled=2` (disable for all), `=1` (disable for unprivileged)
- **Verification:** `sysctl kernel.io_uring_disabled` and `zcat /proc/config.gz | grep IO_URING`
- **Security Impact:** CRITICAL — io_uring has been the source of numerous critical kernel vulnerabilities. It bypasses seccomp-BPF in many configurations. Disable if not required by workload. Google, Microsoft, and others have disabled io_uring in production.

### 3.4 Sysctl Hardening

- **Description:** Runtime kernel parameter hardening via sysctl to restrict dangerous interfaces and enable security features.
- **Key Settings:**
  ```
  kernel.kptr_restrict=2          # Hide kernel pointers from all users
  kernel.dmesg_restrict=1         # Restrict dmesg to root
  kernel.perf_event_paranoid=3    # Restrict perf_events
  kernel.unprivileged_bpf_disabled=1  # Restrict BPF
  kernel.yama.ptrace_scope=2     # Restrict ptrace to root+CAP_SYS_PTRACE
  kernel.unprivileged_userns_clone=0  # Restrict user namespaces (if supported)
  net.core.bpf_jit_harden=2      # Harden BPF JIT
  vm.mmap_min_addr=65536          # Prevent NULL pointer exploitation
  vm.unprivileged_userfaultfd=0   # Restrict userfaultfd
  fs.protected_symlinks=1         # Symlink protection
  fs.protected_hardlinks=1        # Hardlink protection
  fs.protected_fifos=2            # FIFO protection
  fs.protected_regular=2          # Regular file protection
  ```
- **Verification:** `sysctl -a | grep <parameter>`
- **Security Impact:** HIGH — Each parameter addresses a specific attack vector. `kptr_restrict` prevents KASLR bypass via /proc/kallsyms. `perf_event_paranoid` prevents information leakage. `ptrace_scope` prevents process injection.

### 3.5 BPF Restrictions

- **Description:** Controls access to the BPF subsystem, which allows loading programs into the kernel. Unprivileged BPF access has been used in multiple privilege escalation exploits.
- **Kconfig:** `CONFIG_BPF_UNPRIV_DEFAULT_OFF=y`
- **Sysctl:** `kernel.unprivileged_bpf_disabled=1`
- **Verification:** `sysctl kernel.unprivileged_bpf_disabled`
- **Security Impact:** HIGH — BPF programs run inside the kernel and have access to kernel data structures. Verifier bugs have led to arbitrary kernel read/write. Restrict to CAP_BPF/CAP_SYS_ADMIN.

### 3.6 userfaultfd Restrictions

- **Description:** Controls access to the userfaultfd mechanism, which allows user-space handling of page faults. Commonly abused in kernel exploitation to win race conditions by stalling kernel execution at controlled points.
- **Sysctl:** `vm.unprivileged_userfaultfd=0`
- **Verification:** `sysctl vm.unprivileged_userfaultfd`
- **Security Impact:** HIGH — userfaultfd is the most reliable primitive for kernel race condition exploitation. Restricting it to privileged users blocks a key exploitation technique.

## 5. HW Security Interface

### 5.1 IOMMU Enablement

- **Description:** Enables the Input/Output Memory Management Unit to restrict DMA access from I/O devices to only the memory regions explicitly mapped for them. Prevents DMA attacks from malicious or compromised devices.
- **Kconfig:** `CONFIG_IOMMU_SUPPORT=y`, `CONFIG_INTEL_IOMMU=y` (Intel VT-d) or `CONFIG_ARM_SMMU_V3=y` (ARM)
- **Boot params:** `intel_iommu=on iommu=strict` (x86) or `iommu.passthrough=0 iommu.strict=1`
- **Verification:** `dmesg | grep -i iommu` and `ls /sys/class/iommu/`
- **Security Impact:** CRITICAL — Without IOMMU, any DMA-capable device can read/write arbitrary physical memory, bypassing all software security controls. IOMMU strict mode ensures DMA mappings are unmapped immediately after use (vs. lazy unmapping).

### 5.2 SMMU Configuration (ARM)

- **Description:** ARM System Memory Management Unit provides address translation and access control for device-initiated memory transactions on ARM platforms.
- **Kconfig:** `CONFIG_ARM_SMMU=y` (SMMUv2) or `CONFIG_ARM_SMMU_V3=y` (SMMUv3)
- **Verification:** `dmesg | grep -i smmu` and check stream ID to device mappings
- **Security Impact:** CRITICAL — Equivalent to IOMMU on ARM. SMMUv3 adds features like HTTU (Hardware Translation Table Update), PRI (Page Request Interface), and STALL model. Stream ID misconfiguration can allow device cross-access.

### 5.3 DMA Protection

- **Description:** Multiple layers of DMA protection beyond basic IOMMU: bounce buffering for untrusted devices, SWIOTLB for devices with limited addressing, and per-device DMA masks.
- **Kconfig:** `CONFIG_SWIOTLB=y`, `CONFIG_DMA_RESTRICTED_POOL=y`
- **Boot params:** `swiotlb=force` (force bounce buffering)
- **Verification:** `dmesg | grep -i swiotlb` and `cat /sys/kernel/debug/swiotlb/io_tlb_nslabs`
- **Security Impact:** HIGH — Bounce buffering ensures untrusted devices cannot retain stale DMA mappings. Restricted DMA pools limit the memory regions accessible to specific devices.

### 5.4 MTE Mode Configuration

- **Description:** Configures how Memory Tagging Extension operates — synchronous (immediate fault on mismatch), asymmetric (sync for reads, async for writes), or asynchronous (deferred reporting).
- **Kconfig:** `CONFIG_ARM64_MTE=y`, `CONFIG_KASAN_HW_TAGS=y`
- **Verification:** `cat /sys/devices/system/cpu/cpu0/mte_tcf_preferred`
- **Security Impact:** HIGH — Synchronous mode provides immediate detection but higher performance cost (~3-5%). Asymmetric mode balances security and performance. Asynchronous mode has lowest cost but may miss transient violations. Mode selection depends on deployment context.

### 5.5 CET / Shadow Stack (x86)

- **Description:** Intel Control-flow Enforcement Technology provides shadow stacks (for return address protection) and indirect branch tracking (for forward-edge CFI).
- **Kconfig:** `CONFIG_X86_USER_SHADOW_STACK=y`, `CONFIG_X86_KERNEL_IBT=y`
- **Verification:** `dmesg | grep -i cet` or `grep -o shstk /proc/cpuinfo`
- **Security Impact:** HIGH — Hardware-enforced control-flow integrity. Shadow stacks prevent ROP by protecting return addresses. IBT prevents JOP/COP by requiring ENDBR instructions at indirect branch targets.

### 5.6 Pointer Authentication (arm64)

- **Description:** ARMv8.3-A feature that embeds a cryptographic signature (PAC) in unused bits of pointers. Forged or corrupted pointers fail authentication, preventing control-flow hijacking.
- **Kconfig:** `CONFIG_ARM64_PTR_AUTH=y`, `CONFIG_ARM64_PTR_AUTH_KERNEL=y`
- **Verification:** `grep -o paca /proc/cpuinfo`
- **Security Impact:** HIGH — Probabilistic control-flow integrity for both forward-edge (function pointers) and backward-edge (return addresses). Can be combined with BTI (Branch Target Identification) for comprehensive CFI.

## Quick Reference: Priority Configuration

For environments where not all hardening can be applied, prioritize in this order:

| Priority | Category | Key Settings | Rationale |
|----------|----------|-------------|-----------|
| P0 | IOMMU | `iommu=strict`, enforce IOMMU groups | DMA attacks bypass all software controls |
| P1 | Memory protection | KASLR, KPTI, SMAP/SMEP | Kernel exploit mitigations |
| P2 | Privilege reduction | seccomp-BPF, capabilities, lockdown | Reduce attack surface and blast radius |
| P3 | Attack surface | Disable io_uring, restrict BPF/userfaultfd | Remove unnecessary kernel interfaces |
| P4 | Integrity | Module signing, IMA, dm-verity | Prevent persistent compromise |
| P5 | Information hiding | kptr_restrict, dmesg_restrict, perf_paranoid | Prevent information gathering |
