# Kernel Attacks — Threat Catalog

## Overview

Kernel attacks target the operating system kernel and its interfaces with hardware security mechanisms. These attacks operate at the hardware/software boundary — exploiting kernel vulnerabilities to subvert hardware-enforced isolation (IOMMU/SMMU, KASLR, SMAP/SMEP), bypass integrity mechanisms (dm-verity, IMA/EVM), or escape containment boundaries (containers, hypervisors). They are particularly relevant to SoC security because kernel compromise can neutralize hardware security features that depend on correct kernel configuration and management.

---

## KERN-001: Kernel Privilege Escalation via Use-After-Free

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E) |
| **Description** | Attacker exploits a use-after-free (UAF) vulnerability in the kernel to gain arbitrary code execution at ring 0 / EL1. The attack proceeds by freeing a kernel object, reclaiming the freed memory with attacker-controlled data (via heap spray or targeted slab allocation), and then triggering the dangling pointer dereference to hijack control flow. UAF bugs in subsystems such as netfilter, io_uring, and filesystem handlers are common vectors. Successful exploitation grants full kernel privileges, bypassing all user-space isolation. |
| **Target Assets** | Kernel heap (SLUB/SLAB allocator), kernel code execution context (ring 0 / EL1), process credentials (struct cred), kernel function pointers |
| **Affected Domains** | Kernel Security (primary), Confidential AI / TEE (kernel compromise can attack TEE interfaces) |
| **Affected SoC Families** | All — Compute, Data Center, Client, IoT |
| **Preconditions** | Local code execution as unprivileged user; reachable UAF vulnerability in kernel code path; ability to influence slab allocator (heap spray) |
| **Key Mitigations** | KASAN (Kernel Address Sanitizer) for detection, CONFIG_SLAB_FREELIST_HARDENED, CONFIG_INIT_ON_FREE_DEFAULT_ON to zero freed memory, CHERI capability revocation to invalidate dangling pointers, CFI (Control-Flow Integrity) to limit code reuse, hardware MTE (Memory Tagging Extension) for probabilistic UAF detection |
| **Verification Approach** | Tier 2 — kernel fuzzing (syzkaller) for UAF discovery; Tier 1 — hardware MTE/CHERI tag validation assertions |
| **Related Requirements** | REQ-CHERI-002 (bounds checking), REQ-CHERI-004 (revocation support) |

---

## KERN-002: Container Escape via Namespace Bypass

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E) |
| **Description** | Attacker within a container exploits kernel vulnerabilities or misconfigurations to break out of Linux namespace isolation (PID, network, mount, user namespaces) and gain access to the host kernel or other containers. Vectors include: exploiting kernel syscall handlers that fail to check namespace boundaries, abusing user namespace to gain capabilities that affect the host, or leveraging shared kernel resources (cgroups, procfs, sysfs) that leak information or control across namespace boundaries. Container escapes are critical in multi-tenant SoC deployments where containers share a kernel. |
| **Target Assets** | Linux namespaces (PID, net, mnt, user, cgroup), container runtime (runc, containerd), host kernel resources, cgroup hierarchy |
| **Affected Domains** | Kernel Security (primary), Confidential AI / TEE (containers hosting AI workloads) |
| **Affected SoC Families** | Compute, Data Center (multi-tenant container deployments) |
| **Preconditions** | Code execution inside a container; kernel vulnerability reachable from within namespace; or misconfigured container with excessive capabilities (CAP_SYS_ADMIN) |
| **Key Mitigations** | Minimal kernel attack surface from containers (seccomp-BPF filtering), user namespace restrictions, hardware VM-level isolation (Kata Containers, gVisor with KVM), dropping all unnecessary capabilities, read-only root filesystem, hardware-enforced memory isolation between container groups |
| **Verification Approach** | Tier 2 — container escape test suites; Tier 1 — SVA for namespace boundary enforcement on shared kernel objects |
| **Related Requirements** | REQ-CHERI-007 (compartment isolation), REQ-TDISP-005 (domain access control) |

---

## KERN-003: IOMMU/SMMU Bypass via ATS Misuse

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E), Information Disclosure (I) |
| **Description** | Attacker exploits PCIe Address Translation Services (ATS) to bypass IOMMU/SMMU protection. ATS allows devices to cache address translations in an ATC (Address Translation Cache) on the device side. A malicious or compromised device can send pre-translated memory requests that the IOMMU trusts without re-validating, allowing the device to access arbitrary host memory. This defeats DMA isolation that the kernel configured via IOMMU page tables. The attack is particularly dangerous with CXL devices that use ATS for coherent memory access. |
| **Target Assets** | IOMMU/SMMU translation tables, ATS/ATC (Address Translation Cache on device), host physical memory, DMA buffer isolation |
| **Affected Domains** | Kernel Security (primary), TDISP / CXL (ATS in CXL.cache protocol), Microarchitectural Security |
| **Affected SoC Families** | Data Center (PCIe/CXL devices), Compute (GPU/accelerator with ATS) |
| **Preconditions** | Compromised or malicious PCIe/CXL device with ATS capability; kernel/IOMMU driver that does not validate ATS-translated requests; ATS enabled in IOMMU configuration |
| **Key Mitigations** | Disable ATS for untrusted devices, IOMMU hardware that re-validates ATS translations (ATS page request validation), TDISP-enforced device isolation, kernel IOMMU driver ATS allowlist policy, CXL IDE encryption for link-level protection |
| **Verification Approach** | Tier 1 — SVA for IOMMU re-validation on ATS-translated requests; Tier 2 — protocol testing with ATS-capable test devices |
| **Related Requirements** | REQ-TDISP-011 (IOMMU integration), REQ-CXL-007 (memory partition isolation) |

---

## KERN-004: KASLR Bypass via Information Leak

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Attacker defeats Kernel Address Space Layout Randomization (KASLR) by leaking kernel virtual addresses through side channels or information disclosure vulnerabilities. Leak sources include: /proc and /sys interfaces exposing kernel pointers (even with kptr_restrict), timing side channels on kernel memory accesses, hardware side channels (branch predictor state, TLB, cache), exception/interrupt timing, and kernel log messages containing addresses. Once the KASLR base is known, the attacker can precisely target kernel code/data structures for subsequent exploitation. |
| **Target Assets** | Kernel base address randomization, kernel symbol addresses, kernel stack addresses, module load addresses |
| **Affected Domains** | Kernel Security (primary), Microarchitectural Security (cache/TLB-based KASLR bypass) |
| **Affected SoC Families** | All — any SoC running a KASLR-enabled kernel |
| **Preconditions** | Local code execution; access to procfs/sysfs interfaces, timing measurement capability, or reachable information disclosure vulnerability |
| **Key Mitigations** | kptr_restrict=2, dmesg_restrict=1, restrict /proc/kallsyms, FGKASLR (fine-grained KASLR), hardware-assisted address randomization, elimination of timing side channels via constant-time kernel operations, unmap kernel text from user-space page tables (KPTI/KAISER) |
| **Verification Approach** | Tier 2 — scan kernel interfaces for address leaks; Tier 3 — microarchitectural timing analysis for cache/TLB-based KASLR bypass |
| **Related Requirements** | REQ-CHERI-003 (permission enforcement — CHERI makes KASLR bypass less impactful) |

---

## KERN-005: ret2user Attack (Kernel Executing User-Space Code)

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E) |
| **Description** | Attacker corrupts a kernel function pointer to redirect execution to user-space memory containing attacker-controlled code. When the kernel dereferences the corrupted pointer, it executes the user-space payload at kernel privilege (ring 0 / EL1). This converts any kernel write-what-where primitive into arbitrary code execution. The attack bypasses kernel code integrity because the executed code resides in user-controllable pages. SMEP (Supervisor Mode Execution Prevention) and SMAP (Supervisor Mode Access Prevention) are the primary hardware countermeasures. |
| **Target Assets** | Kernel function pointers, kernel dispatch tables, user-space memory mapped into kernel page tables, SMEP/SMAP hardware enforcement |
| **Affected Domains** | Kernel Security (primary), Microarchitectural Security (SMEP/SMAP are hardware features) |
| **Affected SoC Families** | All — x86 (SMEP/SMAP), ARM (PAN/PXN), RISC-V (equivalent features) |
| **Preconditions** | Kernel vulnerability allowing function pointer corruption; SMEP/SMAP disabled or bypassed; user-space mapping accessible from kernel context |
| **Key Mitigations** | Enable SMEP/SMAP (x86), PAN/PXN (ARM), hardware-enforced supervisor/user page table separation (KPTI), CFI (Control-Flow Integrity) to validate indirect call targets, CHERI capabilities to enforce kernel/user pointer provenance |
| **Verification Approach** | Tier 1 — SVA for SMEP/SMAP/PAN/PXN enable status on all kernel entry points; Tier 2 — exploitation testing with SMEP/SMAP bypass attempts |
| **Related Requirements** | REQ-CHERI-001 (capability enforcement), REQ-CHERI-003 (permission enforcement) |

---

## KERN-006: DMA Attack via Missing IOMMU Protection

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E), Information Disclosure (I), Tampering (T) |
| **Description** | A malicious or compromised peripheral device performs Direct Memory Access (DMA) to read or write arbitrary host memory because the kernel has not configured IOMMU protection for the device. Without IOMMU page tables restricting device memory access, a DMA-capable device (PCIe, Thunderbolt, FireWire) can bypass all CPU-enforced memory isolation, read kernel memory, inject code, or modify in-memory data structures. This is a classic attack vector for Thunderbolt/PCIe hotplug devices (e.g., PCILeech). |
| **Target Assets** | Host physical memory (unrestricted), kernel code/data, DMA buffer regions, IOMMU configuration state |
| **Affected Domains** | Kernel Security (primary), TDISP / CXL (device DMA isolation), Confidential AI / TEE (DMA to TEE memory) |
| **Affected SoC Families** | All — Client (Thunderbolt), Data Center (PCIe hotplug), Compute (accelerator DMA) |
| **Preconditions** | Physical or logical access to DMA-capable bus; IOMMU not enabled or device not assigned an IOMMU domain; or IOMMU configured in passthrough mode |
| **Key Mitigations** | Enable IOMMU in strict mode (no passthrough) for all DMA-capable devices, pre-boot IOMMU activation (firmware enables IOMMU before OS boot), Thunderbolt security levels, TDISP for device identity and isolation, hardware memory encryption (attacker reads ciphertext) |
| **Verification Approach** | Tier 1 — SVA for IOMMU domain assignment on all DMA-capable endpoints; Tier 2 — DMA attack testing with PCILeech or similar tools |
| **Related Requirements** | REQ-TDISP-011 (IOMMU integration), REQ-CXL-007 (memory partition isolation), REQ-TDISP-005 (RUN state access control) |

---

## KERN-007: seccomp-BPF Filter Bypass

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E) |
| **Description** | Attacker bypasses seccomp-BPF syscall filters to invoke blocked system calls from a sandboxed process. Bypass techniques include: exploiting TOCTOU races in argument inspection (seccomp checks arguments but they change before use), using syscall variants not covered by the filter (e.g., ioctl subcommands, prctl operations), leveraging cross-architecture syscall number differences (x86 vs x32 ABI), abusing io_uring to perform kernel operations without traditional syscalls, or chaining allowed syscalls to achieve the effect of a blocked syscall. |
| **Target Assets** | seccomp-BPF filter program, syscall interface, kernel ABI compatibility layer, io_uring submission queue |
| **Affected Domains** | Kernel Security (primary) |
| **Affected SoC Families** | All — any SoC running Linux with seccomp sandboxing |
| **Preconditions** | Code execution in a seccomp-sandboxed process; knowledge of the active filter program; access to an unfiltered syscall path or TOCTOU window |
| **Key Mitigations** | Allowlist-based seccomp filters (deny by default), block io_uring in sandboxed contexts, filter all ABI variants (x86, x32, ia32), use SECCOMP_FILTER_FLAG_TSYNC for thread synchronization, validate syscall arguments in kernel (not just in BPF filter), hardware-enforced sandbox boundaries |
| **Verification Approach** | Tier 2 — seccomp filter completeness audit; sandbox escape testing with known bypass techniques |
| **Related Requirements** | REQ-CHERI-007 (compartment isolation — hardware-enforced alternative to software sandboxing) |

---

## KERN-008: Capability Escalation via Incorrect Capability Checks

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E) |
| **Description** | Attacker escalates Linux capabilities by exploiting incorrect or missing capability checks in kernel code paths. Linux capabilities split root privileges into discrete units (CAP_NET_ADMIN, CAP_SYS_ADMIN, etc.), but kernel subsystems sometimes fail to check the correct capability, check capabilities in the wrong namespace context, or miss checks entirely on sensitive operations. Attacker leverages a process with a limited capability set to perform operations requiring higher capabilities. User namespaces are a frequent vector, as they grant full capabilities within the namespace that may affect host resources. |
| **Target Assets** | Linux capability bitmask (effective, permitted, inheritable), user namespace capability scope, kernel subsystem capability checks |
| **Affected Domains** | Kernel Security (primary) |
| **Affected SoC Families** | All — any SoC running Linux |
| **Preconditions** | Code execution with at least one non-default capability or access to user namespaces; kernel code path with missing or incorrect capability check |
| **Key Mitigations** | Audit all kernel subsystems for correct ns_capable() usage, restrict user namespace creation (sysctl user.max_user_namespaces=0 where unneeded), minimal capability grants (drop all unneeded capabilities), capability bounding set restrictions, mandatory access control (SELinux/AppArmor) as defense-in-depth |
| **Verification Approach** | Tier 2 — capability check audit of kernel subsystems; privilege escalation testing with minimal capability sets |
| **Related Requirements** | REQ-CHERI-003 (permission enforcement — CHERI provides hardware-enforced capability model) |

---

## KERN-009: io_uring Kernel Attack Surface Exploitation

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E) |
| **Description** | Attacker exploits vulnerabilities in the Linux io_uring subsystem to achieve kernel code execution or privilege escalation. io_uring provides a shared-memory ring buffer interface between user-space and kernel for asynchronous I/O, creating a large and complex kernel attack surface. Vulnerabilities arise from: complex lifetime management of io_uring requests (leading to UAF), race conditions between submission and completion, incorrect reference counting, and the ability to perform file operations, networking, and other kernel operations through io_uring without triggering traditional seccomp filters. io_uring has been the source of numerous critical kernel CVEs (2021-2024). |
| **Target Assets** | io_uring submission/completion queues, kernel async worker threads, registered file descriptors and buffers, io_uring opcode handlers |
| **Affected Domains** | Kernel Security (primary) |
| **Affected SoC Families** | All — Compute and Data Center (high-performance I/O workloads using io_uring) |
| **Preconditions** | Ability to create io_uring instances (may require io_uring_group or unrestricted access); reachable vulnerability in io_uring opcode handler |
| **Key Mitigations** | Restrict io_uring access via sysctl (io_uring_disabled=2 for unprivileged), limit io_uring operations via allowlist, disable io_uring in hardened/sandboxed environments, kernel fuzzing (syzkaller io_uring coverage), hardware MTE/CHERI for memory safety on io_uring structures |
| **Verification Approach** | Tier 2 — targeted fuzzing of io_uring opcodes; regression testing for known io_uring CVEs |
| **Related Requirements** | REQ-CHERI-002 (bounds checking on shared ring buffers), REQ-CHERI-004 (revocation for io_uring request lifetime) |

---

## KERN-010: Kernel Stack Overflow via Deep Recursion

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E), Denial of Service (D) |
| **Description** | Attacker triggers deep recursion or excessive stack allocation in kernel code paths to overflow the fixed-size kernel stack (typically 8-16 KB on Linux). Stack overflow corrupts adjacent memory (thread_info structure on older kernels, or guard page miss on newer ones), potentially enabling control flow hijacking or kernel panic. Vectors include: deeply nested filesystem operations (symlink following, overlayfs stacking), deeply nested network packet processing, and recursive locking. On architectures without hardware stack guard pages, overflow is silent and exploitable. |
| **Target Assets** | Kernel stack (per-thread), thread_info / task_struct metadata, stack guard pages, kernel stack canaries |
| **Affected Domains** | Kernel Security (primary) |
| **Affected SoC Families** | All — IoT (constrained stack sizes), Compute (complex filesystem/network stacks) |
| **Preconditions** | Ability to trigger deep kernel code paths (filesystem, networking); kernel configuration with small stack size; missing or bypassable stack guard pages |
| **Key Mitigations** | VMAP_STACK (virtual-mapped kernel stacks with guard pages), CONFIG_STACKPROTECTOR (stack canaries), limit recursion depth in filesystem and network subsystems, static analysis for stack depth, hardware shadow stacks (Intel CET, ARM GCS) |
| **Verification Approach** | Tier 2 — static analysis of kernel call graph for maximum stack depth; Tier 1 — SVA for stack guard page presence on architecture |
| **Related Requirements** | REQ-CHERI-002 (bounds checking — CHERI stack capabilities can enforce stack bounds in hardware) |

---

## KERN-011: dm-verity Bypass via Offline Root Filesystem Modification

| Field | Value |
|---|---|
| **STRIDE** | Tampering (T) |
| **Description** | Attacker modifies the root filesystem offline (by booting from alternative media, physically accessing storage, or compromising the update mechanism) and then updates the dm-verity hash tree to match, or disables dm-verity verification entirely. If the dm-verity root hash is not anchored in a hardware root of trust (TPM PCR, secure fuse, DICE measurement), the attacker can substitute a modified filesystem with a consistent hash tree. Alternatively, the attacker modifies kernel command-line parameters to disable dm-verity or switch to a non-verified boot path. |
| **Target Assets** | dm-verity hash tree, dm-verity root hash, kernel command line (dm-verity parameters), storage device (raw block access), boot chain integrity |
| **Affected Domains** | Kernel Security (primary), Secure Boot / DICE (root hash anchoring) |
| **Affected SoC Families** | Client (Chromebook, Android verified boot), IoT (embedded verified boot), Compute |
| **Preconditions** | Physical or privileged access to storage device; dm-verity root hash not anchored in hardware; or ability to modify kernel command line |
| **Key Mitigations** | Anchor dm-verity root hash in hardware (TPM PCR extend, secure boot signature, DICE measurement), lock kernel command line via secure boot, use read-only storage for hash tree, enforce dm-verity in kernel config (no runtime disable), A/B partition scheme with rollback protection |
| **Verification Approach** | Tier 1 — SVA for root hash binding to hardware trust anchor; Tier 2 — boot integrity testing with modified filesystem images |
| **Related Requirements** | REQ-DICE-003 (measurement chain integrity), REQ-DICE-009 (layer transition atomicity) |

---

## KERN-012: IMA/EVM Bypass via Metadata Manipulation

| Field | Value |
|---|---|
| **STRIDE** | Tampering (T) |
| **Description** | Attacker bypasses the Linux Integrity Measurement Architecture (IMA) and Extended Verification Module (EVM) by manipulating filesystem extended attributes (xattrs) that store integrity metadata. Attack vectors include: modifying security.ima and security.evm xattrs on a filesystem that permits xattr writes, exploiting TOCTOU between IMA measurement and file execution, bypassing IMA appraisal via files that are not covered by the IMA policy (policy gaps), or exploiting the gap between initial RAM filesystem (initramfs) loading and IMA policy activation. If EVM is not in HMAC or signature mode, xattr integrity is not protected. |
| **Target Assets** | IMA measurement list, EVM xattr HMAC/signatures, security.ima and security.evm extended attributes, IMA appraisal policy, TPM PCR values |
| **Affected Domains** | Kernel Security (primary), Secure Boot / DICE (integrity measurement chain) |
| **Affected SoC Families** | Data Center (IMA for runtime integrity), Client (IMA for measured boot), IoT |
| **Preconditions** | Write access to filesystem xattrs (CAP_SYS_ADMIN or exploitable capability); IMA policy gaps; EVM not enforcing HMAC/signature protection; or access during pre-IMA-policy boot phase |
| **Key Mitigations** | Enable EVM in signature mode (immutable xattrs), comprehensive IMA policy covering all executable content, early IMA policy loading (in initramfs), anchor IMA measurements in TPM, restrict xattr modification capabilities, mandatory IMA appraisal mode (enforce, not log) |
| **Verification Approach** | Tier 2 — IMA policy completeness audit; integrity bypass testing with xattr manipulation |
| **Related Requirements** | REQ-DICE-003 (measurement chain integrity), REQ-SPDM-005 (measurement integrity) |

---

## KERN-013: Dirty Pipe / Dirty COW Style Page Cache Corruption

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E), Tampering (T) |
| **Description** | Attacker exploits race conditions or logic bugs in the kernel's page cache / virtual memory management to write to files or memory mappings that should be read-only. Dirty COW (CVE-2016-5195) exploited a race in copy-on-write handling to write to read-only memory mappings. Dirty Pipe (CVE-2022-0847) exploited missing initialization of pipe buffer flags to overwrite page cache contents of read-only files. These attacks allow unprivileged users to modify setuid binaries, /etc/passwd, or other privileged files, achieving root. The underlying vulnerability class is kernel VM subsystem bugs that violate page permission invariants. |
| **Target Assets** | Page cache, copy-on-write (COW) mechanism, pipe buffer management, VM area (VMA) permissions, file-backed memory mappings |
| **Affected Domains** | Kernel Security (primary) |
| **Affected SoC Families** | All — any SoC running Linux |
| **Preconditions** | Unprivileged local code execution; reachable vulnerability in VM/page cache subsystem; target file readable by attacker |
| **Key Mitigations** | Kernel patching for specific CVEs, page cache integrity checks, careful COW implementation (serialize permission checks), W^X enforcement on page cache pages, hardware memory tagging (MTE) for detecting out-of-band writes, CHERI capabilities to enforce page-level permissions |
| **Verification Approach** | Tier 2 — regression testing for Dirty COW/Dirty Pipe variants; Tier 3 — formal verification of COW permission invariants |
| **Related Requirements** | REQ-CHERI-002 (bounds checking), REQ-CHERI-003 (permission enforcement) |

---

## KERN-014: SMAP/SMEP Bypass via Kernel ROP Chain

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E) |
| **Description** | Attacker constructs a Return-Oriented Programming (ROP) chain using kernel code gadgets to bypass SMEP (Supervisor Mode Execution Prevention) and SMAP (Supervisor Mode Access Prevention). Since SMEP prevents the kernel from executing user-space code and SMAP prevents the kernel from accessing user-space data, the attacker chains existing kernel code fragments (gadgets ending in 'ret') to: (1) disable SMAP/SMEP by modifying CR4 (x86), (2) execute native_write_cr4() to clear SMEP/SMAP bits, (3) pivot the stack to attacker-controlled data, or (4) call commit_creds(prepare_kernel_cred(0)) to escalate to root. Requires an initial kernel control flow hijack (e.g., from KERN-001 or KERN-013). |
| **Target Assets** | SMEP/SMAP (CR4 bits on x86, SCTLR on ARM), kernel code gadgets, kernel stack, CR4 pinning mechanisms |
| **Affected Domains** | Kernel Security (primary), Microarchitectural Security (hardware enforcement bypass) |
| **Affected SoC Families** | All — x86 (SMEP/SMAP/CR4), ARM (PAN/PXN/SCTLR), RISC-V |
| **Preconditions** | Initial kernel control flow hijack; knowledge of kernel code layout (KASLR bypass, see KERN-004); sufficient kernel gadgets for ROP chain construction |
| **Key Mitigations** | CR4 pinning (prevent modification of SMEP/SMAP bits), hardware CFI (Intel CET IBT/SHSTK, ARM BTI/GCS), kCFI (kernel Control-Flow Integrity), CHERI capabilities (ROP impossible without valid capabilities), static CR4 bit enforcement via hypervisor (VMCS CR4 guest/host mask), stack protectors |
| **Verification Approach** | Tier 1 — SVA for CR4 pin enforcement, hardware CFI enablement; Tier 2 — ROP gadget analysis and exploitation testing |
| **Related Requirements** | REQ-CHERI-001 (capability enforcement — eliminates ROP), REQ-CHERI-003 (permission enforcement) |

---

## KERN-015: Hypervisor Escape via KVM/QEMU Vulnerability

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E), Information Disclosure (I) |
| **Description** | Attacker in a guest VM exploits a vulnerability in the KVM hypervisor (kernel module) or QEMU (user-space device emulation) to escape VM isolation and gain code execution on the host. KVM vulnerabilities (in vCPU handling, nested virtualization, interrupt delivery, or memory management) execute at host kernel privilege. QEMU vulnerabilities (in virtual device emulation — virtio, e1000, USB, display) execute at QEMU process privilege on the host. Common vectors include: heap overflow in virtual device emulation, incorrect MMIO/PIO handling, race conditions in vCPU scheduling, and vulnerabilities in nested page table management. |
| **Target Assets** | KVM kernel module, QEMU device emulation, virtual device state (virtio, SCSI, NIC), nested page tables (EPT/NPT), MMIO/PIO handlers, interrupt injection logic |
| **Affected Domains** | Kernel Security (primary), Confidential AI / TEE (VM-based TEE escape), TDISP / CXL (device assignment in VM context) |
| **Affected SoC Families** | Compute (cloud VMs), Data Center (multi-tenant virtualization) |
| **Preconditions** | Code execution in guest VM; reachable vulnerability in KVM or QEMU device emulation; virtual device accessible from guest |
| **Key Mitigations** | Minimal virtual device exposure (disable unused devices), virtio with restricted backends, QEMU sandboxing (seccomp, SELinux), hardware-assisted isolation (SEV-SNP, TDX — guest memory encrypted from host), TDISP for device isolation, KVM hardening (restrict nested virtualization), kernel fuzzing of KVM interfaces |
| **Verification Approach** | Tier 2 — VM escape testing, virtual device fuzzing; Tier 1 — SVA for EPT/NPT isolation enforcement |
| **Related Requirements** | REQ-TDISP-005 (RUN state access control), REQ-CXL-007 (memory partition isolation), REQ-DICE-003 (measurement chain for VM integrity) |

---

*[FROM TRAINING] Threat descriptions are based on publicly known attack classes from academic literature, kernel security advisories (CVEs), and industry reports. Verify against current threat landscape assessments. Last verified: 2026-02-13.*
