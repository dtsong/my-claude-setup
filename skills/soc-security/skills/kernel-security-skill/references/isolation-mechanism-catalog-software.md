# Isolation Mechanism Catalog — Software Mechanisms & Cross-References

## Contents

- [4. seccomp-BPF](#4-seccomp-bpf)
- [5. Linux Namespaces](#5-linux-namespaces)
- [6. Cgroups (v1/v2)](#6-cgroups-v1v2)
- [7. Linux Capabilities](#7-linux-capabilities)
- [8. Landlock](#8-landlock)
- [9. io_uring Restrictions](#9-io_uring-restrictions)
- [Cross-Reference: HW Features to Isolation Mechanisms](#cross-reference-hw-features-to-isolation-mechanisms)
- [Isolation Mechanism Combinations](#isolation-mechanism-combinations)
  - [Container Isolation Stack](#container-isolation-stack)
  - [VM Isolation Stack](#vm-isolation-stack)
  - [Embedded/SoC Isolation Stack](#embeddedsoc-isolation-stack)

Catalog of software-based kernel isolation mechanisms and cross-reference tables for hardware-to-mechanism and mechanism combination patterns.

---

## 4. seccomp-BPF

- **Name:** Secure Computing Mode with BPF filters
- **Kernel Subsystem:** seccomp-bpf
- **HW Dependency:** None (pure software)
- **Isolation Scope:** Per-process system call filtering
- **Configuration:** Mode 1 (strict: read/write/exit/sigreturn), Mode 2 (filter: BPF decides per syscall), filter inheritance, SECCOMP_FILTER_FLAG_TSYNC, SECCOMP_FILTER_FLAG_LOG
- **Bypass Conditions:** io_uring operations bypass seccomp filters (kernel worker threads); ptrace with CAP_SYS_PTRACE; kernel vulnerability in allowed syscall; SECCOMP_RET_USER_NOTIF TOCTOU; BPF verifier limits; architecture mismatch (compat syscalls)
- **Verification:** `grep Seccomp /proc/<PID>/status`, `seccomp-tools dump`, verify io_uring_setup/io_uring_enter denied

---

## 5. Linux Namespaces

- **Name:** Linux kernel namespaces (user, PID, net, mount, IPC, cgroup, UTS, time)
- **Kernel Subsystem:** namespaces-cgroups
- **HW Dependency:** None
- **Isolation Scope:** Per-namespace isolation of kernel resource views
- **Configuration:** User namespace (UID/GID mapping), PID namespace (CLONE_NEWPID), Network namespace (CLONE_NEWNET, veth/macvlan), Mount namespace (CLONE_NEWNS, pivot_root), IPC namespace, Cgroup namespace
- **Bypass Conditions:** User namespace + unpatched kernel = privilege escalation CVEs; /proc not remounted; mount propagation (shared/slave); --net=host; CAP_SYS_ADMIN in user namespace; symlink attacks; /proc/sys exposure
- **Verification:** `ls -la /proc/<PID>/ns/`, check uid_map, compare mounts, compare namespace inodes

---

## 6. Cgroups (v1/v2)

- **Name:** Control Groups resource isolation
- **Kernel Subsystem:** namespaces-cgroups
- **HW Dependency:** None (resource limits enforced by hardware schedulers)
- **Isolation Scope:** Resource usage limits per process group — CPU, memory, I/O, PIDs, devices
- **Configuration:** Cgroup v2 unified hierarchy, memory.max/high/swap.max, cpu.max/weight, io.max/weight, pids.max, device controller
- **Bypass Conditions:** No memory limit = cross-container OOM; no PID limit = fork bomb; no I/O limit = starvation; writable cgroup filesystem; release_agent escape (CVE-2022-0492)
- **Verification:** `stat -fc %T /sys/fs/cgroup/`, check memory/PID/CPU limits, check for unlimited "max" values

---

## 7. Linux Capabilities

- **Name:** POSIX capabilities
- **Kernel Subsystem:** capabilities
- **HW Dependency:** None
- **Isolation Scope:** Per-thread fine-grained privilege decomposition
- **Configuration:** Bounding set, effective/permitted/inheritable/ambient sets
- **Bypass Conditions:** CAP_SYS_ADMIN (~30% of capable() checks = near-root); CAP_DAC_OVERRIDE+CAP_CHOWN = any file access; CAP_SYS_PTRACE = cross-process injection; CAP_BPF+CAP_PERFMON; capability-unaware programs; ambient inheritance
- **Verification:** `getpcaps <PID>`, `capsh --decode=<hex>`, `capsh --print`

---

## 8. Landlock

- **Name:** Landlock LSM
- **Kernel Subsystem:** landlock
- **HW Dependency:** None
- **Isolation Scope:** Per-process filesystem access restriction (kernel >= 5.19 adds network)
- **Configuration:** Ruleset creation with access rights, path-based rules, enforcement via landlock_restrict_self(), stacking with other LSMs, ABI versioning
- **Bypass Conditions:** Kernel < 5.13; pre-opened file descriptors; /proc/self/fd traversal; mount operations with CAP_SYS_ADMIN; ABI version mismatch
- **Verification:** `dmesg | grep landlock`, check LSM list, verify ABI version

---

## 9. io_uring Restrictions

- **Name:** io_uring access control and restriction
- **Kernel Subsystem:** io-uring
- **HW Dependency:** None
- **Isolation Scope:** Per-ring restriction of allowed operations
- **Configuration:** Global disable (`kernel.io_uring_disabled=2`), unprivileged disable (=1), per-ring restrictions (IORING_REGISTER_RESTRICTIONS), fixed files, seccomp deny
- **Bypass Conditions:** Kernel worker threads bypass seccomp for actual I/O; high CVE density; unrestricted rings created before registration; inherited rings; SQPOLL mode security context
- **Verification:** `sysctl kernel.io_uring_disabled`, verify seccomp blocks, check for existing rings

---

## Cross-Reference: HW Features to Isolation Mechanisms

| Hardware Feature | Isolation Mechanisms Enabled | Required For |
|-----------------|------------------------------|-------------|
| MMU | Page tables, KPTI, KASLR, process isolation | All virtual memory isolation |
| PCID/ASID | Efficient KPTI (avoids TLB flush) | KPTI performance |
| SMAP/PAN | Supervisor mode access prevention | Kernel-user memory boundary |
| SMEP/PXN | Supervisor mode execution prevention | Kernel-user code boundary |
| IOMMU (VT-d) | DMA isolation, device passthrough | Device DMA protection (x86) |
| SMMU (ARM) | DMA isolation, device passthrough | Device DMA protection (ARM) |
| VT-x/AMD-V | KVM VM isolation, EPT/NPT | Virtualization security |
| MTE (ARM) | Memory tagging, KASAN HW tags | Memory safety detection |
| CET (x86) | Shadow stacks, IBT | Control-flow integrity |
| PAC (ARM) | Pointer authentication | Control-flow integrity |
| PMP (RISC-V) | Physical memory protection | M/S/U mode isolation |
| ACS (PCIe) | Per-device IOMMU group isolation | SR-IOV / device passthrough |
| TrustZone (ARM) | Secure/Normal world isolation | TEE isolation |
| SEV/TDX | Encrypted VM memory | Confidential computing |

---

## Isolation Mechanism Combinations

### Container Isolation Stack
```
Landlock          -> filesystem access restriction
seccomp-BPF       -> syscall filtering (must block io_uring_setup)
Namespaces        -> resource view isolation (user, PID, net, mount, IPC, cgroup)
Cgroups v2        -> resource limits (memory, CPU, PID, I/O)
Capabilities      -> privilege restriction (drop all, add only needed)
AppArmor/SELinux  -> mandatory access control
```

### VM Isolation Stack
```
EPT/NPT           -> VM memory isolation (hardware)
IOMMU/SMMU        -> device passthrough DMA isolation (hardware)
KVM               -> CPU state isolation, VMEXIT handling (software)
KPTI              -> guest kernel page table isolation (software)
KSM disabled      -> prevents cross-VM side-channels
CPU pinning        -> reduces shared microarchitectural state
CAT (LLC partition) -> cache side-channel mitigation
```

### Embedded/SoC Isolation Stack
```
PMP (RISC-V) / TrustZone (ARM) -> physical memory protection (hardware)
MMU page tables    -> virtual memory isolation (hardware+software)
SMMU               -> device DMA isolation (hardware)
seccomp-BPF        -> syscall filtering (software)
Capabilities       -> minimal privilege (software)
dm-verity          -> filesystem integrity (software)
```
