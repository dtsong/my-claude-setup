# Isolation Mechanism Catalog — Hardware-Backed Mechanisms

Catalog of kernel isolation mechanisms with hardware dependencies. Each mechanism documents its HW dependency, configuration, bypass conditions, and verification approach.

---

## 1. MMU Page Tables

- **Name:** MMU-based virtual memory isolation
- **Kernel Subsystem:** memory-management
- **HW Dependency:** MMU (required), PCID/ASID (performance), SMEP/SMAP/PAN/PXN (supplementary)
- **Isolation Scope:** Process-to-process address space isolation; user-to-kernel separation via KPTI/TTBR0_EL0 unmapping
- **Configuration:** 4-level or 5-level page tables, KPTI enabled (separate user/kernel tables), NX/XN bit, SMEP/PXN, SMAP/PAN
- **Bypass Conditions:** Kernel info leak defeating KASLR; write-what-where on page table entries; Meltdown (CVE-2017-5754) without KPTI; UAF on page structures; Spectre-class transient access
- **Verification:** `dmesg | grep "page tables isolation"`, `grep -o 'smap\|smep' /proc/cpuinfo`, `dmesg | grep -i "NX"`

---

## 2. IOMMU (Intel VT-d)

- **Name:** Intel VT-d IOMMU DMA isolation
- **Kernel Subsystem:** iommu-smmu
- **HW Dependency:** Intel VT-d (required), ACS (required for per-device isolation), DMAR ACPI table
- **Isolation Scope:** Device-to-host memory isolation; prevents DMA-capable devices from accessing memory outside assigned regions
- **Configuration:** `intel_iommu=on iommu=strict`, DMA domain types, IOMMU groups, ACS at every PCIe switch, interrupt remapping
- **Bypass Conditions:** `iommu=soft` or passthrough; ACS not supported (shared IOMMU groups); RMRR firmware-reserved regions; ATS trust without validation; hot-plug inheritance; large identity-mapped regions
- **Verification:** `dmesg | grep -i "iommu"`, verify IOMMU groups via `/sys/kernel/iommu_groups/`, check for identity mappings, verify interrupt remapping, check ACS via `lspci -vv`

---

## 3. SMMU (ARM SMMUv2/v3)

- **Name:** ARM System Memory Management Unit
- **Kernel Subsystem:** iommu-smmu
- **HW Dependency:** ARM SMMU (required), Stream ID routing, ATS support (SMMUv3)
- **Isolation Scope:** Device-to-host memory isolation on ARM; maps device transactions through kernel-controlled translation tables
- **Configuration:** Stream IDs per device, Stage 1+2 translation, bypass mode disabled, stall model
- **Bypass Conditions:** Stream ID misconfiguration; bypass bit in STE; Stage 2 only; HTTU without dirty bit management; ATS without PRI; global bypass mode
- **Verification:** `dmesg | grep -i smmu`, check device tree / ACPI IORT, verify bypass disabled, verify stage 1+2

---

## 10. KVM Isolation Boundaries

- **Name:** KVM virtual machine isolation
- **Kernel Subsystem:** process-isolation (KVM as kernel module)
- **HW Dependency:** VT-x/AMD-V (required), EPT/NPT (required), VT-d/IOMMU (for device passthrough)
- **Isolation Scope:** VM-to-VM and VM-to-host memory, CPU state, and device isolation
- **Configuration:** `kvm.nx_huge_pages=1`, CPU isolation/pinning, EPT/NPT tables, KSM disabled, IOMMU passthrough via vfio-pci, SEV/TDX
- **Bypass Conditions:** VMEXIT handler vulnerabilities; emulated device bugs; KSM cross-VM side-channels; shared LLC without CAT; nested virtualization; device passthrough without IOMMU
- **Verification:** `grep -o 'vmx\|svm' /proc/cpuinfo`, check KSM disabled, verify IOMMU for passthrough, check SEV/TDX status

---

## 11. SMAP/SMEP (x86) and PAN/PXN (ARM)

- **Name:** Supervisor Mode Access/Execution Prevention
- **Kernel Subsystem:** memory-management
- **HW Dependency:** SMAP/SMEP CPU flags (x86), PAN/PXN (ARMv8.1-A+)
- **Isolation Scope:** Prevents kernel from accessing/executing user-space memory unless explicitly unlocked
- **Configuration:** `CONFIG_X86_SMAP=y`, `CONFIG_X86_SMEP=y`, `CONFIG_ARM64_PAN=y`
- **Bypass Conditions:** Disabled at boot (`nosmap`/`nosmep`); incorrect `stac`/`clac` usage; controlled write to CR4; page table manipulation; speculative execution
- **Verification:** `grep -o 'smap\|smep' /proc/cpuinfo`, `cat /proc/cmdline | grep -v nosmap`

---

## 12. MTE (Memory Tagging Extension)

- **Name:** ARM Memory Tagging Extension
- **Kernel Subsystem:** memory-management
- **HW Dependency:** ARMv8.5-A MTE (required), TBI
- **Isolation Scope:** Per-allocation memory safety; 4-bit tag per 16-byte granule matched against pointer tag
- **Configuration:** `CONFIG_ARM64_MTE=y`, `CONFIG_KASAN_HW_TAGS=y`, sync/async/asymm mode via `prctl`
- **Bypass Conditions:** Tag match (1/16 probability); deterministic tag sequences; async mode missing transient violations; in-object overflows within 16-byte granule; non-pointer access (DMA, /dev/mem); software tag manipulation
- **Verification:** `cat /proc/cpuinfo | grep mte`, check preferred mode, verify KASAN HW tags

---

## 13. PMP (Physical Memory Protection — RISC-V)

- **Name:** RISC-V Physical Memory Protection
- **Kernel Subsystem:** memory-management
- **HW Dependency:** RISC-V PMP (required), typically 8-16 entries
- **Isolation Scope:** Physical memory access control per privilege level (M/S/U)
- **Configuration:** `pmpcfg`/`pmpaddr` CSRs, TOR/NAPOT/NA4 addressing, lock bit, ePMP extension
- **Bypass Conditions:** Limited entries; M-mode vulnerability bypasses all PMP; without ePMP M-mode unrestricted; premature locking; NAPOT alignment too coarse; overlapping region misconfiguration; no I/O memory coverage
- **Verification:** Read `pmpcfg`/`pmpaddr` CSRs, verify lock bits, check ePMP support, test S-mode access to M-mode regions
