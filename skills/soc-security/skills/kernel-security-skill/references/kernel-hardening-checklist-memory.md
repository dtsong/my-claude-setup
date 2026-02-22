# Kernel Hardening Checklist — Memory Protection and Stack Defenses

## 1. Memory Protections

### 1.1 KASLR (Kernel Address Space Layout Randomization)

- **Description:** Randomizes the base address of the kernel in memory at each boot, making it harder for attackers to predict the location of kernel code and data for exploitation.
- **Kconfig:** `CONFIG_RANDOMIZE_BASE=y`
- **Verification:** `cat /proc/cmdline | grep -v nokaslr && dmesg | grep "KASLR enabled"`
- **Security Impact:** HIGH — Without KASLR, kernel addresses are predictable, making ROP/JOP attacks trivial. KASLR alone is insufficient (info leaks can defeat it) but raises the exploitation bar significantly.

### 1.2 KPTI (Kernel Page Table Isolation)

- **Description:** Separates user-space and kernel-space page tables so that kernel memory mappings are not present while executing in user mode. Primary mitigation for Meltdown-class attacks.
- **Kconfig:** `CONFIG_PAGE_TABLE_ISOLATION=y` (x86) / `CONFIG_UNMAP_KERNEL_AT_EL0=y` (arm64)
- **Verification:** `dmesg | grep "page tables isolation"` or `cat /sys/devices/system/cpu/vulnerabilities/meltdown`
- **Security Impact:** CRITICAL — Without KPTI, Meltdown (CVE-2017-5754) allows user-space processes to read arbitrary kernel memory. Performance cost of 1-5% on modern hardware with PCID support.

### 1.3 SMAP (Supervisor Mode Access Prevention)

- **Description:** Prevents the kernel from accessing user-space memory unless explicitly permitted. Blocks a class of exploits where the kernel is tricked into dereferencing user-controlled pointers.
- **Kconfig:** `CONFIG_X86_SMAP=y` (x86) / hardware feature on arm64 (PAN: `CONFIG_ARM64_PAN=y`)
- **Verification:** `grep -o smap /proc/cpuinfo` (x86) or `dmesg | grep "Privileged Access Never"` (arm64)
- **Security Impact:** HIGH — Prevents ret2user attacks where kernel execution is redirected to user-space memory containing attacker-controlled code/data. Hardware-enforced with near-zero performance cost.

### 1.4 SMEP (Supervisor Mode Execution Prevention)

- **Description:** Prevents the kernel from executing code located in user-space memory pages. Blocks the classic ret2user attack where kernel control flow is redirected to user-space shellcode.
- **Kconfig:** `CONFIG_X86_SMEP=y` (x86) / hardware feature on arm64 (PXN)
- **Verification:** `grep -o smep /proc/cpuinfo` (x86)
- **Security Impact:** HIGH — Without SMEP, a single kernel pointer overwrite can redirect execution to user-space shellcode. Hardware-enforced with no performance cost.

### 1.5 MTE (Memory Tagging Extension)

- **Description:** ARMv8.5-A hardware feature that associates a 4-bit tag with each 16-byte memory granule. Pointer tags must match allocation tags for memory accesses to succeed, catching use-after-free and buffer overflows.
- **Kconfig:** `CONFIG_ARM64_MTE=y`, `CONFIG_KASAN_HW_TAGS=y` (for kernel KASAN+MTE)
- **Verification:** `cat /proc/cpuinfo | grep mte` and `cat /sys/devices/system/cpu/cpu0/mte_tcf_preferred`
- **Security Impact:** HIGH — Probabilistic (1/16 chance of tag match for random access) detection of memory safety bugs in hardware. In synchronous mode, provides immediate fault on tag mismatch. In asymmetric/async mode, lower performance cost but delayed detection.

### 1.6 Shadow Call Stack

- **Description:** Maintains a separate, protected stack containing only return addresses. On function return, the return address is validated against the shadow stack copy, preventing ROP attacks that corrupt the main stack.
- **Kconfig:** `CONFIG_SHADOW_CALL_STACK=y` (arm64, requires Clang) / `CONFIG_X86_USER_SHADOW_STACK=y` (x86 CET)
- **Verification:** `zcat /proc/config.gz | grep SHADOW_CALL_STACK` or check compiler flags for `-fsanitize=shadow-call-stack`
- **Security Impact:** HIGH — Defeats ROP chains that depend on overwriting return addresses on the stack. The shadow stack is protected by hardware (CET on x86, pointer authentication on arm64).

### 1.7 Stack Canaries

- **Description:** Places a random value (canary) between local variables and the return address on the stack. Buffer overflows that overwrite the return address will also corrupt the canary, which is detected before the function returns.
- **Kconfig:** `CONFIG_STACKPROTECTOR=y`, `CONFIG_STACKPROTECTOR_STRONG=y` (recommended)
- **Verification:** `zcat /proc/config.gz | grep STACKPROTECTOR`
- **Security Impact:** MEDIUM — Detects linear stack buffer overflows but can be bypassed by info leaks (reading the canary) or non-linear overwrites. STRONG variant protects more functions than the basic variant.

### 1.8 Stack Initialization

- **Description:** Initializes all local variables on the stack to zero at function entry, preventing information leaks from uninitialized stack memory.
- **Kconfig:** `CONFIG_INIT_STACK_ALL_ZERO=y`
- **Verification:** `zcat /proc/config.gz | grep INIT_STACK_ALL`
- **Security Impact:** MEDIUM — Eliminates a class of information disclosure vulnerabilities where kernel stack contents leak to user space via uninitialized variables. Small performance cost (~1%).

### 1.9 Hardened Usercopy

- **Description:** Validates that kernel buffers used in copy_to_user/copy_from_user operations are within expected bounds, preventing heap overflows from being exploitable via usercopy operations.
- **Kconfig:** `CONFIG_HARDENED_USERCOPY=y`
- **Verification:** `zcat /proc/config.gz | grep HARDENED_USERCOPY`
- **Security Impact:** MEDIUM — Catches out-of-bounds accesses during user/kernel data transfers. Detects when a copy operation crosses slab object boundaries.
