# Kernel Hardening Checklist — Access Control and Integrity Verification

## Contents

- [2. Isolation Mechanisms](#2-isolation-mechanisms)
  - [2.1 seccomp-BPF](#21-seccomp-bpf)
  - [2.2 User Namespaces](#22-user-namespaces)
  - [2.3 PID Namespace](#23-pid-namespace)
  - [2.4 Network Namespace](#24-network-namespace)
  - [2.5 Mount Namespace](#25-mount-namespace)
  - [2.6 IPC Namespace](#26-ipc-namespace)
  - [2.7 Cgroup Namespace](#27-cgroup-namespace)
  - [2.8 Linux Capabilities](#28-linux-capabilities)
  - [2.9 Landlock](#29-landlock)
- [4. Integrity Mechanisms](#4-integrity-mechanisms)
  - [4.1 dm-verity](#41-dm-verity)
  - [4.2 IMA (Integrity Measurement Architecture)](#42-ima-integrity-measurement-architecture)
  - [4.3 EVM (Extended Verification Module)](#43-evm-extended-verification-module)
  - [4.4 Kernel Lockdown](#44-kernel-lockdown)
  - [4.5 Module Signature Enforcement](#45-module-signature-enforcement)

## 2. Isolation Mechanisms

### 2.1 seccomp-BPF

- **Description:** Allows processes to define a filter (BPF program) that restricts which system calls they can make. Reduces the kernel attack surface available to a process by blocking access to unnecessary or dangerous syscalls.
- **Kconfig:** `CONFIG_SECCOMP=y`, `CONFIG_SECCOMP_FILTER=y`
- **Verification:** `grep Seccomp /proc/self/status`
- **Security Impact:** CRITICAL — The primary mechanism for reducing kernel attack surface per-process. Docker default profile blocks ~50 syscalls. Without seccomp, all ~450 syscalls are available to every process.

### 2.2 User Namespaces

- **Description:** Allow unprivileged users to create isolated user ID mappings where they appear as root within the namespace. Essential for rootless containers but historically a source of privilege escalation bugs.
- **Kconfig:** `CONFIG_USER_NS=y`
- **Verification:** `unshare --user --map-root-user whoami` or `sysctl user.max_user_namespaces`
- **Security Impact:** MIXED — Required for rootless containers (security benefit) but exposes kernel interfaces normally restricted to root (security risk). Consider restricting with `sysctl kernel.unprivileged_userns_clone=0` on non-container hosts.

### 2.3 PID Namespace

- **Description:** Isolates the process ID number space so processes in different namespaces can have the same PID. Processes in a PID namespace cannot see or signal processes outside it.
- **Kconfig:** `CONFIG_PID_NS=y`
- **Verification:** `ls -la /proc/self/ns/pid`
- **Security Impact:** MEDIUM — Prevents container processes from seeing or interacting with host processes. Must be combined with other namespaces for effective isolation.

### 2.4 Network Namespace

- **Description:** Isolates the network stack — network devices, IP addresses, routing tables, firewall rules, and sockets — per namespace.
- **Kconfig:** `CONFIG_NET_NS=y`
- **Verification:** `ls -la /proc/self/ns/net`
- **Security Impact:** HIGH — Without network namespace isolation, container processes share the host network stack and can sniff traffic, bind to host ports, or manipulate routing.

### 2.5 Mount Namespace

- **Description:** Isolates the filesystem mount table so each namespace has an independent view of the filesystem hierarchy.
- **Kconfig:** `CONFIG_MNT_NS=y` (always available in modern kernels)
- **Verification:** `ls -la /proc/self/ns/mnt`
- **Security Impact:** HIGH — Without mount namespace, container processes can see and potentially modify the host filesystem. Must use pivot_root or proper mount propagation settings.

### 2.6 IPC Namespace

- **Description:** Isolates System V IPC objects (message queues, semaphore sets, shared memory segments) and POSIX message queues.
- **Kconfig:** `CONFIG_IPC_NS=y`
- **Verification:** `ls -la /proc/self/ns/ipc`
- **Security Impact:** MEDIUM — Without IPC namespace, processes in different containers can communicate via shared memory, potentially leaking data or enabling covert channels.

### 2.7 Cgroup Namespace

- **Description:** Virtualizes the cgroup hierarchy view for processes in the namespace, hiding the host cgroup path and preventing cgroup escape.
- **Kconfig:** `CONFIG_CGROUP_NS=y` (cgroup v2: always available)
- **Verification:** `ls -la /proc/self/ns/cgroup`
- **Security Impact:** MEDIUM — Prevents container processes from discovering the host cgroup hierarchy and potentially manipulating resource limits via cgroup filesystem.

### 2.8 Linux Capabilities

- **Description:** Divides the privileges of the root user into distinct units (capabilities) that can be independently granted or revoked. Enables fine-grained privilege assignment without full root.
- **Kconfig:** Always available in modern kernels
- **Verification:** `capsh --print` or `getpcaps <PID>`
- **Security Impact:** CRITICAL — Running containers with a minimal capability set (dropping CAP_SYS_ADMIN, CAP_NET_RAW, etc.) dramatically reduces the blast radius of container compromise. CAP_SYS_ADMIN alone grants near-root privileges.

### 2.9 Landlock

- **Description:** Stackable LSM that enables unprivileged processes to restrict their own filesystem access rights. Provides defense-in-depth sandboxing without requiring root or a privileged daemon.
- **Kconfig:** `CONFIG_SECURITY_LANDLOCK=y`
- **Verification:** `dmesg | grep landlock` or check `CONFIG_LSM` includes `landlock`
- **Security Impact:** MEDIUM — Provides application-level filesystem sandboxing. Unlike seccomp, Landlock operates at the filesystem level and can restrict access to specific paths. Newer versions add network restrictions.

## 4. Integrity Mechanisms

### 4.1 dm-verity

- **Description:** Provides transparent block-level integrity checking using a hash tree. Detects any modification to the contents of a read-only filesystem partition.
- **Kconfig:** `CONFIG_DM_VERITY=y`
- **Verification:** `dmsetup table | grep verity` or `veritysetup status <device>`
- **Security Impact:** HIGH — Ensures filesystem integrity for read-only partitions (root filesystem on Android, Chrome OS). Cannot protect writable filesystems. Hash tree root is typically stored in a signed boot image.

### 4.2 IMA (Integrity Measurement Architecture)

- **Description:** Measures (hashes) files as they are accessed and can optionally appraise (verify) file integrity against stored reference values. Provides runtime file integrity monitoring.
- **Kconfig:** `CONFIG_IMA=y`, `CONFIG_IMA_APPRAISE=y`
- **Verification:** `cat /sys/kernel/security/ima/ascii_runtime_measurements`
- **Security Impact:** HIGH — Detects unauthorized modification of executables, libraries, and configuration files at runtime. With IMA appraise and enforce mode, prevents execution of tampered files.

### 4.3 EVM (Extended Verification Module)

- **Description:** Protects file metadata (security extended attributes) from offline tampering by computing an HMAC or digital signature over security-relevant xattrs.
- **Kconfig:** `CONFIG_EVM=y`
- **Verification:** `cat /sys/kernel/security/evm`
- **Security Impact:** MEDIUM — Without EVM, an attacker with physical access can modify SELinux labels, IMA hashes, or capability xattrs by mounting the filesystem offline. EVM detects such offline tampering.

### 4.4 Kernel Lockdown

- **Description:** Restricts kernel functionality that could be used to modify the running kernel or extract sensitive information, even by root. Two modes: integrity (prevents kernel modification) and confidentiality (additionally prevents reading kernel memory).
- **Kconfig:** `CONFIG_SECURITY_LOCKDOWN_LSM=y`, `CONFIG_LOCK_DOWN_KERNEL_FORCE_INTEGRITY=y` or `CONFIG_LOCK_DOWN_KERNEL_FORCE_CONFIDENTIALITY=y`
- **Verification:** `cat /sys/kernel/security/lockdown`
- **Security Impact:** CRITICAL — In confidentiality mode, prevents root from reading /dev/mem, /dev/kmem, /proc/kcore, and using kprobes/ftrace/eBPF to extract kernel memory contents. Essential for protecting kernel secrets (encryption keys, KASLR base).

### 4.5 Module Signature Enforcement

- **Description:** Requires all kernel modules to carry a valid cryptographic signature matching a key built into the kernel. Unsigned or incorrectly signed modules are rejected.
- **Kconfig:** `CONFIG_MODULE_SIG_FORCE=y` (enforcement), `CONFIG_MODULE_SIG_ALL=y` (sign all at build)
- **Verification:** `zcat /proc/config.gz | grep MODULE_SIG_FORCE`
- **Security Impact:** HIGH — Without enforcement (`CONFIG_MODULE_SIG_FORCE`), the kernel only logs a warning for unsigned modules (tainting the kernel) but still loads them. Enforcement is required for meaningful protection against malicious module loading.
