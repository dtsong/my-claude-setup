# Eval Case: Seccomp Policy Audit for Container-Based SoC Workload

## Metadata
- **Case ID:** KS-003
- **Tier:** 2 (medium)
- **Skill Route:** kernel-security-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Audit the seccomp-BPF policy for our containerized inference workload running on a data center AI accelerator SoC. The containers run machine learning inference services that interact with the GPU accelerator via a custom kernel driver.\n\nKernel: Linux 6.8.12, x86_64\nContainer runtime: containerd 1.7 with runc\nLSM: AppArmor (default Docker profile)\n\nKernel config:\nCONFIG_SECCOMP=y\nCONFIG_SECCOMP_FILTER=y\nCONFIG_BPF_SYSCALL=y\nCONFIG_IO_URING=y\nCONFIG_USER_NS=y\nCONFIG_CHECKPOINT_RESTORE=y\nCONFIG_MODULES=y\nCONFIG_MODULE_SIG=y\nCONFIG_MODULE_SIG_FORCE=n\n\nSeccomp profile (applied to inference containers):\n```json\n{\n  \"defaultAction\": \"SCMP_ACT_ERRNO\",\n  \"syscalls\": [\n    {\"names\": [\"read\",\"write\",\"open\",\"close\",\"stat\",\"fstat\",\"mmap\",\"mprotect\",\"munmap\",\"brk\",\"ioctl\",\"access\",\"pipe\",\"select\",\"sched_yield\",\"mremap\",\"clone\",\"execve\",\"wait4\",\"kill\",\"fcntl\",\"flock\",\"fsync\",\"fdatasync\",\"getdents\",\"getcwd\",\"chdir\",\"rename\",\"mkdir\",\"rmdir\",\"link\",\"unlink\",\"readlink\",\"chmod\",\"chown\",\"lseek\",\"getpid\",\"socket\",\"connect\",\"accept\",\"sendto\",\"recvfrom\",\"bind\",\"listen\",\"setsockopt\",\"getsockopt\",\"epoll_create1\",\"epoll_ctl\",\"epoll_wait\",\"eventfd2\",\"timerfd_create\",\"signalfd4\",\"futex\",\"set_robust_list\",\"get_robust_list\",\"nanosleep\",\"clock_gettime\",\"sysinfo\",\"prctl\",\"arch_prctl\",\"set_tid_address\",\"exit_group\"], \"action\": \"SCMP_ACT_ALLOW\"},\n    {\"names\": [\"io_uring_setup\",\"io_uring_enter\",\"io_uring_register\"], \"action\": \"SCMP_ACT_ALLOW\"},\n    {\"names\": [\"ptrace\"], \"action\": \"SCMP_ACT_ALLOW\"},\n    {\"names\": [\"mount\",\"umount2\"], \"action\": \"SCMP_ACT_ALLOW\"}\n  ]\n}\n```\n\nCapabilities granted to inference containers:\n- CAP_SYS_PTRACE (for debugging stuck inference jobs)\n- CAP_NET_RAW (for health check pings)\n- CAP_IPC_LOCK (for GPU memory pinning via mlock)\n\nHardware: x86_64 with VT-x, VT-d, SMAP, SMEP, CET (shadow stacks)\nDeployment: Multi-tenant cloud, containers on bare-metal (no VM isolation layer)\nSoC family: data-center\nTechnology domain: confidential-ai",
  "context": "Seccomp policy audit with a deliberately over-permissive profile. Key issues: io_uring allowed (bypasses seccomp for many ops), ptrace allowed (cross-process injection), mount allowed (namespace escape vector), user namespaces enabled, module signing not enforced. Multi-tenant bare-metal without VM isolation amplifies risk. Phases 2, 3, and 4 are primary."
}
```

## Expected Output
A kernel security analysis focused on seccomp-BPF policy producing:
- Multiple HIGH/CRITICAL findings for over-permissive syscalls (io_uring, ptrace, mount)
- Container escape path analysis via ptrace + CAP_SYS_PTRACE combination
- io_uring seccomp bypass analysis
- Assessment of capability set combined with seccomp gaps
- Isolation completeness evaluation (seccomp + capabilities + namespaces + AppArmor)

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] io_uring_setup/enter/register allowed in seccomp flagged as HIGH/CRITICAL — bypasses seccomp-BPF for many operations in kernel worker threads
- [ ] ptrace allowed + CAP_SYS_PTRACE flagged as container escape vector — enables cross-process injection
- [ ] mount/umount2 allowed flagged as privilege escalation/namespace escape vector
- [ ] Isolation assessed in combination — seccomp gaps evaluated alongside capabilities and AppArmor
- [ ] Multi-tenant bare-metal (no VM layer) noted as amplifying all container escape risks
- [ ] KernelSecFinding entities produced with correct privilege levels and attack primitives

### Should Pass (partial credit)
- [ ] User namespaces (CONFIG_USER_NS=y) assessed as capability amplification vector inside containers
- [ ] Module signing enabled but not enforced (MODULE_SIG_FORCE=n) flagged as attack surface
- [ ] CAP_NET_RAW assessed for network-level attack surface (raw socket creation)
- [ ] CAP_IPC_LOCK assessed for mlock-based resource exhaustion potential
- [ ] Remediation recommendations provided: deny io_uring, deny ptrace/mount, enforce module signing
- [ ] Confidence tiers: seccomp policy findings GROUNDED (config provided), escape paths INFERRED

### Bonus
- [ ] Custom GPU driver ioctl interface assessed as additional attack surface (ioctl is allowed in seccomp)
- [ ] CET shadow stacks assessed as hardware mitigation for ROP/JOP in kernel exploit chains
- [ ] AppArmor default Docker profile limitations noted — does not restrict io_uring or many privileged operations
- [ ] Specific container escape chain documented: ptrace attach to host-PID-namespace process -> arbitrary code execution in host context

## Raw Trace Log
