---
name: isolation-review
department: "warden"
description: "Use when mapping isolation boundaries, enumerating crossing points, verifying enforcement mechanisms, and testing for bypass paths across trust domains. Covers containers, VMs, enclaves, namespaces, seccomp, and network segmentation. Do not use for kernel configuration audit (use kernel-hardening) or HW/SW security interface review (use hw-sw-boundary)."
version: 1
triggers:
  - "isolation"
  - "container"
  - "namespace"
  - "seccomp"
  - "enclave"
  - "TEE"
  - "sandbox"
  - "VM"
  - "process isolation"
  - "privilege separation"
  - "trust boundary"
---

# Isolation Review

## Purpose
Map all isolation boundaries in a system, enumerate every crossing point, verify enforcement mechanisms, and test for bypass paths that could allow privilege escalation or data leakage across trust domains.

## Scope Constraints

Reads system architecture documentation, container/VM configurations, and security policies. Does not modify isolation configurations or execute active bypass tests. Does not access production environments.

## Inputs
- System architecture with component boundaries
- Isolation mechanisms in use (containers, VMs, enclaves, process separation, namespaces)
- Trust domain definitions (which components trust which)
- Threat model (what attacker capabilities are assumed)
- Compliance requirements for isolation (e.g., PCI DSS network segmentation)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Step 1: Map Isolation Boundaries
Enumerate all isolation boundaries in the system:
- Process boundaries (separate address spaces)
- Container boundaries (namespaces, cgroups, seccomp)
- VM boundaries (hypervisor, separate kernels)
- Enclave/TEE boundaries (hardware-enforced memory isolation)
- Network boundaries (VLANs, firewalls, VPNs)
- For each boundary, identify the enforcement mechanism and its trust anchor

### Step 2: Enumerate Crossing Points
For each isolation boundary, find every legitimate crossing point:
- System calls and ioctls (process ↔ kernel)
- Shared memory regions (process ↔ process)
- Mounted volumes and bind mounts (container ↔ host)
- Virtual device interfaces (VM ↔ hypervisor)
- Network sockets and IPC channels
- Shared files, pipes, signals
- For each crossing, document: what data flows, what validation occurs, what privileges are required

### Step 3: Check Enforcement Mechanisms
Verify that each isolation mechanism is correctly configured:
- **Namespaces**: All relevant namespaces enabled (PID, net, mount, user, UTS, IPC, cgroup)?
- **Seccomp**: Filter is allowlist-based? Covers dangerous syscalls (ptrace, mount, kexec)?
- **Capabilities**: Dropped all capabilities except those explicitly needed? No CAP_SYS_ADMIN?
- **SELinux/AppArmor**: Mandatory access control policy applied and enforcing?
- **Resource limits**: cgroup limits set to prevent resource exhaustion attacks?

### Step 4: Test Bypass Paths
For each isolation boundary, enumerate known bypass techniques:
- Kernel exploits (shared kernel = shared vulnerability for containers)
- Device access (/dev exposure, device cgroups)
- Privileged operations (mount, ptrace, raw sockets)
- Information leaks (procfs, sysfs, timing channels)
- Resource exhaustion (cgroup escape, fork bombs affecting host)
- Escape via shared resources (Docker socket, host PID namespace)

### Step 5: Verify Containment
Assess what happens when an isolation boundary is breached:
- Does breach of one boundary grant access to all resources, or is there defense in depth?
- Are there monitoring/alerting mechanisms for boundary violations?
- Can a compromised component be isolated further (kill, quarantine)?
- Is there blast radius limitation (breach of one container doesn't compromise all containers)?

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, then resume from the earliest incomplete step.

## Output Format

### Isolation Boundary Map

```
┌──────────────────────────────────────┐
│ Host Kernel (shared trust anchor)    │
│  ┌─────────────┐  ┌──────────────┐  │
│  │ Container A  │  │ Container B  │  │
│  │ ns: pid,net  │  │ ns: pid,net  │  │
│  │ seccomp: yes │  │ seccomp: yes │  │
│  └──────┬───────┘  └──────┬───────┘  │
│         │ shared volume    │          │
│         └────────┬─────────┘          │
│                  ▼                    │
│          [Shared /data]              │
└──────────────────────────────────────┘
```

### Crossing Point Inventory

| Boundary | Crossing Point | Data Flow | Validation | Privilege | Risk |
|----------|---------------|-----------|------------|-----------|------|
| Container ↔ Host | Shared volume /data | Config files | None | Read-only mount | Medium |
| ... | ... | ... | ... | ... | ... |

### Bypass Assessment

| Boundary | Bypass Technique | Feasibility | Impact | Mitigation |
|----------|-----------------|-------------|--------|------------|
| Container | Kernel exploit (shared kernel) | Medium | Critical | Minimal kernel, gVisor/Kata |
| ... | ... | ... | ... | ... |

## Handoff

- Hand off to kernel-hardening if kernel-level hardening changes are needed based on isolation findings.
- Hand off to hw-sw-boundary if hardware security feature enablement is required for isolation enforcement.

## Quality Checks
- [ ] All isolation boundaries are mapped with enforcement mechanisms
- [ ] Every crossing point is enumerated with data flow and validation
- [ ] Namespace, seccomp, and capability configuration verified
- [ ] Known bypass techniques assessed for each boundary type
- [ ] Defense in depth evaluated (what happens after one boundary breaches)
- [ ] Shared resources (volumes, network, IPC) are inventoried
- [ ] Containment and blast radius limitations are assessed

## Evolution Notes
<!-- Observations appended after each use -->
