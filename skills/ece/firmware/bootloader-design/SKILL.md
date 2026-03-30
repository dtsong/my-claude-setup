---
name: bootloader-design
department: firmware
description: "Design secure bootloader architecture for field-updatable medical device firmware"
version: 1
triggers:
  - bootloader
  - firmware update
  - OTA
  - secure boot
  - flash partition
  - image verification
  - DFU
---

# Bootloader Design

## Purpose

Design a secure bootloader architecture for a field-updatable medical device. Define flash partitioning, boot sequence, firmware update flow, rollback mechanism, and cryptographic verification. Ensure the device always boots to a valid image, even after power loss during update, and that regulatory requirements for field changes are addressed.

## Scope Constraints

- Medical device firmware on ARM Cortex-M or PIC32 microcontrollers with internal or external flash
- Covers bootloader architecture, not full firmware application design
- Does not cover wireless protocol stacks (BLE OTA, Wi-Fi) — assumes transport layer delivers image bytes
- Does not generate IEC 62304 documentation — handoff to iec62304-compliance for regulatory artifacts
- Assumes single-core MCU; multi-core secure boot chains require additional analysis

## Inputs

- MCU specifications: flash size, flash sector/page size, RAM size, hardware crypto accelerator availability
- Security requirements: code signing algorithm preference, debug port policy, anti-rollback needs
- Update transport: wired (UART/USB/SPI) or wireless (BLE/Wi-Fi), maximum transfer rate
- Regulatory context: predicate device history, intended IEC 62304 class, FDA guidance applicability
- Application size: estimated firmware image size and growth projection
- Reliability requirements: expected field update frequency, acceptable update failure rate

## Input Sanitization

- Reject requests without flash size — partition design is impossible without knowing total flash
- If sector size is unspecified, flag as assumption and use 4 KB (common Cortex-M minimum erase size)
- Verify that application image fits in proposed partition with at least 20% growth margin
- Confirm whether external flash is available for staging or if everything must fit in internal flash

## Procedure

1. **Define flash partitioning.** Divide flash into regions: bootloader (write-protected, immutable), application slot A (active image), application slot B (staging/rollback), NVM configuration data, factory defaults/golden image. Calculate sizes based on application estimate with growth margin. Align all partitions to sector boundaries. Document partition map with absolute addresses.

2. **Design boot sequence.** Define the boot flow from power-on reset: hardware initialization (clocks, watchdog) -> read boot configuration -> validate active image integrity (CRC-32 or SHA-256) -> verify image authenticity (ECDSA or RSA signature) -> branch to application entry point. Define fallback behavior at each validation failure: try alternate slot, enter recovery mode, or boot golden image.

3. **Design firmware update flow.** Define the state machine for receiving and installing an update: idle -> receiving (write chunks to staging slot) -> verifying integrity (hash of complete image) -> verifying authenticity (signature check) -> swapping (mark staging as pending-active) -> rebooting -> bootloader confirms swap -> application marks update successful. Power loss at any state must result in a bootable device.

4. **Design rollback mechanism.** Define automatic rollback triggers: application fails to confirm update within N boot cycles, watchdog reset occurs within M seconds of boot, application self-test failure. Define rollback action: revert boot configuration to previous slot, reboot. Ensure rollback image is never overwritten until new image is confirmed good.

5. **Define security measures.** Select code signing algorithm (ECDSA P-256 recommended for Cortex-M: small signature, hardware acceleration available). Define key management: public key embedded in bootloader, private key in HSM, key revocation strategy. Implement anti-rollback counter in one-time-programmable (OTP) memory or monotonic counter. Define debug port policy: JTAG/SWD locked in production, unlockable only with signed debug token.

6. **Address regulatory considerations.** Document implications of field updates under IEC 62304 maintenance process. Identify whether firmware update changes the device's risk profile (requires new 510(k) or not per FDA guidance). Define version tracking and audit trail requirements. Specify validation requirements for the update mechanism itself.

### Progress Checklist

- [ ] Flash partition map defined with addresses and sizes
- [ ] Boot sequence designed with failure handling at each stage
- [ ] Firmware update state machine defined with power-loss resilience
- [ ] Rollback mechanism designed with automatic triggers
- [ ] Security measures specified (signing, anti-rollback, debug lockout)
- [ ] Regulatory considerations documented

### Compaction Resilience

If context is compacted mid-analysis, the Flash Partition Map and Update State Machine capture the core architecture. These two artifacts plus the Security Architecture summary contain all values needed to resume.

## Output Format

```markdown
## Bootloader Design: [System Name]

### System Parameters
- MCU: [part number]
- Internal flash: [size], sector size: [size]
- External flash: [size, if applicable]
- Hardware crypto: [available accelerators]
- Application image size (estimated): [size]

### Flash Partition Map
| Region | Start Address | End Address | Size | Write Protection |
|---|---|---|---|---|
| Bootloader | | | | Yes (immutable) |
| App Slot A | | | | No |
| App Slot B | | | | No |
| NVM Config | | | | No |
| Factory Image | | | | Yes |

### Boot Sequence
1. [Step with success/failure paths]
2. ...

### Boot Decision Tree
```
[ASCII flowchart: reset -> validate A -> valid? -> boot A
                                      -> invalid? -> validate B -> valid? -> boot B
                                                                -> invalid? -> recovery mode]
```

### Firmware Update State Machine
| State | Entry Condition | Action | Next State (success) | Next State (failure) | Power-Loss Behavior |
|---|---|---|---|---|---|
| | | | | | |

### Rollback Strategy
- Automatic rollback triggers:
  1. [trigger and threshold]
  2. [trigger and threshold]
- Rollback action: [description]
- Maximum consecutive rollbacks before recovery mode: [count]

### Security Architecture
- Code signing: [algorithm, key size]
- Public key storage: [location in bootloader]
- Private key management: [HSM/process]
- Anti-rollback: [mechanism]
- Debug port policy: [locked/unlock method]
- Key revocation: [strategy]

### Regulatory Considerations
- IEC 62304 maintenance process implications:
- FDA field update guidance applicability:
- Version tracking and audit trail:
- Update mechanism validation requirements:

### Risks and Mitigations
| Risk | Severity | Mitigation |
|---|---|---|
| | | |
```

## Handoff

- If IEC 62304 documentation is required for the update mechanism, handoff to **iec62304-compliance**
- If RTOS tasks are needed for background update reception, handoff to **rtos-architecture**
- If cryptographic performance affects real-time deadlines, flag for system-level timing review
- If external flash is used, flag for hardware review of SPI/QSPI interface integrity

## Quality Checks

1. Bootloader region is write-protected (hardware flash protection, not just software)
2. Update is atomic — power loss at any point during the update process results in a bootable device
3. Rollback is tested for all failure scenarios: corrupt image, failed signature, watchdog timeout, application self-test failure
4. Cryptographic verification occurs before any new code is executed
5. Anti-rollback counter prevents downgrade attacks to known-vulnerable firmware versions
6. Update mechanism is documented in the IEC 62304 maintenance plan
7. Flash partition sizes include at least 20% growth margin for application image
8. Factory/golden image provides a last-resort recovery path independent of application slots

## Evolution Notes

- Future versions may add support for delta/differential firmware updates to reduce transfer size
- Consider adding encrypted firmware images (confidentiality in addition to authenticity)
- Add support for multi-image systems (bootloader + RTOS + application as separate updateable images)
