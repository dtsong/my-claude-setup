---
name: "Fleet Management"
department: "sentinel"
description: "Device provisioning, OTA update strategy, and fleet-scale monitoring"
version: 1
triggers:
  - "OTA"
  - "fleet"
  - "provisioning"
  - "update"
  - "telemetry"
  - "device management"
  - "certificate"
  - "rollout"
  - "firmware update"
---

# Fleet Management

## Purpose

Design the fleet management infrastructure for an IoT device fleet, including device provisioning, OTA firmware update strategy, telemetry aggregation, and fleet-scale monitoring.

## Inputs

- Expected fleet size (current and projected)
- Device hardware capabilities (storage, connectivity, compute)
- Update frequency requirements
- Monitoring and alerting requirements
- Regulatory requirements (safety-critical updates, rollback mandates)

## Process

### Step 1: Design Device Provisioning

Plan how devices go from factory to operational:
- **Identity:** Unique device ID (hardware serial, provisioned certificate)
- **Authentication:** Device certificates (X.509), pre-shared keys, or cloud-provisioned tokens
- **Registration flow:** First-boot sequence, cloud registration, owner assignment
- **Zero-touch:** Can a device self-provision without manual intervention?
- **Factory integration:** What happens on the manufacturing line?

### Step 2: Design OTA Update System

Plan the firmware update lifecycle:
- **Partition scheme:** A/B (dual partition for atomic swap), single with rollback region
- **Update delivery:** Pull (device checks periodically) vs push (server initiates)
- **Delta updates:** Full firmware image vs binary diff (saves bandwidth)
- **Integrity verification:** Cryptographic signature verification before applying
- **Rollback mechanism:** Automatic rollback if new firmware fails health check
- **Staged rollout:** Canary (1%) → early (10%) → general (100%) with hold gates

### Step 3: Design Telemetry Pipeline

Plan how device data reaches the cloud:
- **Data types:** Health metrics (battery, signal, temperature), application data, error reports
- **Aggregation:** On-device pre-aggregation to reduce bandwidth (send averages, not raw samples)
- **Transport:** MQTT topics, HTTP batch uploads, or store-and-forward
- **Cloud ingestion:** Message broker → stream processing → storage
- **Retention:** Hot (real-time queries), warm (weekly), cold (archive)

### Step 4: Design Monitoring and Alerting

Plan fleet-scale observability:
- **Health dashboards:** Fleet-wide metrics (online %, firmware version distribution, battery levels)
- **Anomaly detection:** Devices reporting unusual values, sudden offline clusters
- **Alert thresholds:** Battery < 10%, signal < -90dBm, error rate > 1%, offline > 24h
- **Group operations:** Query and act on device groups (by firmware version, region, owner)

### Step 5: Design Remote Management

Plan remote device operations:
- **Configuration updates:** Push configuration changes without firmware update
- **Remote diagnostics:** Request debug logs, trigger self-test, read sensor state
- **Remote actions:** Reboot, factory reset, enter recovery mode
- **Access control:** Who can perform which operations on which devices

### Step 6: Plan Scaling Strategy

Design for fleet growth:
- **Connection management:** Connection limits per broker, load balancing
- **Update infrastructure:** CDN for firmware binaries, rate limiting downloads
- **Database design:** Time-series storage for telemetry, device registry scaling
- **Cost modeling:** Per-device cloud cost at 1K, 10K, 100K, 1M devices

## Output Format

```markdown
# Fleet Management Architecture

## Provisioning Flow
```
[Factory] → [Flash firmware + certificate] → [First boot] → [Cloud registration] → [Owner assignment] → [Operational]
```

| Step | Method | Duration | Manual? |
|------|--------|----------|---------|
| Identity | X.509 certificate | Factory | No |
| Registration | MQTT first-connect | <30s | No |
| Owner assignment | QR code scan | User-initiated | Yes |

## OTA Update Strategy
| Aspect | Approach |
|--------|----------|
| Partition scheme | A/B dual-partition |
| Delivery | Pull, 6-hour check interval |
| Format | Delta updates (bsdiff) |
| Verification | Ed25519 signature |
| Rollback | Automatic on 3 failed health checks |
| Staged rollout | 1% → 10% → 50% → 100% with 24h holds |

## Telemetry Pipeline
```
[Device] → [MQTT] → [Message Broker] → [Stream Processor] → [Time-Series DB] → [Dashboard]
```

| Data Type | Frequency | Aggregation | Retention |
|-----------|-----------|-------------|-----------|
| Health | 5 min | On-device avg | 90 days |
| Errors | Event-driven | None | 1 year |
| Application | 30 sec | 1-min rollups | 30 days |

## Monitoring Dashboard
| Metric | Threshold | Alert |
|--------|-----------|-------|
| Fleet online % | < 95% | Warning |
| Firmware current % | < 80% | Info |
| Battery critical | < 5% | Critical |
| Error rate | > 1% | Warning |

## Scaling Projections
| Fleet Size | Monthly Cost | Key Bottleneck |
|-----------|-------------|----------------|
| 1,000 | $X | None |
| 10,000 | $X | MQTT connections |
| 100,000 | $X | Telemetry storage |
```

## Quality Checks

- [ ] Provisioning flow is zero-touch (no manual steps per device)
- [ ] OTA updates are cryptographically signed and verified
- [ ] Rollback is automatic — a bad update doesn't brick the fleet
- [ ] Staged rollout has hold gates between stages
- [ ] Telemetry pipeline handles device-side aggregation to reduce bandwidth
- [ ] Monitoring has defined thresholds and alert escalation paths
- [ ] Cost model scales linearly (not exponentially) with fleet size

## Evolution Notes
<!-- Observations appended after each use -->
