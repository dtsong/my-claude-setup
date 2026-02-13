---
name: "Protocol Design"
department: "sentinel"
description: "[Council] Wireless protocol selection, stack design, and interoperability. Used during council/academy deliberation only."
version: 1
triggers:
  - "BLE"
  - "MQTT"
  - "Matter"
  - "Thread"
  - "Zigbee"
  - "LoRa"
  - "CoAP"
  - "protocol"
  - "wireless"
  - "radio"
---

# Protocol Design

## Purpose

Select and design the communication protocol stack for an IoT/embedded system, including physical layer selection, transport protocol, application protocol, and security layer.

## Inputs

- Device hardware capabilities (radio modules available)
- Communication requirements (range, bandwidth, latency, power)
- Network topology (star, mesh, point-to-point)
- Security requirements (encryption, authentication, integrity)
- Ecosystem requirements (Matter certification, HomeKit, Alexa)

## Process

### Step 1: Define Communication Requirements

Quantify what the protocol must deliver:
- **Range:** Indoor (10m), building (50m), campus (500m), wide-area (km+)
- **Bandwidth:** Bytes/second needed for typical and peak traffic
- **Latency:** Maximum acceptable end-to-end delay
- **Power budget:** mA available for radio operations, duty cycle
- **Topology:** Star (hub-spoke), mesh (multi-hop), point-to-point
- **Device density:** How many devices in one radio neighborhood

### Step 2: Select Physical/Link Layer

Choose the radio technology:

| Protocol | Range | Bandwidth | Power | Topology | Best For |
|----------|-------|-----------|-------|----------|----------|
| BLE 5.0 | 50m | 2Mbps | Low | Star/mesh | Wearables, sensors, phones |
| Thread | 50m | 250kbps | Low | Mesh | Home automation (Matter) |
| Zigbee | 100m | 250kbps | Low | Mesh | Legacy home automation |
| Wi-Fi | 50m | High | High | Star | High-bandwidth, powered devices |
| LoRaWAN | 15km | 0.3-50kbps | Very low | Star | Wide-area, low-frequency |
| Cellular (LTE-M/NB-IoT) | km+ | Moderate | Medium | Star | Asset tracking, remote |

### Step 3: Select Application Protocol

Choose how data is structured and exchanged:
- **MQTT:** Pub/sub, lightweight, great for telemetry. Needs TCP (Wi-Fi/cellular).
- **CoAP:** REST-like over UDP, ideal for constrained devices. Built-in discovery.
- **HTTP/REST:** Universal but heavy. Only for powered devices with good connectivity.
- **Custom binary:** Maximum efficiency but maintenance burden. Use Protobuf or CBOR instead of raw binary.

### Step 4: Design Security Layer

Layer security into the stack:
- **Transport encryption:** TLS 1.3 (TCP), DTLS (UDP), or link-layer encryption (BLE bonding)
- **Authentication:** Device certificates, pre-shared keys, or OAuth 2.0 device flow
- **Integrity:** Message signing, sequence numbers to prevent replay
- **Key management:** How are keys provisioned, rotated, and revoked?

### Step 5: Design Message Format

Define the wire format:
- **Serialization:** JSON (readable, large), CBOR (compact, schemaless), Protobuf (compact, schema-required)
- **Envelope:** Header (device ID, message type, sequence, timestamp) + payload
- **Size budget:** Maximum message size for the chosen transport
- **Fragmentation:** How to handle messages larger than MTU

### Step 6: Design Error Handling and Resilience

Plan for communication failures:
- **Retry strategy:** Exponential backoff with jitter
- **QoS levels:** At-most-once, at-least-once, exactly-once — which is needed?
- **Offline queuing:** Buffer messages during disconnection, sync on reconnect
- **Connection management:** Keepalive intervals, reconnection strategy

## Output Format

```markdown
# Protocol Architecture

## Requirements Summary
| Requirement | Value |
|-------------|-------|
| Range | [X meters/km] |
| Bandwidth | [X bytes/sec] |
| Latency | [X ms max] |
| Power budget | [X mA avg] |
| Topology | [Star/Mesh/P2P] |

## Protocol Stack
| Layer | Choice | Rationale |
|-------|--------|-----------|
| Physical/Link | [BLE/Thread/Wi-Fi/etc.] | [Why] |
| Transport | [TCP/UDP/none] | [Why] |
| Security | [TLS/DTLS/link-layer] | [Why] |
| Application | [MQTT/CoAP/custom] | [Why] |
| Serialization | [JSON/CBOR/Protobuf] | [Why] |

## Message Format
```
[Header: device_id (4B) | msg_type (1B) | seq (2B) | timestamp (4B)]
[Payload: CBOR-encoded application data]
[Total: ~128 bytes typical, 512 bytes max]
```

## Security Design
| Aspect | Approach |
|--------|----------|
| Encryption | [Method] |
| Authentication | [Method] |
| Key management | [Provisioning and rotation strategy] |

## Error Handling
| Scenario | Strategy |
|----------|----------|
| Message lost | [Retry/QoS approach] |
| Disconnection | [Offline queue + sync] |
| Server unreachable | [Backoff + local operation] |
```

## Quality Checks

- [ ] Protocol selection is justified against requirements (not just "we always use MQTT")
- [ ] Power consumption of radio operations is calculated against battery budget
- [ ] Security covers encryption, authentication, and key management
- [ ] Message format fits within the chosen transport's MTU
- [ ] Error handling addresses disconnection, retry, and offline operation
- [ ] Ecosystem requirements (Matter, HomeKit) are satisfied by protocol choice

## Evolution Notes
<!-- Observations appended after each use -->
