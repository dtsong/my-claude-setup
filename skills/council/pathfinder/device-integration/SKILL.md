---
name: "Device Integration"
department: "pathfinder"
description: "[Council] Hardware API integration for sensors, permissions, and biometrics. Used during council/academy deliberation only."
version: 1
triggers:
  - "camera"
  - "GPS"
  - "biometric"
  - "Face ID"
  - "Touch ID"
  - "NFC"
  - "haptic"
  - "sensor"
  - "permission"
  - "bluetooth"
  - "accelerometer"
  - "push notification"
---

# Device Integration

## Purpose

Design the integration strategy for device hardware APIs (camera, sensors, biometrics, Bluetooth, etc.), including permission flows, fallback behavior, and cross-platform abstraction.

## Inputs

- Feature requirements involving hardware capabilities
- Target platforms and OS version minimums
- Cross-platform framework (if applicable)
- Privacy requirements and data sensitivity

## Process

### Step 1: Inventory Required Capabilities

List every hardware API the feature needs:
- Camera (photo, video, barcode scanning)
- Location (GPS, network-based, background location)
- Biometrics (Face ID, Touch ID, fingerprint, device PIN fallback)
- Bluetooth (BLE scanning, pairing, data transfer)
- Sensors (accelerometer, gyroscope, compass, barometer)
- Push notifications (remote, local, rich notifications)
- Haptics (impact, selection, notification feedback)
- Other (NFC, ARKit/ARCore, HealthKit)

### Step 2: Map Permission Requirements

For each capability, document:
- **iOS permission:** NSCameraUsageDescription, NSLocationWhenInUseUsageDescription, etc.
- **Android permission:** CAMERA, ACCESS_FINE_LOCATION, USE_BIOMETRIC, etc.
- **Runtime vs install-time:** Which permissions need runtime prompts
- **Purpose strings:** User-facing explanation for each permission
- **Privacy manifest entries:** (iOS 17+ privacy manifest requirements)

### Step 3: Design Permission Flow

For each permission:
- **Pre-prompt education:** Explain why the permission is needed before the system dialog
- **First request timing:** When in the user flow to request (not on launch — at the moment of need)
- **Denial handling:** What the feature does if permission is denied
- **Settings redirect:** How to guide the user to Settings if they denied and changed their mind
- **Partial permission:** Handle "While Using" vs "Always" for location, "Limited" for photos

### Step 4: Evaluate Cross-Platform Abstraction

If using a cross-platform framework:
- Identify which APIs have mature cross-platform libraries
- Flag which capabilities require native modules or platform-specific code
- Assess abstraction quality (does the library expose all platform-specific options?)
- Plan for platform differences (Face ID vs fingerprint, iOS haptics vs Android vibration)

### Step 5: Design Fallback Behavior

For each capability, define behavior when:
- Hardware is absent (no NFC chip, no biometric sensor)
- Permission is denied (camera denied, location denied)
- Hardware fails (GPS can't get a fix, Bluetooth disconnects)
- OS version doesn't support the API

### Step 6: Power and Performance Impact

Assess battery and performance cost:
- Background location tracking power draw
- Continuous sensor polling vs event-driven
- Bluetooth scanning intervals and power modes
- Camera session lifecycle management

## Output Format

```markdown
# Device Integration Plan

## Capability Matrix
| Capability | iOS | Android | Cross-Platform Library | Native Required |
|-----------|-----|---------|----------------------|-----------------|
| Camera    | Yes | Yes     | expo-camera          | No              |
| BLE       | Yes | Yes     | react-native-ble-plx | No              |
| Face ID   | Yes | N/A     | expo-local-auth      | Partial         |

## Permission Map
| Capability | iOS Permission | Android Permission | Timing | Purpose String |
|-----------|---------------|-------------------|--------|----------------|
| Camera    | NSCameraUsageDescription | CAMERA | On first scan | "Scan barcodes..." |

## Permission Flow
### [Capability Name]
1. User taps [action]
2. Show education screen: "[Why we need this]"
3. System permission dialog
4. If granted: [proceed]
5. If denied: [fallback behavior]
6. If denied permanently: [settings redirect with instructions]

## Fallback Matrix
| Capability | Hardware Absent | Permission Denied | Hardware Failure |
|-----------|----------------|-------------------|-----------------|
| Camera    | [Fallback]     | [Fallback]        | [Fallback]      |

## Power Impact
| Capability | Active Draw | Mitigation |
|-----------|------------|------------|
| GPS       | ~50mA      | Use significant-change monitoring |
```

## Quality Checks

- [ ] Every required permission has a user-facing purpose string
- [ ] Permission requests happen at moment of need, not on app launch
- [ ] Every capability has fallback behavior for denial, absence, and failure
- [ ] Cross-platform libraries are evaluated for API completeness
- [ ] Power impact is assessed for continuous-use capabilities
- [ ] iOS privacy manifest requirements are addressed (iOS 17+)
- [ ] Android runtime vs install-time permissions are correctly categorized

## Evolution Notes
<!-- Observations appended after each use -->
