---
name: protocol-analysis
department: "cipher"
description: "Use when analyzing cryptographic protocol security by modeling state machines, enumerating transitions, and identifying desynchronization, replay, downgrade, and session binding vulnerabilities. Covers protocol handshakes, session management, and negotiation integrity. Do not use for implementation-level crypto review (use crypto-review) or post-quantum assessment (use pqc-readiness)."
version: 1
triggers:
  - "protocol"
  - "TLS"
  - "SPDM"
  - "handshake"
  - "session"
  - "replay"
  - "downgrade"
  - "state machine"
  - "mutual authentication"
  - "key exchange"
  - "session binding"
---

# Protocol Analysis

## Purpose
Model cryptographic protocols as state machines, enumerate state transitions, and identify vulnerabilities including desynchronization, replay attacks, downgrade attacks, and session binding failures.

## Scope Constraints

Reads protocol specifications, message sequence diagrams, and implementation source code. Does not modify files or execute code. Does not interact with live protocol endpoints or perform active testing.

## Inputs
- Protocol specification or implementation under analysis
- Message sequence diagrams or protocol description
- Participant roles and trust relationships
- Security properties the protocol should provide (authentication, confidentiality, integrity, forward secrecy)
- Deployment context (network model, adversary capabilities)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Step 1: Model Protocol State Machine
Define the protocol as a state machine for each participant:
- Enumerate all states (initial, waiting, authenticated, established, error, closed)
- Define all valid transitions with triggering messages
- Identify terminal states and error recovery paths
- Document state variables maintained at each state (keys, nonces, sequence numbers)

### Step 2: Enumerate State Transitions
For each state transition, document:
- Triggering condition (message received, timeout, local event)
- Validation checks performed before transition
- State variables updated during transition
- Messages sent as a result of transition
- What happens on invalid input at this state

### Step 3: Check for Desync and Replay
Analyze the protocol for synchronization vulnerabilities:
- **Replay**: Can any message be replayed to cause a state transition? Are nonces/timestamps checked?
- **Desynchronization**: Can an attacker cause participants to disagree on the current state?
- **Reordering**: Is message ordering enforced? Can out-of-order messages cause incorrect state transitions?
- **Reflection**: Can messages from one direction be reflected back to the sender?
- **Interleaving**: Can messages from different sessions be mixed?

### Step 4: Verify Session Binding
Check that protocol sessions are properly bound:
- Session identifiers are unique and unpredictable
- All messages within a session are cryptographically bound to the session ID
- Channel binding prevents man-in-the-middle relay (TLS channel binding, etc.)
- Session resumption does not weaken security properties
- Concurrent sessions do not share mutable state

### Step 5: Assess Downgrade Resistance
Analyze the protocol's resistance to version/algorithm downgrade:
- Is the version/algorithm negotiation authenticated?
- Can an attacker force a weaker cipher suite?
- Is there a mechanism to prevent rollback to older protocol versions?
- Are negotiation messages included in the session transcript hash?
- Are there minimum security floor requirements that cannot be negotiated away?

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, then resume from the earliest incomplete step.

## Output Format

### Protocol State Machine

```
[Initial] ──ClientHello──→ [WaitServerHello]
                                    │
                          ServerHello│
                                    ▼
                           [WaitFinished]
                                    │
                             Finished│
                                    ▼
                            [Established]
```

### State Transition Table

| Current State | Input | Validation | Next State | Output | Notes |
|---------------|-------|------------|------------|--------|-------|
| Initial | ClientHello | Version check | WaitServerHello | — | Nonce generated |
| ... | ... | ... | ... | ... | ... |

### Vulnerability Assessment

| ID | Category | Description | Severity | Recommendation |
|----|----------|-------------|----------|----------------|
| P1 | Replay | ServerHello lacks nonce binding | High | Include client nonce in server response |
| ... | ... | ... | ... | ... |

### Security Properties Verification
- [ ] Mutual authentication: [Verified/Failed/N/A]
- [ ] Forward secrecy: [Verified/Failed/N/A]
- [ ] Replay resistance: [Verified/Failed/N/A]
- [ ] Downgrade resistance: [Verified/Failed/N/A]

## Handoff

- Hand off to crypto-review if cryptographic implementation issues are discovered during protocol analysis.
- Hand off to prover/formal-spec if the protocol requires formal verification of state machine properties.

## Quality Checks
- [ ] Complete state machine modeled for all participants
- [ ] All state transitions have explicit validation checks
- [ ] Invalid input handling defined for every state
- [ ] Replay resistance verified (nonce/timestamp checking)
- [ ] Session binding verified (session ID, channel binding)
- [ ] Downgrade resistance verified (authenticated negotiation)
- [ ] Error states do not leak information or allow recovery to an insecure state

## Evolution Notes
<!-- Observations appended after each use -->
