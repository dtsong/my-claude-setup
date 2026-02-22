# Threat Modeling Methodology — Cross-Framework Integration & Templates

## Purpose

Guidance for cross-framework synthesis, threat statement templates, and quality checks for multi-framework threat analysis.

**Primary consumer:** threat-model-skill (Phase 3 synthesis, Phase 5 output formatting)

---

## Cross-Framework Integration

### When Multiple Frameworks Identify the Same Threat

1. **Merge into a single finding** — use the most specific description
2. **Note all framework sources** — `framework: combined`
3. **Use the highest applicable confidence** — standards-derived (GROUNDED) trumps STRIDE (may be INFERRED) which trumps attack tree leaves (may be SPECULATIVE)
4. **Combine the reasoning chains** — show how each framework arrived at the same conclusion

### When Frameworks Identify Different Threats

- **STRIDE finds threats that standards-derived misses:** Threats not covered by the spec — potentially novel or implementation-specific. Document and flag for spec gap analysis.
- **Standards-derived finds threats that STRIDE misses:** Threats embedded in specific protocol/spec requirements. STRIDE may be too coarse-grained to catch them.
- **Attack trees find compound threats:** Multi-step scenarios that neither STRIDE nor standards-derived capture individually. The value is identifying attack chains.

### Coverage Gap Analysis

After cross-framework synthesis, produce a gap report:

```
Framework Coverage Gap Analysis
================================

Threats identified by:
  STRIDE only: [count] — [summary of unique findings]
  Standards-derived only: [count] — [summary]
  Attack trees only: [count] — [summary of compound threats]
  Multiple frameworks: [count] — [highest confidence]

Attack surfaces with single-framework coverage:
  [list surfaces covered by only one framework — coverage risks]

Attack surfaces with no framework coverage:
  [list surfaces not covered — these become ABSENT findings]
```

---

## Threat Statement Templates

### Standard Format

Every threat finding should use this statement format:

> "An attacker with **[access level]** can **[action]** the **[target component/interface/asset]** by **[method/technique]**, resulting in **[security impact]**."

### Examples by STRIDE Category

**Spoofing:**
> "An attacker with PCIe fabric access can **impersonate a legitimate TDISP device** by **forging SPDM authentication responses using a stolen or manufactured device certificate**, resulting in **unauthorized device assignment to a trusted domain.**"

**Tampering:**
> "An attacker with local physical access can **corrupt the TDISP state machine** by **injecting voltage glitches during the assignment handshake**, resulting in **the device entering an assignment state without completing security checks.**"

**Repudiation:**
> "An authorized debug operator can **access security-critical registers without audit** because **the debug authentication module does not log successful authentication events**, resulting in **inability to reconstruct the timeline of security-relevant access during incident response.**"

**Information Disclosure:**
> "An attacker with local physical access can **extract the AES key** from the **crypto engine** by **measuring power consumption during encryption operations (DPA)**, resulting in **compromise of all data encrypted with that key.**"

**Denial of Service:**
> "An attacker with PCIe fabric access can **prevent legitimate device assignments** by **flooding the TDISP module with malformed assignment requests that exhaust the state machine's concurrent session capacity**, resulting in **denial of device assignment for legitimate trusted domains.**"

**Elevation of Privilege:**
> "An attacker with user-mode access can **gain kernel-mode access to protected memory regions** by **manipulating a CHERI capability stored in an uninitialized stack location**, resulting in **access to the entire address space with full permissions.**"

### Anti-Patterns (What NOT to Write)

- "The system might be vulnerable." — No specific threat, no specific impact.
- "An attacker could attack the component." — Circular, provides no information.
- "The bus is insecure." — Missing access level, method, and impact.
- "There may be side-channel issues." — Too vague to act on.
