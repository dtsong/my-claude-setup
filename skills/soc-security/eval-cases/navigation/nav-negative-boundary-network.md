# Navigation Eval Case: Negative Boundary — Network Port Scanning

## Metadata
- **Case ID:** NAV-009
- **Tier:** 1 (simple)
- **Expected Route:** decline
- **Navigation Challenge:** "scan for vulnerabilities" could superficially match security analysis skills, but the request is entirely network-scoped; coordinator must not confuse network security with hardware security

## Input
```json
{
  "user_prompt": "Scan our network for open ports and vulnerabilities",
  "context": "The user wants a network vulnerability scan of their infrastructure. This involves port scanning, service enumeration, and CVE checking against network-exposed services. No SoC, embedded device firmware, or hardware security concern is mentioned."
}
```

## Expected Routing Behavior
The coordinator should decline this request. Network port scanning and vulnerability assessment is network security, which is explicitly excluded from the soc-security-skills scope ("Do NOT use for software-only security, network security, or web application security"). None of the specialist skills handle network scanning, port enumeration, or network-level CVE analysis. The coordinator should clearly state the scope limitation and suggest appropriate network security tools (nmap, Nessus, OpenVAS, etc.) instead.

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Does NOT route to any specialist skill
- [ ] Recognizes the request as network security, outside SoC hardware scope
- [ ] Does NOT attempt to reinterpret "vulnerabilities" as hardware vulnerabilities

### Should Pass (partial credit)
- [ ] Explicitly mentions network security as an exclusion category
- [ ] Suggests appropriate network security tools or approaches
- [ ] Clearly distinguishes network vulnerability scanning from hardware security analysis

### Bonus
- [ ] Offers to help if the user's network includes SoC/embedded devices with hardware security concerns
- [ ] Lists all three exclusion categories from the skill description

## Raw Trace Log
