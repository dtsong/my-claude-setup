# Eval Case: Basic Chiplet Trust Boundary Assessment

## Metadata
- **Case ID:** EH-002
- **Tier:** 1 (simple)
- **Skill Route:** emerging-hw-security-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Assess the trust boundaries for our chiplet-based data-center SoC. The SoC uses UCIe (Universal Chiplet Interconnect Express) to connect:\n- Compute die: 4nm process, CPU cores + L3 cache (designed in-house)\n- IO die: 7nm process, PCIe 5.0 + CXL controllers (designed in-house)\n- Memory die: HBM3 stack (third-party vendor, JEDEC HBM3 interface)\n\nUCIe configuration:\n- UCIe 1.1 standard\n- D2D (die-to-die) adapter with CRC for link integrity\n- No encryption on the UCIe link (plaintext die-to-die communication)\n- No authentication between dies at link layer\n- Organic substrate (advanced package, no silicon interposer)\n\nTrust model:\n- Compute die and IO die are trusted (same design house, same fab)\n- Memory die is third-party — treated as untrusted for confidentiality but trusted for availability\n- No IDE (Integrity and Data Encryption) deployed on UCIe links\n\nMaturity: early-adoption. No prior chiplet security assessment.\nSoC family: Data Center. Technology domain: Chiplet/UCIe Architecture.",
  "context": "Basic chiplet trust boundary assessment. Three dies connected via UCIe. Third-party memory die is the untrusted component. No link encryption or authentication. Simple trust model to assess."
}
```

## Expected Output
EmergingHWFindings covering:
- Trust boundary between in-house dies and third-party memory die
- Lack of UCIe link encryption exposing data in transit between dies
- Lack of die-to-die authentication allowing potential die substitution
- Organic substrate as an interposition attack surface
- Maturity assessment for UCIe 1.1 security features

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains at least one EmergingHWFinding for chiplet trust boundary risk
- [ ] Finding specifies paradigm as chiplet-ucie
- [ ] Finding includes maturityLevel assessment
- [ ] Finding identifies the third-party memory die as an untrusted trust boundary crossing
- [ ] Finding has a confidence tier and severity rating
- [ ] Finding has a research reference or `[FROM TRAINING]` marker

### Should Pass (partial credit)
- [ ] Lack of UCIe link encryption explicitly flagged — data (including crypto keys, application data) visible in plaintext between dies
- [ ] Lack of die-to-die authentication flagged — a malicious die could be substituted during assembly
- [ ] Organic substrate identified as accessible for physical interposition (probe, MITM on D2D link)
- [ ] UCIe IDE (Integrity and Data Encryption) recommended as the primary mitigation
- [ ] Paradigm coverage table present showing chiplet/UCIe as analyzed

### Bonus
- [ ] Notes that CRC provides integrity against random errors but not adversarial tampering — MAC/signature needed
- [ ] Assesses supply chain risk: third-party memory die manufactured at a different fab creates a supply chain trust gap
- [ ] Identifies that HBM3 JEDEC interface does not include encryption — confidentiality must be enforced at the UCIe D2D layer

## Raw Trace Log
