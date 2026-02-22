# Navigation Eval Case: Microarchitectural vs Physical — Crypto Accelerator Side Channels

## Metadata
- **Case ID:** NAV-003
- **Tier:** 2 (medium)
- **Expected Route:** physical-sca-skill (with clarification)
- **Navigation Challenge:** "side-channel vulnerabilities" is shared vocabulary between microarch-attack and physical-sca; "crypto accelerator" suggests physical SCA (DPA/SPA on crypto), but "side-channel" alone could also mean cache timing attacks

## Input
```json
{
  "user_prompt": "Analyze side-channel vulnerabilities in our crypto accelerator",
  "context": "The crypto accelerator is a dedicated hardware IP block for AES and SHA operations. No specification of whether the concern is cache-based microarchitectural leaks or physical power/EM side channels. The block has both a shared cache interface and exposed power rails."
}
```

## Expected Routing Behavior
The coordinator should either clarify whether the user means physical side channels (DPA/SPA/EM) or microarchitectural side channels (cache timing), or default to physical-sca-skill. The reasoning: "crypto accelerator" as a dedicated hardware IP is more commonly associated with physical side-channel attacks (DPA, SPA) than microarchitectural transient execution attacks. Microarch-attack-skill targets CPU-centric Spectre/Meltdown/MDS patterns. If clarifying, the coordinator should present both options with clear descriptions.

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Identifies both physical-sca-skill and microarch-attack-skill as candidates
- [ ] Does NOT silently route to only one skill without acknowledging the ambiguity
- [ ] If routing without clarification, chooses physical-sca-skill (crypto accelerator DPA/SPA is the more natural fit)

### Should Pass (partial credit)
- [ ] Explains the distinction: physical SCA = power/EM analysis on dedicated crypto hardware vs microarch = cache timing on CPU pipelines
- [ ] Asks the user to clarify which type of side-channel analysis they need
- [ ] Mentions DPA/SPA as the physical SCA concern and cache timing as the microarch concern

### Bonus
- [ ] Notes that if the crypto accelerator shares a cache with the CPU, microarch-attack may also be relevant
- [ ] Proposes running both analyses if budget allows

## Raw Trace Log
