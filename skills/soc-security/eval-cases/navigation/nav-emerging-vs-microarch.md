# Navigation Eval Case: Emerging HW vs Microarchitectural — AI Accelerator Cache Timing

## Metadata
- **Case ID:** NAV-006
- **Tier:** 2 (medium)
- **Expected Route:** microarch-attack-skill
- **Navigation Challenge:** "neural network accelerator" suggests emerging-hw-security (AI accelerator security), but "cache timing leaks" is a core microarch-attack keyword; the attack vector determines the routing, not the target component

## Input
```json
{
  "user_prompt": "Check our neural network accelerator for cache timing leaks",
  "context": "The SoC includes a dedicated NPU (neural processing unit) that shares the L2 cache with the application processor. Concern is that inference workloads create observable cache access patterns that leak model architecture or input data. No prior analysis of either the NPU architecture novelty or cache side-channel exposure."
}
```

## Expected Routing Behavior
The coordinator should route to microarch-attack-skill. Although the target component (neural network accelerator) falls under emerging-hw-security territory, the specific attack vector described is cache timing leaks, which is a core competency of microarch-attack-skill (Spectre, cache side-channels, branch predictor attacks). The emerging-hw-security-skill handles novel architectural concerns like PQC migration, chiplet security, and AI accelerator trust boundaries, but cache timing analysis methodology is the same regardless of the component being analyzed. The coordinator should note that emerging-hw-security may provide supplementary context about NPU-specific attack surfaces.

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Routes to microarch-attack-skill as the primary skill
- [ ] Recognizes "cache timing leaks" as a microarch-attack keyword
- [ ] Does NOT route to emerging-hw-security-skill as the primary skill

### Should Pass (partial credit)
- [ ] Explains that attack methodology (cache timing) determines routing over target component (NPU)
- [ ] Notes that emerging-hw-security may provide supplementary NPU architecture context
- [ ] Identifies shared L2 cache as the relevant attack surface for cache side-channel analysis

### Bonus
- [ ] Notes that model architecture leakage via cache patterns is an active research area
- [ ] Suggests a follow-up with emerging-hw-security for broader NPU threat surface beyond cache timing

## Raw Trace Log
