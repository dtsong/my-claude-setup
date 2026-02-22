# Navigation Eval Case: Negative Boundary — Software-Only Django Auth

## Metadata
- **Case ID:** NAV-008
- **Tier:** 1 (simple)
- **Expected Route:** decline
- **Navigation Challenge:** Request is entirely software-scoped (web application authentication) with no hardware or SoC component; coordinator must recognize scope boundary and decline rather than force-fitting into a hardware security skill

## Input
```json
{
  "user_prompt": "Review the authentication logic in our Django web app",
  "context": "The user is working on a Python Django web application and wants a security review of the login/authentication flow. There is no SoC, no hardware IP, no RTL, and no embedded system involved."
}
```

## Expected Routing Behavior
The coordinator should decline this request. The soc-security-skills suite is explicitly scoped to hardware security analysis for System-on-Chip components. Django web application authentication is software-only security, which is listed as an exclusion in the coordinator's description ("Do NOT use for software-only security, network security, or web application security"). The coordinator should politely explain the scope boundary and suggest the user seek a software security review tool or manual code review instead.

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Does NOT route to any specialist skill
- [ ] Recognizes the request as outside the SoC hardware security scope
- [ ] Communicates that the skill suite does not cover software-only security

### Should Pass (partial credit)
- [ ] Explicitly states the scope boundary: SoC/hardware security vs software/web application security
- [ ] Provides a helpful suggestion for what the user should use instead
- [ ] References the exclusion criteria from the skill description

### Bonus
- [ ] Offers to help if the user has a hardware security question related to the system
- [ ] Notes specific exclusion categories: software-only, network, web application

## Raw Trace Log
