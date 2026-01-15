# UCC Constitution
## Consent • Repair • Legibility • Auditability

The Universal Control Codex (UCC) is a governance runtime for reasoning systems.  
Its purpose is not to increase control for its own sake, but to increase **legibility**, **safety**, and **repairability** while preserving **human dignity** and **ongoing, revocable consent**.

This repository is a public commons. Contributions must strengthen the commons, not create new markets of coercion or opacity.

---

## 1) Core invariant: Collapse → Repair → Translation → Access (CRTA)

Any UCC module, pipeline, or “authority pack” MUST be designed such that:

1. **Collapse** is detectable  
   - We name drift, uncertainty, missing evidence, or contradictions explicitly.
2. **Repair** is possible without shame or blame  
   - The default response to instability is repair, not punishment.
3. **Translation** is required before enforcement  
   - Findings must be translated to the user’s context and capacity (plain-language available).
4. **Access** is granted with consent-aware gating  
   - Actions that affect stakeholders require explicit disclosure and escalation paths.

CRTA is a *design invariant*: if a change breaks this chain, it is a rejection candidate.

---

## 2) Non-negotiables

### Consent-first
- Consent is ongoing and revocable.
- Escalation paths must exist (human review is allowed and sometimes required).
- Refusal is acceptable when evidence is insufficient or harm risk is high.

### Legibility over power
- Prefer explanations, provenance, and minimalism over authority.
- If a change reduces transparency or increases “black box” behavior, it is presumptively rejected.

### Auditability over persuasion
- Outputs must be auditable (inputs, versions, hashes, and decision points).
- Exceptions must be explicit and time-bounded (expiry dates).

### No dehumanization; label patterns, not people
- UCC may diagnose *failure modes* and *pattern clusters*.
- UCC must not be used to brand people as enemies or subhuman.
- “Empire” is a diagnostic pattern of governance failure, not an identity label.

---

## 3) Rejection criteria (“Do Not Merge”)

A proposal SHOULD be rejected if it:

1. **Reduces transparency** (less provenance, fewer limitations/uncertainty disclosures)
2. **Collapses consent** (no escalation channel, no refusal mode, coercive defaults)
3. **Centralizes authority without auditability** (no review cycle, no exceptions, no traceable outputs)

---

## 4) Minimum required disclosures (public modules)

Every public-facing module SHOULD include:
- Assumptions
- Limitations
- Uncertainty / confidence bounds
- Disclosure statement
- Reporting channel + escalation path
- Evidence links (or explicit “no evidence available” with rationale)
- Review cadence + exception expiry policy

---

## 5) Governance and contribution expectations

- All changes should ship with a CI-checked fixture task and a module that validates required structure.
- Prefer “IDs + structure only” for copyrighted standards; do not paste long standard text into the repo.
- Any user-sensitive information must be handled with explicit consent and minimal retention.

---

## 6) Safety disclaimer

UCC outputs are governance and audit scaffolds, not guarantees of truth.  
High-stakes decisions require qualified human review.
