# Summary
This coherence run audits the repo artifacts for the Helmholtz toy guided-vs-unguided comparison using UCC outputs.

# Assumptions
- Toy experiment; proxy coherence only; not a physics claim.
- Coherence audit improves traceability, not truth guarantees.

# Limitations
- Comparator summarizes a specific input CSV; results depend on that summary.
- Drift/criticality are token/label proxies.

# Uncertainty
- Outputs depend on the summary file and thresholds. Rerun if artifacts change.

# Disclosure
Research scaffold only. Report issues via GitHub.

# Results
- Comparator emits comparison.md and audit_bundle.json.
- Delta curve artifact is preserved for inspection.