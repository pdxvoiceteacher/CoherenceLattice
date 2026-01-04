# Summary
This coherence run audits the Helmholtz guided-vs-unguided ΔΨ comparator artifacts produced by UCC:
comparison.json/.md, delta_curve.csv, and audit_bundle.json.

# Assumptions
- Toy experiment; proxy coherence only; not a physics claim.
- Audit improves traceability; it is not a truth guarantee.

# Limitations
- Comparator summarizes a specific input summary CSV; results depend on that artifact.
- ΔS/Λ are proxy stability checks on paraphrases.

# Uncertainty
- If the comparator outputs change, rerun this audit.

# Disclosure
Research scaffold only. Report issues via GitHub.

# Results
The comparator records ΔΨ_start/peak/end, AUC(ΔΨ), and pass/fail flags in comparison.json and binds provenance in audit_bundle.json.
