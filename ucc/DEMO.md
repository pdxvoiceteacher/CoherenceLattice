# UCC DEMO (v0.1): Auditable Governance Artifacts in Minutes

This demo shows how UCC produces **auditable control artifacts**:
- schema-validated modules
- deterministic reports
- threshold/checklist tables
- comparative audits (delta reports)
- cryptographic audit bundles (hashes + environment + git commit)

> Safety note: UCC is a research scaffold. Do not run untrusted modules.
> UCC executes only built-in step types (no arbitrary code execution).

---

## 0) Prereqs (local)

From repo root:

```powershell
# Create/activate your existing venv if needed; otherwise skip.
cd C:\Users\pdxvo\Documents\Lean\CoherenceLattice

# Install UCC (editable) into your existing python venv
.\python\.venv\Scripts\python.exe -m pip install -U pip
.\python\.venv\Scripts\python.exe -m pip install -e .\ucc[dev]

## Coherence Runs (Helmholtz / TCHES / Quantum)

This repo includes reproducible “coherence audits” that bind claims → sources and emit an auditable bundle (metrics + flags + hashes).

### Run all three coherence audits (Windows PowerShell)

From repo root:

```powershell
powershell -ExecutionPolicy Bypass -File ucc\notes\coherence_runs\MakeCoherenceRuns.ps1

### Strict mode (peer-review readiness)

Strict mode uses:
- `ucc/modules/coherence_audit_strict.yml`
- perturbations JSON files for ΔS/Λ

Run:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File ucc\notes\coherence_runs\MakeCoherenceRuns.ps1 -PythonExe .\python\.venv\Scripts\python.exe -Strict
