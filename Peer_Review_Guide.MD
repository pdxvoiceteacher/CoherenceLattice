# Peer Review Guide (UVLM / CoherenceLattice)

This repository is built around two reproducibility pillars:

1) **Lean 4 formalization** (machine-checked statements; “no axioms” style where feasible)  
2) **UCC audit pipelines** that emit **hash-bound audit bundles** (inputs/outputs/environment hashes + flags)

> Important: “UCC certification” here means reproducibility + traceability (audit bundles), **not** regulatory compliance.

---

## What reviewers can validate quickly

### A) Lean (formal)
- Theorems and definitions typecheck in Lean (CI green).
- Quantum anchor pack includes:
  - Pauli commutators
  - explicit eigenstates and normalization (finite-dimensional / qubit)
  - two-level partition function and Gibbs normalization
  - a basis-relative off-diagonal “coherence proxy”
  - an algebraic expected-energy identity derived from partition-function weights

### B) Python (tests)
- Python unit tests and property tests (Hypothesis) pass.
- Experiments produce deterministic summaries and can be audited by UCC.

### C) UCC (audit artifacts)
- UCC modules run locally and produce:
  - `report.json` (metrics + flags)
  - `audit_bundle.json` (hashes, environment, git commit)
  - additional artifacts depending on module (checklists, comparisons, delta curves, logs)

---

## Reproduce locally (recommended path)

### 1) Clone + enter repo
```bash
git clone https://github.com/pdxvoiceteacher/CoherenceLattice.git
cd CoherenceLattice

2) Lean build
lake exe cache get
lake build

3) Lean spot-check: Quantum anchors

A reviewer-friendly scratch file is included:

lake env lean ScratchQuantum.lean

This prints #check results for the key quantum theorems.



Python + UCC setup (single venv)
Windows PowerShell
python -m venv .venv
.\.venv\Scripts\python.exe -m pip install -U pip

# Python package tests
cd python
..\.\.venv\Scripts\python.exe -m pip install -e ".[dev]"
..\.\.venv\Scripts\python.exe -m pytest -q
cd ..

# UCC tests
.\.venv\Scripts\python.exe -m pip install -e ".\ucc[dev]"
cd ucc
..\.\.venv\Scripts\python.exe -m pytest -q
cd ..

Linux/macOS (bash)
python3 -m venv .venv
./.venv/bin/python -m pip install -U pip

cd python
../.venv/bin/python -m pip install -e ".[dev]"
../.venv/bin/python -m pytest -q
cd ..

./.venv/bin/python -m pip install -e "./ucc[dev]"
cd ucc
../.venv/bin/python -m pytest -q
cd ..

Run the key UCC demos

All UCC outputs go under ucc/out/ and should remain uncommitted/ignored.

A) Quantum anchor coverage (checklist + audit bundle)
python -m ucc.cli run ucc/modules/quantum_anchor_coverage.yml \
  --input ucc/tasks/quantum_anchor_task.json \
  --outdir ucc/out/quantum_anchor_demo

B) Quantum Lean symbol verification (writes ScratchLeanSymbols.lean + lean_check.log)
python -m ucc.cli run ucc/modules/quantum_anchor_lean_symbols.yml \
  --input ucc/tasks/quantum_anchor_lean_symbols.json \
  --outdir ucc/out/quantum_anchor_lean_symbols_demo

C) Helmholtz guided vs unguided ΔΨ comparator (delta curve + audit bundle)
python -m ucc.cli run ucc/modules/helmholtz_compare.yml \
  --input ucc/tasks/helmholtz_compare_sample.json \
  --outdir ucc/out/helmholtz_demo

D) TCHES baseline vs lambda comparator (comparison + audit bundle)
python -m ucc.cli run ucc/modules/tches_compare.yml \
  --input ucc/tasks/tches_compare_sample.json \
  --outdir ucc/out/tches_demo

E) MC-AI salvage coverage (parity + harmonic recall coverage)
python -m ucc.cli run ucc/modules/mc_ai_salvage_coverage.yml \
  --input ucc/tasks/mc_ai_salvage_task.json \
  --outdir ucc/out/mc_ai_salvage_demo

How to review an audit bundle

Open any ucc/out/**/audit_bundle.json and look for:

environment.git_commit — exact code revision

input.sha256 — hash of the input file

module.sha256 — hash of the module YAML

outputs.{...} — hashes for emitted files

metrics and flags — the measured outcomes and any pass/fail decisions

This makes reproductions checkable even across machines.

Snapshot-robust quantum choices (mathlib compatibility)

Some mathlib snapshots vary in which convenience lemmas/names are available. To keep the repo build-stable across snapshots, the quantum pack intentionally uses:

absSq z = z.re^2 + z.im^2 as a magnitude proxy in Density.lean instead of Complex.abs.

Algebraic partition-function analysis in ThermoExtras.lean instead of a calculus proof of ⟨H⟩ = −∂β log Z.
The expected-energy identity is derived directly from Gibbs weights (still standard statistical mechanics), avoiding derivative simp-lemmas that can differ across snapshots.

Where to leave feedback

GitHub Issues: reproducibility failures, naming clarity, missing references, suggested tests

Pull Requests: improvements to proofs/tests/docs, new UCC modules, additional anchor systems

Thank you for taking the time to review.


---

