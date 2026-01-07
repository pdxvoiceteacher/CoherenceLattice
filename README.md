
---

## Build status

<!-- Replace <OWNER>/<REPO> and workflow filenames if needed -->
**Lean proofs:**  
[![Lean proofs](https://github.com/pdxvoiceteacher/CoherenceLattice/actions/workflows/lean_proofs_ci.yml/badge.svg?branch=master)](https://github.com/pdxvoiceteacher/CoherenceLattice/actions/workflows/lean_proofs_ci.yml?query=branch%3Amaster)

**Python + UCC + KONOMI:**  
[![Python + UCC + KONOMI](https://github.com/pdxvoiceteacher/CoherenceLattice/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/pdxvoiceteacher/CoherenceLattice/actions/workflows/ci.yml?query=branch%3Amaster)

## What’s implemented (high-level)
# CoherenceLattice (Lean + Python + UCC)

This repository is a reproducible research + governance scaffold that combines:

- **Lean 4 formalization** (machine-checked theorems; “hard-to-reject” anchors)
- **Python reference implementations** (toy experiments + benchmarks)
- **UCC (Universal Control Codex)** — an auditable pipeline format that emits **hash-bound audit bundles** for experiments, checks, and reports

> “UCC certification” in this repo means **reproducibility + traceability** (inputs/outputs/env hashed in `audit_bundle.json`) — **not** regulatory compliance.

### Lean: formal anchors
- **Coherence lattice core**: state/regime machinery + “no teleport” adjacency constraints
- **ΔSyn-inspired dynamics**: step functions with bounded drift and monotonicity lemmas (where applicable)
- **Quantum anchor pack (orthodox qubit basis)**:
  - Pauli commutators
  - σz and σx eigenstates + normalization/orthogonality
  - two-level partition function and Gibbs trace normalization
  - basis-relative “off-diagonal coherence proxy”
  - expected-energy identity derived from partition-function weights (algebraic, snapshot-robust)

### Python: experiments + benchmarks
- **Helmholtz toy**: guided vs unguided ΔΨ curve (CSV summaries + UCC comparator)
- **TCHES ODE toy**: baseline vs lambda comparisons + sweeps + plots
- **CGL–KG toy**: stability testbed with Λ-proxy audit
- **KONOMI v0 scaffolds (CPU-first)**:
  - eVGPU ops (NumPy/BLAS) + benchmark harness
  - FemtoModel async stub + concurrency benchmark
  - BlockArray sparse chunked 1000³ address space + bounded scan benchmark
  - Cube runtime: 9-node deterministic routing + backpressure + benchmark
  - API scaffold: FastAPI + WebSocket demo + auth + rate limiting
  - API hardening: request-id propagation + audit JSONL logging + module registry endpoint

### UCC: audit pipelines (hash-bound, reproducible)
- UCC modules validate both **toy experiments** and **governance checklists** by emitting:
  - `report.json` (metrics + flags)
  - `audit_bundle.json` (hashes, environment, git commit)
  - module-specific artifacts (threshold tables, checklists, delta curves, logs)

---

## Quickstart (reviewers)

### 1) Lean build
```powershell
lake exe cache get
lake build

### 2) Python + UCC tests
# from repo root
python -m venv .venv
.\.venv\Scripts\python.exe -m pip install -U pip

# python package
cd python
..\.\.venv\Scripts\python.exe -m pip install -e ".[dev]"
..\.\.venv\Scripts\python.exe -m pytest -q
cd ..

# ucc package
.\.venv\Scripts\python.exe -m pip install -e ".\ucc[dev]"
cd ucc
..\.\.venv\Scripts\python.exe -m pytest -q
cd ..

# from repo root
python -m venv .venv
.\.venv\Scripts\python.exe -m pip install -U pip

# python package
cd python
..\.\.venv\Scripts\python.exe -m pip install -e ".[dev]"
..\.\.venv\Scripts\python.exe -m pytest -q
cd ..

# ucc package
.\.venv\Scripts\python.exe -m pip install -e ".\ucc[dev]"
cd ucc
..\.\.venv\Scripts\python.exe -m pytest -q
cd ..
3) Read the reviewer guide
PEER_REVIEW_GUIDE.md

ucc/DEMO.md

These include copy/paste commands to reproduce key audits.

How to interpret results
Lean: if it builds, the theorems typecheck (formal anchor)

Python: tests validate invariants + toy implementations

UCC: audit bundles bind results to code revision + inputs via SHA-256 hashes

Notes on snapshot robustness
Some mathlib snapshots vary in convenience lemma availability. We keep quantum anchors build-stable by using:

absSq z = z.re^2 + z.im^2 as a magnitude proxy (instead of Complex.abs)

algebraic partition-function analysis rather than derivative simp-lemmas

Contributing / peer review
Issues and PRs are welcome:

proof improvements / new Lean anchors

additional UCC modules / authority packs

experiments + benchmarks that emit auditable artifacts


---
