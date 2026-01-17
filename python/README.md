# coherence-sim

This is a lightweight Python simulation harness that mirrors the Lean model:
- τ0..τ3 thresholds
- Ψ = E*T
- classify + adjacency graph
- ΔSyn-based stepPsi and stepET (capped/clamped)

## Experiments

Install local sources and experiment dependencies:

```bash
pip install -e "python[experiments]"
```

Then run experiment scripts from the repo root, for example:

```bash
python python/experiments/konomi_smoke/run_smoke.py --quick
python python/experiments/coherence_music/demo_bhairav.py
```
