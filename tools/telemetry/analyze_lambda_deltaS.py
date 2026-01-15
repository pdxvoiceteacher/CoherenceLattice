from __future__ import annotations
import json
from pathlib import Path
import sys

def load_metrics(telemetry_path: Path) -> dict:
    d = json.loads(telemetry_path.read_text(encoding="utf-8"))
    # adjust if your schema nests differently
    return d.get("coherence_metrics", d.get("coherenceMetrics", {}))

def main() -> int:
    if len(sys.argv) < 3:
        print("usage: analyze_lambda_deltaS.py <unguided_telemetry.json> <guided_telemetry.json>")
        return 2

    u = load_metrics(Path(sys.argv[1]))
    g = load_metrics(Path(sys.argv[2]))

    def get(m, k, default=None):
        return m.get(k, default)

    # Minimal invariants: both should exist
    for label, m in [("unguided", u), ("guided", g)]:
        if get(m, "Λ") is None and get(m, "lambda") is None:
            print(f"{label}: missing Λ")
            return 3
        if get(m, "ΔS") is None and get(m, "deltaS") is None:
            print(f"{label}: missing ΔS")
            return 3

    # Normalize key names
    def norm(m):
        return {
            "lambda": m.get("Λ", m.get("lambda")),
            "deltaS": m.get("ΔS", m.get("deltaS")),
        }

    u2, g2 = norm(u), norm(g)

    print("UNGUIDED:", u2)
    print("GUIDED:", g2)

    # A very conservative check: guided should not increase both Lambda and deltaS vs unguided.
    # (You can tighten later.)
    if (g2["lambda"] is not None and u2["lambda"] is not None and
        g2["deltaS"] is not None and u2["deltaS"] is not None):
        if g2["lambda"] > u2["lambda"] and g2["deltaS"] > u2["deltaS"]:
            print("FAIL: guided worsened both Λ and ΔS")
            return 4

    print("OK")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
