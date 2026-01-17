from pathlib import Path
import sys

REPO_ROOT = Path(__file__).resolve().parents[3]
SRC_PATH = REPO_ROOT / "python" / "src"
if SRC_PATH.exists() and str(SRC_PATH) not in sys.path:
    sys.path.insert(0, str(SRC_PATH))

from coherence_music.raga import bhairav_profile
from coherence_music.engine import EngineConfig, CoherenceMusicEngine
from coherence_music.midi import write_midi

out = Path("python/experiments/coherence_music/out")
out.mkdir(parents=True, exist_ok=True)

# toy coherence metrics (0..1), 16 steps
metrics = {
    "E":        [0.2,0.2,0.3,0.4,0.6,0.8,0.9,0.7,0.4,0.3,0.2,0.2,0.3,0.4,0.5,0.6],
    "T":        [0.1,0.1,0.2,0.3,0.3,0.4,0.6,0.7,0.5,0.4,0.3,0.2,0.2,0.2,0.3,0.3],
    "DELTA_S":  [0.1,0.1,0.1,0.2,0.2,0.3,0.3,0.4,0.6,0.8,0.7,0.5,0.3,0.2,0.2,0.1],
    "E_SYM":    [0.4,0.41,0.42,0.43,0.44,0.46,0.48,0.47,0.45,0.44,0.43,0.42,0.41,0.40,0.39,0.38],
    "LAMBDA":   [0.2,0.2,0.25,0.3,0.35,0.5,0.65,0.72,0.8,0.9,0.6,0.4,0.3,0.2,0.2,0.2],
}

profile = bhairav_profile(tonic_midi=60)  # C4 tonic
cfg = EngineConfig(bpm=92, seed=7)
engine = CoherenceMusicEngine(profile, cfg)

seq = engine.generate(metrics, name="bhairav_guft_demo")
midi_path = write_midi(seq.flatten_notes(), out / "bhairav_guft_demo.mid", bpm=seq.bpm)

print("Wrote:", midi_path)
print("First 8 phrase labels:", [p.label for p in seq.phrases[:8]])
print("First 8 categories:", [p.category for p in seq.phrases[:8]])
