from pathlib import Path
import sys

REPO_ROOT = Path(__file__).resolve().parents[3]
SRC_PATH = REPO_ROOT / "python" / "src"
if SRC_PATH.exists() and str(SRC_PATH) not in sys.path:
    sys.path.insert(0, str(SRC_PATH))

from coherence_music.quantum_mapper import SerialQuantumMapper
from coherence_music.midi import write_midi

out = Path("python/experiments/coherence_music/out")
out.mkdir(parents=True, exist_ok=True)

bits = "0100110101110010"
mapper = SerialQuantumMapper(seed=42, octave=4)
seq = mapper.translate_bitstring(bits, bpm=120, dur_beats=0.5)

midi_path = write_midi(seq.flatten_notes(), out / "quantum_serial_bits.mid", bpm=seq.bpm)
print("Wrote:", midi_path)
