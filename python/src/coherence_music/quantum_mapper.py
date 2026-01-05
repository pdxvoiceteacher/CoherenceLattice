from __future__ import annotations

import random
from dataclasses import dataclass
from typing import List, Sequence as SeqT

from .core import Note, Phrase, Sequence, clamp01, clamp_int


PitchClass = int  # 0..11


def make_tone_row(seed: int = 0) -> List[PitchClass]:
    rng = random.Random(seed)
    pcs = list(range(12))
    rng.shuffle(pcs)
    return pcs


def invert_row(row: SeqT[PitchClass]) -> List[PitchClass]:
    if not row:
        return []
    root = int(row[0])
    inv = [root]
    for pc in row[1:]:
        interval = (int(pc) - root) % 12
        inv.append((root - interval) % 12)
    return [int(x) for x in inv]


def pc_to_midi(pc: PitchClass, octave: int = 4) -> int:
    return 12 * (octave + 1) + int(pc)


class SerialQuantumMapper:
    def __init__(self, seed: int = 0, octave: int = 4):
        self.row = make_tone_row(seed)
        self.row_inv = invert_row(self.row)
        self.octave = int(octave)

    def translate_bitstring(self, bits: str, bpm: int = 120, dur_beats: float = 0.5) -> Sequence:
        phrases: List[Phrase] = []
        idx = 0
        for i, b in enumerate(bits.strip()):
            base = self.row if b == "0" else self.row_inv
            tri = [base[(idx + k) % 12] for k in range(3)]
            idx = (idx + 3) % 12
            notes = [Note(pc_to_midi(pc, self.octave), float(dur_beats), 90) for pc in tri]
            phrases.append(Phrase(label=f"bit{i+1}_{b}", notes=notes, category="SERIAL"))
        return Sequence(phrases=phrases, bpm=int(bpm), name="quantum_serial_bits")