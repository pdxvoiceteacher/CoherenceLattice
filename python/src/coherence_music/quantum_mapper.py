from __future__ import annotations

import math
import random
from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence as SeqT, Tuple

from .core import Note, Phrase, Sequence, clamp01, clamp_int, midi_from_name

"""
Quantum → Music mapping (starter).

This is a minimal, orthodox sonification scaffold:
- energy levels → pitches (higher energy → higher pitch)
- probabilities → velocity (loudness)
- serial mapping: tone row + transformations (inversion/retrograde/transposition)
The "equal probability ↔ equal note emphasis" motivation for 12-tone is in the GUFT doc. 
"""


def energy_to_midi(
    energy: float,
    e_min: float,
    e_max: float,
    base: int = 48,     # C3
    span: int = 36,     # 3 octaves
) -> int:
    if e_max <= e_min:
        return base
    x = (energy - e_min) / (e_max - e_min)
    x = clamp01(x)
    return clamp_int(int(round(base + span * x)), 0, 127)


def prob_to_velocity(p: float, vmin: int = 20, vmax: int = 120) -> int:
    p = clamp01(p)
    return clamp_int(int(round(vmin + (vmax - vmin) * p)), 1, 127)


@dataclass
class QuantumSnapshot:
    energies: List[float]
    probs: List[float]
    dt_beats: float = 1.0


class WesternQuantumMapper:
    """
    Map each energy+prob into a single note per time step (choose max-prob state).
    """
    def translate(self, snaps: List[QuantumSnapshot], bpm: int = 120) -> Sequence:
        all_e = [e for s in snaps for e in s.energies]
        e_min, e_max = (min(all_e), max(all_e)) if all_e else (0.0, 1.0)

        phrases: List[Phrase] = []
        for i, s in enumerate(snaps):
            if not s.energies or not s.probs or len(s.energies) != len(s.probs):
                continue
            j = max(range(len(s.probs)), key=lambda k: s.probs[k])
            pitch = energy_to_midi(s.energies[j], e_min, e_max, base=60, span=24)  # around C4
            vel = prob_to_velocity(s.probs[j])
            phrases.append(Phrase(label=f"Q{i+1}", notes=[Note(pitch, s.dt_beats, vel)], category="QUANTUM"))
        return Sequence(phrases=phrases, bpm=bpm, name="quantum_western")


# ---- Serial / dodecaphonic scaffold ----

PitchClass = int  # 0..11


def make_tone_row(seed: int = 0) -> List[PitchClass]:
    rng = random.Random(seed)
    pcs = list(range(12))
    rng.shuffle(pcs)
    return pcs


def transpose_row(row: SeqT[PitchClass], n: int) -> List[PitchClass]:
    return [int((pc + n) % 12) for pc in row]


def invert_row(row: SeqT[PitchClass]) -> List[PitchClass]:
    """
    Inversion around first pitch class: intervals are negated.
    """
    if not row:
        return []
    root = row[0]
    inv = [root]
    for pc in row[1:]:
        interval = (pc - root) % 12
        inv.append((root - interval) % 12)
    return [int(x) for x in inv]


def retrograde_row(row: SeqT[PitchClass]) -> List[PitchClass]:
    return list(reversed([int(x) for x in row]))


def pc_to_midi(pc: PitchClass, octave: int = 4) -> int:
    # map pitch class to C-based MIDI in given octave
    return 12 * (octave + 1) + int(pc)


class SerialQuantumMapper:
    """
    Very small 12-tone engine:
    - Build a row (seeded)
    - Encode a bitstring by appending triads from the row:
        bit=0 -> next 3 pcs in order
        bit=1 -> next 3 pcs in inverted row (same index)
    This aligns with the doc’s idea that bit outcomes can map to ascending/descending motifs
    and that serial structure can be used as an analytical audit channel. 
    """
    def __init__(self, seed: int = 0, octave: int = 4):
        self.row = make_tone_row(seed)
        self.row_inv = invert_row(self.row)
        self.octave = octave

    def translate_bitstring(self, bits: str, bpm: int = 120, dur_beats: float = 0.5) -> Sequence:
        phrases: List[Phrase] = []
        idx = 0
        for i, b in enumerate(bits.strip()):
            base = self.row if b == "0" else self.row_inv
            tri = [base[(idx + k) % 12] for k in range(3)]
            idx = (idx + 3) % 12
            notes = [Note(pc_to_midi(pc, self.octave), dur_beats, 90) for pc in tri]
            phrases.append(Phrase(label=f"bit{i+1}_{b}", notes=notes, category="SERIAL"))
        return Sequence(phrases=phrases, bpm=bpm, name="quantum_serial_bits")
