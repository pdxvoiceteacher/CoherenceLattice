from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, List, Optional, Sequence as SeqT, Tuple


@dataclass(frozen=True)
class Note:
    """
    Minimal note primitive for MIDI output.
    pitch: MIDI note number 0..127
    duration_beats: beats (quarter note = 1.0)
    velocity: MIDI velocity 1..127
    channel: 0..15
    """
    pitch: int
    duration_beats: float = 1.0
    velocity: int = 80
    channel: int = 0


@dataclass(frozen=True)
class Phrase:
    """
    A short motif / phrase (often 1–2 bars).
    category is useful for auditing (BASE/E/T/PSI/DELTA_S/E_SYM/LAMBDA etc.).
    """
    label: str
    notes: List[Note]
    category: str = "BASE"


@dataclass(frozen=True)
class Sequence:
    """A realized musical sequence: ordered phrases plus metadata."""
    phrases: List[Phrase]
    bpm: int = 120
    name: str = "coherence_sequence"

    def flatten_notes(self) -> List[Note]:
        out: List[Note] = []
        for ph in self.phrases:
            out.extend(ph.notes)
        return out


# --- Pitch helpers (very small, no external deps) ---

_NOTE_TO_SEMITONE = {
    "C": 0, "C#": 1, "Db": 1,
    "D": 2, "D#": 3, "Eb": 3,
    "E": 4,
    "F": 5, "F#": 6, "Gb": 6,
    "G": 7, "G#": 8, "Ab": 8,
    "A": 9, "A#": 10, "Bb": 10,
    "B": 11,
}


def midi_from_name(name: str) -> int:
    """
    Convert pitch name like 'C4' or 'Db3' to MIDI note number.
    MIDI convention: C4 = 60.
    """
    name = name.strip()
    if len(name) < 2:
        raise ValueError(f"Bad pitch name: {name}")
    # split note part + octave (supports C#4, Db4)
    note_part = name[:-1]
    octave_part = name[-1]
    if name[-2].isdigit():
        # octave has 2 digits (e.g. C10) – rare but handle
        # find last digit run
        i = len(name) - 1
        while i >= 0 and name[i].isdigit():
            i -= 1
        note_part = name[: i + 1]
        octave_part = name[i + 1 :]

    if note_part not in _NOTE_TO_SEMITONE:
        raise ValueError(f"Unknown note: {note_part}")
    octave = int(octave_part)
    semitone = _NOTE_TO_SEMITONE[note_part]
    return 12 * (octave + 1) + semitone  # C-1 = 0; C4=60


def transpose_midi(pitch: int, semitones: int) -> int:
    return int(pitch + semitones)


def clamp_int(x: int, lo: int, hi: int) -> int:
    return max(lo, min(hi, x))


def clamp01(x: float) -> float:
    return max(0.0, min(1.0, float(x)))


def safe_mean(xs: SeqT[float]) -> float:
    if not xs:
        return 0.0
    return float(sum(xs)) / float(len(xs))


def pairwise(iterable: Iterable[int]) -> List[Tuple[int, int]]:
    it = list(iterable)
    return list(zip(it, it[1:])) if len(it) >= 2 else []
