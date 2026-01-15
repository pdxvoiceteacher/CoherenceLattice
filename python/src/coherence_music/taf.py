from __future__ import annotations

from typing import Dict, List

from .core import Note, Phrase, midi_from_name

"""
TAF Western melodic theme and harmonic stack.

Appendix TAF gives:
Bar1 (Total): C4–E4–G4–C5
Bar2 (Physical): C3–G3–C4–G3
Bar3 (Informational): E3–B3–E4–B3
Bar4 (Coherence/Agent): G3–D4–G4–D4

And the vertical stack yields Cmaj9 pitch classes: C–E–G–B–D.

"""


def taf_theme_pitch_names() -> Dict[str, List[str]]:
    return {
        "total": ["C4", "E4", "G4", "C5"],
        "physical": ["C3", "G3", "C4", "G3"],
        "informational": ["E3", "B3", "E4", "B3"],
        "coherence": ["G3", "D4", "G4", "D4"],
    }


def taf_theme_notes(velocity: int = 90, dur_beats: float = 1.0) -> List[Phrase]:
    parts = taf_theme_pitch_names()
    out: List[Phrase] = []
    for label, names in parts.items():
        notes = [Note(midi_from_name(n), dur_beats, velocity) for n in names]
        out.append(Phrase(label=f"TAF_{label}", notes=notes, category="TAF"))
    return out


def taf_cmaj9_pitch_classes() -> List[int]:
    """
    Returns unique pitch classes (0..11) for the Cmaj9 stack: C,E,G,B,D.
    """
    pcs = set()
    for n in ["C", "D", "E", "G", "B"]:
        pcs.add({"C": 0, "D": 2, "E": 4, "G": 7, "B": 11}[n])
    return sorted(pcs)
