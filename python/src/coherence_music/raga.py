from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List

from .core import Note, Phrase, clamp_int

# Minimal svara → semitone offsets relative to tonic (Sa)
_SVARA_TO_SEMI = {
    "S": 0,
    "r~": 1,   # komal re (flat 2)
    "R": 2,
    "g~": 3,
    "G": 4,
    "m": 5,
    "M": 6,
    "P": 7,
    "d~": 8,
    "D": 10,
    "N": 11,
}


def svara_to_midi(token: str, tonic_midi: int = 60) -> int:
    """
    Tokens like '.S', 'S', "S'", '.r~', 'd~', etc.
    '.' = lower octave, "'" = higher octave.
    """
    t = token.strip()
    octave_shift = 0
    if t.startswith("."):
        octave_shift -= 12
        t = t[1:]
    if t.endswith("'"):
        octave_shift += 12
        t = t[:-1]
    if t not in _SVARA_TO_SEMI:
        raise ValueError(f"Unknown svara token: {token}")
    return int(tonic_midi + octave_shift + _SVARA_TO_SEMI[t])


@dataclass(frozen=True)
class RagaProfile:
    name: str
    system: str
    tonic_midi: int = 60
    base_phrases: List[List[str]] = field(default_factory=list)
    guft_phrases: Dict[str, List[List[str]]] = field(default_factory=dict)

    def phrase_from_tokens(
        self,
        label: str,
        tokens: List[str],
        category: str = "BASE",
        velocity: int = 80,
        dur_beats: float = 1.0,
    ) -> Phrase:
        notes = [
            Note(
                pitch=svara_to_midi(tok, tonic_midi=self.tonic_midi),
                duration_beats=float(dur_beats),
                velocity=clamp_int(int(velocity), 1, 127),
            )
            for tok in tokens
        ]
        return Phrase(label=label, notes=notes, category=category)


def bhairav_profile(tonic_midi: int = 60) -> RagaProfile:
    base = [
        [".S", ".r~", ".G", "m", "P"],
        ["P", "d~", "N", "S"],
        ["S", "r~", "G", "m", "P"],
        ["P", "m", "G", "r~", "S"],
    ]
    guft = {
        "E": [["S", "r~", "G", "r~"]],
        "T": [["S", "P", "S'", "P"]],
        "PSI": [["S", "r~", "P", "G"]],
        "DELTA_S": [["S", "r~", "R", "g~"]],
        "E_SYM": [["S", "G", "P", "G"]],
        "LAMBDA": [["r~", "d~", "N", "r~"]],
    }
    return RagaProfile(
        name="Bhairav",
        system="Hindustani",
        tonic_midi=int(tonic_midi),
        base_phrases=base,
        guft_phrases=guft,
    )