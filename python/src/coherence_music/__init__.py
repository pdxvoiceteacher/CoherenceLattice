"""
coherence_music: GUFT/TAF-inspired music engines (research tool).

Design goals:
- Transparent mapping rules (T): auditable, deterministic options, logged motifs.
- Expressive motifs (E): stable semantic hooks for GUFT metrics.
- Lightweight core: no heavy deps required; MIDI writer included.
"""

from .core import Note, Phrase, Sequence
from .taf import taf_theme_notes, taf_cmaj9_pitch_classes
from .raga import bhairav_profile
from .engine import EngineConfig, CoherenceMusicEngine
from .midi import write_midi

__all__ = [
    "Note",
    "Phrase",
    "Sequence",
    "taf_theme_notes",
    "taf_cmaj9_pitch_classes",
    "bhairav_profile",
    "EngineConfig",
    "CoherenceMusicEngine",
    "write_midi",
]