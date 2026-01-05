from pathlib import Path

from coherence_music.raga import bhairav_profile, svara_to_midi
from coherence_music.engine import EngineConfig, CoherenceMusicEngine
from coherence_music.taf import taf_cmaj9_pitch_classes, taf_theme_notes
from coherence_music.midi import write_midi


def test_taf_pitch_classes():
    pcs = taf_cmaj9_pitch_classes()
    assert pcs == [0, 2, 4, 7, 11]  # C D E G B


def test_svara_mapping_basic():
    tonic = 60  # C4
    assert svara_to_midi("S", tonic) == 60
    assert svara_to_midi("r~", tonic) == 61
    assert svara_to_midi("G", tonic) == 64
    assert svara_to_midi("P", tonic) == 67
    assert svara_to_midi("S'", tonic) == 72
    assert svara_to_midi(".S", tonic) == 48


def test_engine_determinism_and_midi(tmp_path: Path):
    metrics = {
        "E": [0.1, 0.2, 0.8, 0.2],
        "T": [0.2, 0.2, 0.6, 0.2],
        "DELTA_S": [0.1, 0.1, 0.2, 0.1],
        "E_SYM": [0.4, 0.42, 0.45, 0.44],
        "LAMBDA": [0.2, 0.3, 0.8, 0.2],
    }
    profile = bhairav_profile(tonic_midi=60)
    cfg = EngineConfig(seed=123, bpm=90)
    eng = CoherenceMusicEngine(profile, cfg)
    seq1 = eng.generate(metrics, name="t1")

    eng2 = CoherenceMusicEngine(profile, cfg)
    seq2 = eng2.generate(metrics, name="t2")

    assert [p.label for p in seq1.phrases] == [p.label for p in seq2.phrases]
    assert [p.category for p in seq1.phrases] == [p.category for p in seq2.phrases]

    midi_path = write_midi(seq1.flatten_notes(), tmp_path / "out.mid", bpm=seq1.bpm)
    assert midi_path.exists()
    assert midi_path.stat().st_size > 100  # sanity


def test_taf_demo_midi(tmp_path: Path):
    phrases = taf_theme_notes()
    notes = []
    for p in phrases:
        notes.extend(p.notes)
    midi_path = write_midi(notes, tmp_path / "taf.mid", bpm=96)
    assert midi_path.exists()
