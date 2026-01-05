from __future__ import annotations

import struct
from pathlib import Path
from typing import List, Tuple

from .core import Note, clamp_int

TPB_DEFAULT = 480  # ticks per beat


def _vlq(n: int) -> bytes:
    n = int(n)
    if n < 0:
        raise ValueError("VLQ negative")
    out = bytearray()
    out.append(n & 0x7F)
    n >>= 7
    while n:
        out.insert(0, 0x80 | (n & 0x7F))
        n >>= 7
    return bytes(out)


def _mthd(format_type: int, ntrks: int, division: int) -> bytes:
    return b"MThd" + struct.pack(">IHHH", 6, format_type, ntrks, division)


def _meta_tempo(bpm: int) -> bytes:
    bpm = max(1, int(bpm))
    mpqn = int(60_000_000 // bpm)
    data = struct.pack(">I", mpqn)[1:]
    return b"\xFF\x51\x03" + data


def _meta_end_of_track() -> bytes:
    return b"\xFF\x2F\x00"


def write_midi(notes: List[Note], out_path: str | Path, bpm: int = 120, ticks_per_beat: int = TPB_DEFAULT) -> Path:
    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    events: List[Tuple[int, bytes]] = []
    t = 0
    events.append((0, _meta_tempo(bpm)))

    for note in notes:
        pitch = clamp_int(int(note.pitch), 0, 127)
        vel = clamp_int(int(note.velocity), 1, 127)
        ch = clamp_int(int(note.channel), 0, 15)
        dur_ticks = int(round(float(note.duration_beats) * ticks_per_beat))
        dur_ticks = max(1, dur_ticks)

        events.append((t, bytes([0x90 | ch, pitch, vel])))
        events.append((t + dur_ticks, bytes([0x80 | ch, pitch, 0x40])))
        t += dur_ticks

    events.append((t, _meta_end_of_track()))
    events.sort(key=lambda x: x[0])

    track = bytearray()
    last_t = 0
    for abs_t, msg in events:
        delta = abs_t - last_t
        last_t = abs_t
        track += _vlq(delta)
        track += msg

    mtrk = b"MTrk" + struct.pack(">I", len(track)) + bytes(track)
    data = _mthd(format_type=0, ntrks=1, division=int(ticks_per_beat)) + mtrk
    out_path.write_bytes(data)
    return out_path