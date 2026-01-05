from __future__ import annotations

import random
from dataclasses import dataclass
from typing import Dict, List, Optional

from .core import Phrase, Sequence, clamp01, clamp_int
from .raga import RagaProfile

"""
Aleatoric GUFT metric phrase engine (dependency-light).

Weighted random selection across categories:
- Higher E -> more E motifs
- Higher T -> more T motifs
- Higher PSI -> more PSI motifs (or PSI := E*T if PSI absent)
- Higher ΔS -> more DELTA_S motifs
- Λ crossing threshold -> LAMBDA motifs
"""


@dataclass
class EngineConfig:
    bpm: int = 100
    dur_beats: float = 1.0
    base_weight: float = 1.0

    E_weight_base: float = 1.0
    T_weight_base: float = 1.0
    PSI_weight_base: float = 1.0
    DELTA_S_weight_base: float = 1.0
    E_SYM_weight_base: float = 1.0
    LAMBDA_weight_base: float = 1.0

    # heuristic knobs
    DELTA_S_scale: float = 0.3
    E_SYM_improve_delta: float = 0.05
    E_SYM_worsen_delta: float = -0.05
    LAMBDA_critical_level: float = 0.7

    seed: Optional[int] = 0

    def categories(self) -> List[str]:
        return ["BASE", "E", "T", "PSI", "DELTA_S", "E_SYM", "LAMBDA"]


def _normalize_weights(w: Dict[str, float]) -> Dict[str, float]:
    total = sum(max(0.0, float(v)) for v in w.values())
    if total <= 0:
        return {k: (1.0 if k == "BASE" else 0.0) for k in w.keys()}
    return {k: max(0.0, float(v)) / total for k, v in w.items()}


def _weighted_choice(rng: random.Random, weights: Dict[str, float]) -> str:
    r = rng.random()
    cum = 0.0
    last = "BASE"
    for k, w in weights.items():
        last = k
        cum += float(w)
        if r <= cum:
            return k
    return last


class CoherenceMusicEngine:
    def __init__(self, profile: RagaProfile, config: EngineConfig):
        self.profile = profile
        self.config = config
        self.rng = random.Random(config.seed)

    def _weights_for_step(
        self,
        E: float,
        T: float,
        PSI: float,
        dS: float,
        Esym: float,
        Lam: float,
        prev_Esym: float,
        prev_Lam: float,
    ) -> Dict[str, float]:
        c = self.config
        w: Dict[str, float] = {"BASE": float(c.base_weight)}

        w["E"] = float(c.E_weight_base) * clamp01(E)
        w["T"] = float(c.T_weight_base) * clamp01(T)
        w["PSI"] = float(c.PSI_weight_base) * clamp01(PSI)
        w["DELTA_S"] = float(c.DELTA_S_weight_base) * clamp01(dS * float(c.DELTA_S_scale))

        # Ethical symmetry uses change magnitude
        delta_Esym = Esym - prev_Esym
        if delta_Esym >= float(c.E_SYM_improve_delta) or delta_Esym <= float(c.E_SYM_worsen_delta):
            w["E_SYM"] = float(c.E_SYM_weight_base) * (1.0 + abs(delta_Esym))
        else:
            w["E_SYM"] = float(c.E_SYM_weight_base) * 0.2

        # Lambda spikes on threshold crossing
        if (prev_Lam < float(c.LAMBDA_critical_level)) and (Lam >= float(c.LAMBDA_critical_level)):
            w["LAMBDA"] = float(c.LAMBDA_weight_base) * (1.0 + abs(Lam))
        else:
            w["LAMBDA"] = float(c.LAMBDA_weight_base) * 0.1

        return _normalize_weights(w)

    def generate(self, metrics: Dict[str, List[float]], name: str = "coherence_run") -> Sequence:
        Ets = metrics.get("E", [])
        Tts = metrics.get("T", [])
        dSts = metrics.get("DELTA_S", [])
        Es_ts = metrics.get("E_SYM", [])
        Lts = metrics.get("LAMBDA", [])
        n = min(len(Ets), len(Tts), len(dSts), len(Es_ts), len(Lts))
        if n <= 0:
            raise ValueError("metrics time series must be non-empty and aligned")

        PSIts = metrics.get("PSI", None)
        if PSIts is None or len(PSIts) < n:
            PSIts = [clamp01(float(Ets[i]) * float(Tts[i])) for i in range(n)]

        phrases: List[Phrase] = []
        prev_Esym = float(Es_ts[0])
        prev_Lam = float(Lts[0])

        counts: Dict[str, int] = {k: 0 for k in self.config.categories()}

        for i in range(n):
            E = float(Ets[i])
            T = float(Tts[i])
            PSI = float(PSIts[i])
            dS = float(dSts[i])
            Esym = float(Es_ts[i])
            Lam = float(Lts[i])

            w = self._weights_for_step(E, T, PSI, dS, Esym, Lam, prev_Esym, prev_Lam)
            cat = _weighted_choice(self.rng, w)
            counts[cat] += 1
            label = f"{cat}{counts[cat]}"

            if cat == "BASE":
                tokens = self.rng.choice(self.profile.base_phrases)
                ph = self.profile.phrase_from_tokens(
                    label=label,
                    tokens=tokens,
                    category="BASE",
                    velocity=70,
                    dur_beats=self.config.dur_beats,
                )
            else:
                choices = self.profile.guft_phrases.get(cat, [])
                if not choices:
                    tokens = self.rng.choice(self.profile.base_phrases)
                    ph = self.profile.phrase_from_tokens(label, tokens, category="BASE", velocity=70, dur_beats=self.config.dur_beats)
                else:
                    tokens = self.rng.choice(choices)
                    intensity = {
                        "E": E,
                        "T": T,
                        "PSI": PSI,
                        "DELTA_S": dS,
                        "E_SYM": abs(Esym - prev_Esym),
                        "LAMBDA": Lam,
                    }.get(cat, 0.5)
                    vel = clamp_int(55 + int(70 * clamp01(intensity)), 1, 127)
                    ph = self.profile.phrase_from_tokens(
                        label=label,
                        tokens=tokens,
                        category=cat,
                        velocity=vel,
                        dur_beats=self.config.dur_beats,
                    )

            phrases.append(ph)
            prev_Esym = Esym
            prev_Lam = Lam

        return Sequence(phrases=phrases, bpm=int(self.config.bpm), name=name)