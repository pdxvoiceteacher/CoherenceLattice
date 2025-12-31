from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, List, Tuple
import math

# Thresholds (mirror Lean): tau0=1/5, tau1=2/5, tau2=3/5, tau3=4/5
tau0: float = 1.0 / 5.0
tau1: float = 2.0 / 5.0
tau2: float = 3.0 / 5.0
tau3: float = 4.0 / 5.0

Regime = int  # 0..4 for S0..S4

# Adjacency (mirror your updated Lean Regime.lean): ring + neighbors + self
ADJ = {
    0: [4, 0, 1],
    1: [0, 1, 2],
    2: [1, 2, 3],
    3: [2, 3, 4],
    4: [3, 4, 0],
}

@dataclass(frozen=True)
class State:
    E: float  # in [0,1]
    T: float  # in [0,1]

    def __post_init__(self) -> None:
        if not (0.0 <= self.E <= 1.0 and 0.0 <= self.T <= 1.0):
            raise ValueError(f"State out of bounds: E={self.E}, T={self.T}")

@dataclass(frozen=True)
class DeltaSynInput:
    lam: float
    mu: float
    gradH: float
    Es: float

def clamp01(x: float) -> float:
    return max(0.0, min(x, 1.0))

def psi(s: State) -> float:
    return s.E * s.T

def classify(s: State) -> Regime:
    p = psi(s)
    if p < tau0:
        return 0
    if p < tau1:
        return 1
    if p < tau2:
        return 2
    if p < tau3:
        return 3
    return 4

def valid_transition(s1: State, s2: State) -> bool:
    r1 = classify(s1)
    r2 = classify(s2)
    return r2 in ADJ[r1]

# --- ΔSyn core (mirror Lean Basic.lean) ---
# deltaS = -(lam*gradH) - (mu*Es)
def deltaS(p: DeltaSynInput) -> float:
    return -(p.lam * p.gradH) - (p.mu * p.Es)

def drive(p: DeltaSynInput) -> float:
    # drive = -deltaS
    return -deltaS(p)

# --- Caps (mirror Lean Dynamics / DynamicsET) ---
def cap_delta(delta: float, cap: float) -> float:
    # clamp delta to [-cap, +cap]
    return max(-cap, min(delta, cap))

def stepPsi(eta: float, p: DeltaSynInput, s: State) -> State:
    # mirror Lean: deltaPsi = eta * (-deltaS) = eta*drive; cap at tau0/2; clamp psi back to [0,1]
    dpsi = eta * drive(p)
    c = cap_delta(dpsi, tau0 / 2.0)
    psi2 = clamp01(psi(s) + c)
    return State(E=psi2, T=1.0)

def stepET(etaE: float, etaT: float, p: DeltaSynInput, s: State) -> State:
    # mirror Lean: deltaE = etaE*drive, deltaT = etaT*drive; cap each at tau0/4; clamp E,T to [0,1]
    dE = etaE * drive(p)
    dT = etaT * drive(p)
    cE = cap_delta(dE, tau0 / 4.0)
    cT = cap_delta(dT, tau0 / 4.0)
    e2 = clamp01(s.E + cE)
    t2 = clamp01(s.T + cT)
    return State(E=e2, T=t2)

def traj(f: Callable[[State], State], steps: int, s0: State) -> List[State]:
    xs = [s0]
    s = s0
    for _ in range(steps):
        s = f(s)
        xs.append(s)
    return xs

def regime_path(xs: List[State]) -> List[Regime]:
    return [classify(s) for s in xs]

def bounded_drift_stepET(etaE: float, etaT: float, p: DeltaSynInput, s: State) -> float:
    s2 = stepET(etaE, etaT, p, s)
    return abs(psi(s2) - psi(s))