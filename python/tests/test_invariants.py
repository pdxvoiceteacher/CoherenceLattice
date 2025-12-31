from __future__ import annotations

from hypothesis import given, strategies as st

from coherence_sim import State, DeltaSynInput, psi, tau0, stepET, stepPsi, valid_transition, deltaS

float01 = st.floats(min_value=0.0, max_value=1.0, allow_nan=False, allow_infinity=False)
floatpos = st.floats(min_value=0.0, max_value=10.0, allow_nan=False, allow_infinity=False)
floatany = st.floats(min_value=-10.0, max_value=10.0, allow_nan=False, allow_infinity=False)

@given(E=float01, T=float01)
def test_state_bounds(E: float, T: float) -> None:
    s = State(E=E, T=T)
    assert 0.0 <= s.E <= 1.0
    assert 0.0 <= s.T <= 1.0
    assert 0.0 <= psi(s) <= 1.0

@given(
    E=float01, T=float01,
    lam=floatany, mu=floatany, gradH=floatany, Es=floatany,
    etaE=floatany, etaT=floatany
)
def test_stepET_invariants(E, T, lam, mu, gradH, Es, etaE, etaT) -> None:
    s = State(E=E, T=T)
    p = DeltaSynInput(lam=lam, mu=mu, gradH=gradH, Es=Es)
    s2 = stepET(etaE, etaT, p, s)

    # bounds
    assert 0.0 <= s2.E <= 1.0
    assert 0.0 <= s2.T <= 1.0
    assert 0.0 <= psi(s2) <= 1.0

    # bounded drift (theorem says <= tau0/2; allow tiny fp slack)
    assert abs(psi(s2) - psi(s)) <= (tau0 / 2.0) + 1e-12

    # no-teleport (should always be valid under our construction)
    assert valid_transition(s, s2)

@given(
    E=float01, T=float01,
    lam=floatpos, mu=floatpos, gradH=floatpos, Es=floatpos,
    eta=floatpos
)
def test_stepPsi_safe(E, T, lam, mu, gradH, Es, eta) -> None:
    s = State(E=E, T=T)
    p = DeltaSynInput(lam=lam, mu=mu, gradH=gradH, Es=Es)
    s2 = stepPsi(eta, p, s)

    assert 0.0 <= s2.E <= 1.0
    assert 0.0 <= s2.T <= 1.0
    assert abs(psi(s2) - psi(s)) <= tau0 + 1e-12  # stepPsi caps at tau0/2 but this is looser
    assert valid_transition(s, s2)

@given(
    E=float01, T=float01,
    lam=floatpos, mu=floatpos, gradH=floatpos, Es=floatpos,
    etaE=floatpos, etaT=floatpos
)
def test_interpretation_nondec_when_deltaS_neg(E, T, lam, mu, gradH, Es, etaE, etaT) -> None:
    # With all positive inputs, deltaS = -(lam*gradH) - (mu*Es) is strictly negative unless gradH=Es=0
    s = State(E=E, T=T)
    p = DeltaSynInput(lam=lam, mu=mu, gradH=gradH, Es=Es)

    if not (deltaS(p) < 0.0):
        return

    s2 = stepET(etaE, etaT, p, s)
    assert psi(s2) + 1e-12 >= psi(s)