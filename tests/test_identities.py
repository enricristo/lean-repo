"""Every algebraic step used in the Lean proofs, redone in SymPy.

These tests do not replace the formal proofs. They check the same identities
in an independent system, and they recompute the numbers quoted in the notes.
"""

import re
from fractions import Fraction
from pathlib import Path

import numpy as np
import sympy as sp

ROOT = Path(__file__).resolve().parent.parent
t, x = sp.symbols("t x", nonnegative=True)
n, N = sp.symbols("n N", positive=True, integer=True)


# ── log(1 + x) ≥ x − x²/2 ───────────────────────────────────────────────────
def test_derivative_of_the_gap():
    f = sp.log(1 + t) - t + t**2 / 2
    assert sp.simplify(sp.diff(f, t) - t**2 / (1 + t)) == 0
    assert f.subs(t, 0) == 0


def test_derivative_identity_used_in_lean():
    # hval in hasDerivAt_logGap
    assert sp.simplify(t**2 / (1 + t) - (1 / (1 + t) - 1 + t)) == 0


def test_inequality_numerically():
    xs = np.linspace(0, 50, 200_001)
    assert np.all(np.log1p(xs) - (xs - xs**2 / 2) >= -1e-15)


def test_taylor_polynomial_is_the_degree_2_truncation():
    assert sp.series(sp.log(1 + x), x, 0, 3).removeO() == x - x**2 / 2


# ── Σ 1/(n(n+1)(n+2)) = 1/4 ─────────────────────────────────────────────────
def test_partial_fractions():
    g = lambda k: 1 / (k * (k + 1))  # noqa: E731
    term = 1 / (n * (n + 1) * (n + 2))
    assert sp.simplify(term - sp.Rational(1, 2) * (g(n) - g(n + 1))) == 0


def test_closed_form_of_partial_sums():
    closed = sp.Rational(1, 4) - 1 / (2 * (N + 1) * (N + 2))
    s = sp.summation(1 / (n * (n + 1) * (n + 2)), (n, 1, N))
    assert sp.simplify(s - closed) == 0


def test_inductive_step_used_in_lean():
    # sum_telescopingTerm: S(N + 1) = S(N) + term(N), with Lean's shifted index
    S = lambda k: sp.Rational(1, 4) - 1 / (2 * (k + 1) * (k + 2))  # noqa: E731
    term = 1 / ((N + 1) * (N + 2) * (N + 3))
    assert sp.simplify(S(N + 1) - (S(N) + term)) == 0


def test_limit_and_series_value():
    assert sp.limit(1 / (2 * (N + 1) * (N + 2)), N, sp.oo) == 0
    assert sp.summation(1 / (n * (n + 1) * (n + 2)), (n, 1, sp.oo)) == sp.Rational(1, 4)


def test_numbers_quoted_in_the_figures():
    s, sums = Fraction(0), []
    for k in range(1, 6):
        s += Fraction(1, k * (k + 1) * (k + 2))
        sums.append(s)
    assert sums[3] == Fraction(7, 30)
    assert sums[4] == Fraction(5, 21)


def test_squeeze_bound_used_in_lean():
    # tendsto_correction: 1/(2(N+1)(N+2)) ≤ 1/(N+1)
    assert sp.simplify(1 / (N + 1) - 1 / (2 * (N + 1) * (N + 2)) - (2 * N + 3) / (2 * (N + 1) * (N + 2))) == 0


# ── π_p ─────────────────────────────────────────────────────────────────────
def test_pi_integral_at_two():
    s_ = sp.symbols("s", nonnegative=True)
    assert sp.integrate(1 / sp.sqrt(1 - s_**2), (s_, 0, 1)) == sp.pi / 2
    assert sp.diff(sp.asin(s_), s_) == 1 / sp.sqrt(1 - s_**2)


def test_pi_integral_closed_form_numerically():
    from scipy.integrate import quad

    for p in (1.25, 1.5, 2, 3, 4, 6, 8, 10):
        value, _ = quad(lambda s, p=p: (1 - s**p) ** (-1 / p), 0, 1, limit=200)
        assert abs(value - np.pi / (p * np.sin(np.pi / p))) < 1e-7, p


def test_pi_p_closed_form_and_its_ingredients():
    from scipy.integrate import quad
    from scipy.special import beta, gamma

    for p in (1.25, 1.5, 2, 3, 4, 6, 8, 10):
        a = 1 / p
        # step 1: substitution u = s^p
        lhs, _ = quad(lambda s, p=p: (1 - s**p) ** (-a), 0, 1, limit=200)
        rhs, _ = quad(lambda u, a=a: u ** (a - 1) * (1 - u) ** (-a), 0, 1, limit=200)
        assert abs(lhs - a * rhs) < 1e-7, p
        # step 2: Beta, Gamma and Euler's reflection formula
        assert abs(beta(a, 1 - a) - gamma(a) * gamma(1 - a)) < 1e-9
        assert abs(gamma(a) * gamma(1 - a) - np.pi / np.sin(np.pi * a)) < 1e-9
        # step 3: pi_p
        assert abs(2 * lhs - 2 * np.pi / (p * np.sin(np.pi / p))) < 1e-7, p


def test_pi_p_closed_form_at_two_is_pi():
    p = sp.Integer(2)
    assert sp.simplify(2 * sp.pi / (p * sp.sin(sp.pi / p))) == sp.pi


# ── the repository itself ───────────────────────────────────────────────────
def test_no_sorry_in_the_lean_sources():
    for f in list((ROOT / "Portfolio").rglob("*.lean")) + list((ROOT / "Solutions").rglob("*.lean")):
        code = re.sub(r"/-.*?-/", "", f.read_text(encoding="utf-8"), flags=re.S)
        assert not re.search(r"\bsorry\b", code), f
