"""Every algebraic step used in the Lean proofs, redone in SymPy.

These tests do not replace the formal proofs. They check the same identities
in an independent system, and they recompute the numbers quoted in the notes.
"""

import math
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


# ── time scales ──────────────────────────────────────────────────────────────
def test_hilger_exponential_solves_the_dynamic_equation():
    h, c = sp.Rational(1, 3), sp.Rational(5, 2)
    y = [sp.Integer(1)]
    for _ in range(10):
        y.append(y[-1] + h * c * y[-1])  # y(t + h) = y(t) + mu(t) y^Delta(t)
    assert all(y[k] == (1 + h * c) ** k for k in range(11))


def test_hilger_exponential_below_exp_and_converges():
    c, t = 1.0, 1.0
    vals = [(1 + c * t / N) ** N for N in (1, 2, 10, 100, 10_000)]
    assert vals[0] == 2.0 and all(v < np.e for v in vals)
    assert all(a < b for a, b in zip(vals, vals[1:]))
    assert abs(vals[-1] - np.e) < 2e-4


# ── Dirac delta ──────────────────────────────────────────────────────────────
def test_dirac_proof_mechanism_on_an_unbounded_locally_integrable_f():
    # f(x) = |x|^(-1/2) is locally integrable but unbounded near 0; the proof only needs
    # that its integral over (-r, r), here 4 sqrt(r), goes to 0.
    from scipy.integrate import quad

    for r in (1.0, 0.1, 0.01):
        val = 2 * quad(lambda x: x ** -0.5, 0, r)[0]
        assert abs(val - 4 * np.sqrt(r)) < 1e-8
    assert 4 * np.sqrt(0.01) < 1


# ── the repository itself ───────────────────────────────────────────────────
def test_no_sorry_in_the_lean_sources():
    for f in list((ROOT / "Portfolio").rglob("*.lean")) + list((ROOT / "Solutions").rglob("*.lean")):
        code = re.sub(r"/-.*?-/", "", f.read_text(encoding="utf-8"), flags=re.S)
        assert not re.search(r"\bsorry\b", code), f


# ── Ekeland's principle ─────────────────────────────────────────────────────
def _wavy(z):
    """The function drawn in figures/07_ekeland.png."""
    return 1.1 + 0.45 * np.sin(2.2 * z) + 0.05 * (z - 0.6) ** 2


def test_ekeland_point_of_the_figure():
    z = np.linspace(-3.2, 3.2, 4001)
    x0, eps = 2.6, 0.35
    i = int(np.argmin(_wavy(z) + eps * np.abs(z - x0)))
    y = z[i]
    # (a) the point does at least as well as the start, cone included
    assert _wavy(y) + eps * abs(x0 - y) <= _wavy(x0)
    # (b) strict minimizer of f + eps |. - y| on the grid
    g = _wavy(z) + eps * np.abs(z - y)
    others = np.delete(g, i)
    assert np.all(others > _wavy(y))
    # the principle moved, but no farther than (f(x0) - inf f) / eps, which follows from (a)
    assert y != x0
    assert eps * abs(x0 - y) <= _wavy(x0) - _wavy(z).min()


def test_almost_critical_points_of_exp_minus_x_escape():
    # inf e^{-x} = 0 is not attained; u_eps = log(1/eps) satisfies both bounds of statement 2
    s = sp.symbols("s", real=True)
    f = sp.exp(-s)
    for eps in [sp.Rational(1, 2), sp.Rational(1, 10), sp.Rational(1, 100)]:
        u = sp.log(1 / eps)
        assert sp.simplify(f.subs(s, u) - eps) == 0          # f(u) = eps <= inf f + eps
        assert sp.simplify(sp.Abs(sp.diff(f, s).subs(s, u)) - eps) == 0  # |f'(u)| = eps
    assert sp.limit(sp.log(1 / s), s, 0, "+") == sp.oo


# ── seven-coloring of the plane ─────────────────────────────────────────────
def _brick(x, y):
    """Brick (i, j) of a point, as `brickCol` / `brickRow` in Lean."""
    j = math.floor(5 * y / 3)
    return math.floor(5 * x / 4 - 2 * j / 5), j


def test_brick_offsets_and_gaps_exactly():
    # offsets within reach of a unit distance that repeat the color, and their squared gaps
    w, h, s = Fraction(4, 5), Fraction(3, 5), Fraction(2, 5)
    same = sorted((di, dj) for di in range(-3, 4) for dj in range(-2, 3) if (di + 5 * dj) % 7 == 0)
    assert same == [(-3, 2), (-2, -1), (0, 0), (2, 1), (3, -2)]
    for di, dj in same:
        if (di, dj) == (0, 0):
            continue
        gx = max(Fraction(0), abs(di + s * dj) * w - w)
        gy = max(Fraction(0), (abs(dj) - 1) * h)
        assert gx * gx + gy * gy in (Fraction(784, 625), Fraction(801, 625))
    assert w * w + h * h == 1  # the brick diagonal


def test_unit_distance_pairs_never_share_a_color():
    rng = np.random.default_rng(0)
    for _ in range(200_000):
        x, y = rng.uniform(-50, 50, 2)
        a = rng.uniform(0, 2 * math.pi)
        i, j = _brick(x, y)
        k, l = _brick(x + math.cos(a), y + math.sin(a))
        assert (i + 5 * j) % 7 != (k + 5 * l) % 7
