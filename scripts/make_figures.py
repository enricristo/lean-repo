"""Regenerate every figure in ``figures/``.

Usage, from the repository root::

    python scripts/make_figures.py

The overview numbers are read from the Lean sources, so they stay true when
new results are added.
"""

from __future__ import annotations

import math
import re
from fractions import Fraction
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

import viz
from viz import AMBER, AMBER_WASH, CONTEXT, INK, INK_2, INK_3, NAVY, NAVY_LIGHT, PAPER, TILE

ROOT = Path(__file__).resolve().parent.parent
FIGURES = ROOT / "figures"


# ── numbers read from the Lean sources ──────────────────────────────────────
def lean_stats() -> dict[str, int]:
    files = sorted((ROOT / "Portfolio").rglob("*.lean"))
    text = "\n".join(f.read_text(encoding="utf-8") for f in files)
    code = re.sub(r"/-.*?-/", "", text, flags=re.S)  # drop comments and docstrings
    return {
        "results": len(list((ROOT / "notes").glob("*.md"))),
        "declarations": len(re.findall(r"^(?:noncomputable )?(?:theorem|lemma|def) ", code, flags=re.M)),
        "sorry": len(re.findall(r"\bsorry\b", code)),
    }


# ── 00 · overview banner ────────────────────────────────────────────────────
def fig_overview():
    s = lean_stats()
    return viz.overview(
        [
            (str(s["results"]), "formal results", "each with a note and a figure"),
            (str(s["declarations"]), "definitions and lemmas", "in Portfolio/, built on Mathlib"),
            ("3", "standard axioms", "propext, choice, Quot.sound"),
            (str(s["sorry"]), "sorry", "every step checked by the kernel"),
        ]
    )


# ── 01 · log(1 + x) ─────────────────────────────────────────────────────────
def fig_log_bound():
    x = np.linspace(0, 3, 400)
    log1p = np.log1p(x)
    taylor = x - x**2 / 2

    fig, (ax, bx) = plt.subplots(1, 2, figsize=(12, 4.8))

    ax.fill_between(x, taylor, log1p, color=AMBER_WASH, lw=0)
    ax.plot(x, x, color=CONTEXT, lw=1.4, ls=(0, (4, 3)))
    ax.plot(x, log1p, color=NAVY, lw=2.2, solid_capstyle="round")
    ax.plot(x, taylor, color=AMBER, lw=2.2, solid_capstyle="round")
    ax.text(2.35, 2.48, "x  (upper bound)", color=INK_3, fontsize=9, ha="left")
    ax.text(2.55, np.log1p(2.55) + 0.14, "log(1 + x)", color=INK, fontsize=10, fontweight="medium", ha="center")
    ax.text(1.0, -0.22, "x − x²/2", color=AMBER, fontsize=10, fontweight="semibold", ha="center")
    ax.text(2.62, 0.35, "the gap is\nnever negative", color=INK_2, fontsize=8.5, ha="center", va="center")
    ax.set_xlim(0, 3)
    ax.set_ylim(-1.6, 3.05)
    ax.axhline(0, color=INK_3, lw=0.8)
    ax.set_xlabel("x")
    ax.set_title("Both sides of the inequality", pad=10)

    t = np.linspace(0, 2.2, 300)
    f, df = np.log1p(t) - t + t**2 / 2, t**2 / (1 + t)
    bx.fill_between(t, 0, df, color=AMBER_WASH, lw=0)
    bx.plot(t, df, color=AMBER, lw=2.2, solid_capstyle="round")
    bx.plot(t, f, color=NAVY, lw=2.2, solid_capstyle="round")
    bx.scatter([0], [0], s=42, color=PAPER, edgecolors=NAVY, linewidths=1.6, zorder=4)
    bx.text(0.07, 0.07, "f(0) = 0", color=INK, fontsize=9, fontweight="medium")
    bx.text(1.0, 1.12, "slope  f′(t) = t²/(1 + t) ≥ 0", color=AMBER, fontsize=10, fontweight="semibold",
            ha="center")  # fmt: skip
    bx.text(2.08, 0.98, "f(t)", color=INK, fontsize=10, fontweight="medium", ha="left")
    bx.text(1.5, 0.22, "f starts at 0 and never\ngoes down, so f ≥ 0", color=INK_2, fontsize=8.5, va="center")
    bx.set_xlim(0, 2.2)
    bx.set_ylim(-0.05, 1.7)
    bx.set_xlabel("t")
    bx.set_title("The difference f(t) = log(1 + t) − t + t²/2 and its slope", pad=10)

    viz.headline(fig, "The degree 2 Taylor polynomial never overshoots log(1 + x)",
                 "For x ≥ 0 the parabola x − x²/2 stays below log(1 + x). The proof only needs f(0) = 0 and f′ ≥ 0",
                 extra_top=8)  # fmt: skip
    fig.subplots_adjust(wspace=0.18)
    return fig


# ── 02 · telescoping, the cancellation ──────────────────────────────────────
def fig_cancellation(rows: int = 5):
    """Each term is half a difference g(n) − g(n + 1); neighbouring pieces cancel."""
    fig, ax = plt.subplots(figsize=(12, 4.9))
    ax.set_axis_off()
    col_w = 1.55
    x0 = 2.55

    def g(n: int) -> str:
        return rf"$\frac{{1}}{{{n}\cdot{n + 1}}}$"

    for i, n in enumerate(range(1, rows + 1)):
        y = -i
        ax.text(0.0, y, rf"$\frac{{1}}{{{n}\cdot{n + 1}\cdot{n + 2}}}$", fontsize=15, color=INK, va="center")
        ax.text(1.45, y, r"$= \frac{1}{2}\,($", fontsize=15, color=INK_2, va="center")
        plus_x = x0 + i * col_w
        minus_x = plus_x + col_w
        first, last = n == 1, n == rows
        c_plus = AMBER if first else CONTEXT
        c_minus = AMBER if last else CONTEXT
        for xx, txt, c, sign in ((plus_x, g(n), c_plus, ""), (minus_x, g(n + 1), c_minus, "−")):
            box_fc = AMBER_WASH if c == AMBER else TILE
            ax.add_patch(
                plt.matplotlib.patches.FancyBboxPatch((xx - 0.48, y - 0.36), 0.96, 0.72,
                                                      boxstyle="round,pad=0,rounding_size=0.12", fc=box_fc, ec="none")
            )  # fmt: skip
            ax.text(xx - 0.33, y, sign, fontsize=14, color=INK if c == AMBER else INK_3, va="center", ha="center")
            ax.text(xx + 0.06, y, txt, fontsize=15, color=INK if c == AMBER else INK_3, va="center", ha="center")
        ax.text(minus_x + 0.6, y, ")", fontsize=17, color=INK_2, va="center")
        if not last:
            ax.plot([minus_x, minus_x], [y - 0.4, y - 0.6], color=NAVY, lw=1.6)
            ax.text(minus_x + 0.52, y - 0.5, "cancel", fontsize=8, color=NAVY, va="center")
    end = x0 + rows * col_w + 1.2
    ax.text(end, -(rows - 1) / 2, rf"sum of {rows} terms" "\n" r"$= \frac{1}{2}\left(\frac{1}{2} - \frac{1}{%d\cdot %d}\right)$"
            % (rows + 1, rows + 2), fontsize=13, color=INK, va="center")  # fmt: skip
    ax.text(end, -(rows - 1) / 2 - 0.85, rf"$= {sum(Fraction(1, n * (n + 1) * (n + 2)) for n in range(1, rows + 1))}$",
            fontsize=13, color=AMBER, va="center", fontweight="semibold")  # fmt: skip
    ax.set_xlim(-0.1, end + 3.2)
    ax.set_ylim(-rows + 0.4, 0.6)
    viz.headline(fig, "Every middle piece cancels, only the first and the last survive",
                 "1/(n(n+1)(n+2)) is half of g(n) − g(n+1) with g(n) = 1/(n(n+1)). Grey pieces cancel against the row below")  # fmt: skip
    fig.subplots_adjust(left=0.02, right=0.99)
    return fig


# ── 03 · telescoping, the limit ─────────────────────────────────────────────
def partial_sums(n_max: int) -> list[Fraction]:
    out, s = [], Fraction(0)
    for n in range(1, n_max + 1):
        s += Fraction(1, n * (n + 1) * (n + 2))
        out.append(s)
    return out


def fig_telescoping_limit(n_max: int = 40):
    S = partial_sums(n_max)
    N = np.arange(1, n_max + 1)
    closed = [Fraction(1, 4) - Fraction(1, 2 * (k + 1) * (k + 2)) for k in N]
    assert S == closed, "closed form does not match the exact partial sums"
    s = np.array([float(v) for v in S])
    gap = 0.25 - s

    fig, (ax, bx) = plt.subplots(1, 2, figsize=(12, 4.6))
    ax.axhline(0.25, color=AMBER, lw=2.0)
    ax.text(n_max, 0.2535, "1/4", color=AMBER, fontsize=11, fontweight="semibold", ha="right", va="bottom")
    ax.plot(N, s, color=NAVY_LIGHT, lw=1.0, zorder=2)
    ax.scatter(N, s, s=16, color=NAVY, zorder=3)
    ax.text(4, s[3] - 0.004, f"S₄ = {S[3].numerator}/{S[3].denominator}", fontsize=9, color=INK, va="top")
    ax.set_xlim(0, n_max + 1)
    ax.set_ylim(0.16, 0.262)
    ax.set_xlabel("number of terms N")
    ax.set_title(r"Partial sums $S_N$, computed exactly with fractions", pad=10)

    Nf = np.logspace(0, np.log10(n_max), 200)
    bx.plot(Nf, 1 / (2 * (Nf + 1) * (Nf + 2)), color=AMBER, lw=2.0)
    bx.scatter(N, gap, s=16, color=NAVY, zorder=3)
    bx.set_xscale("log")
    bx.set_yscale("log")
    bx.text(2.2, 1 / (2 * 3.2 * 4.2) * 1.5, "1 / (2(N + 1)(N + 2))", color=AMBER, fontsize=10, fontweight="semibold")
    bx.text(1.08, 6e-4, r"dots: $1/4 - S_N$, exact", color=INK_2, fontsize=9)
    bx.set_xlabel("number of terms N (log scale)")
    bx.set_title("What is still missing, on a log scale", pad=10)
    bx.grid(which="minor", visible=False)
    bx.set_xticks([1, 2, 5, 10, 20, 40], ["1", "2", "5", "10", "20", "40"])
    bx.minorticks_off()

    viz.headline(fig, "The partial sums close in on 1/4",
                 r"The gap $1/4 - S_N$ equals 1/(2(N+1)(N+2)) for every N checked, and it falls like 1/(2N²)",
                 extra_top=8)  # fmt: skip
    fig.subplots_adjust(wspace=0.2)
    return fig


# ── 04 · the integral behind π_p ─────────────────────────────────────────────
def fig_pi_p():
    from scipy.integrate import quad

    def integrand(s, p):
        return (1 - s**p) ** (-1 / p)

    def closed(p):
        return np.pi / (p * np.sin(np.pi / p))

    fig, (ax, bx) = plt.subplots(1, 2, figsize=(12, 4.8))
    s = np.linspace(0, 0.995, 600)
    for p in (1.5, 4.0):
        ax.plot(s, integrand(s, p), color=NAVY_LIGHT, lw=1.4)
    ax.fill_between(s, 0, integrand(s, 2), color=AMBER_WASH, lw=0)
    ax.plot(s, integrand(s, 2), color=AMBER, lw=2.2)
    ax.text(0.45, 0.55, "p = 2: area π/2", color=AMBER, fontsize=10, fontweight="semibold", ha="center")
    ax.text(0.84, 2.95, "p = 1.5", color=INK_2, fontsize=8.5, ha="right")
    ax.text(0.79, 1.85, "p = 2", color=AMBER, fontsize=9, ha="right", fontweight="semibold")
    ax.text(0.99, 1.22, "p = 4", color=INK_2, fontsize=8.5, ha="right")
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 4)
    ax.set_xlabel("s")
    ax.set_title(r"The integrand $(1-s^p)^{-1/p}$ blows up at $s = 1$, the area stays finite", pad=10)

    ps = np.linspace(1.12, 10, 300)
    bx.plot(ps, 2 * closed(ps), color=AMBER, lw=2.2)
    qs = [1.25, 1.5, 2, 3, 4, 6, 8, 10]
    vals = [2 * quad(integrand, 0, 1, args=(q,), limit=200)[0] for q in qs]
    bx.scatter(qs, vals, s=30, color=PAPER, edgecolors=NAVY, linewidths=1.5, zorder=3)
    bx.annotate("π₂ = π", xy=(2, np.pi), xytext=(2.6, 3.9), color=INK, fontsize=10, fontweight="medium",
                arrowprops={"arrowstyle": "-", "color": INK_3, "lw": 0.8})  # fmt: skip
    bx.axhline(2, color=CONTEXT, lw=1, ls=(0, (4, 3)))
    bx.text(9.9, 1.95, "limit 2 as p → ∞", color=INK_3, fontsize=8.5, ha="right", va="top")
    bx.text(4.3, 4.6, r"line: $2\pi\,/\,(p\,\sin(\pi/p))$, proved in Lean", color=AMBER, fontsize=10,
            fontweight="semibold")  # fmt: skip
    bx.text(4.3, 4.25, "circles: numerical quadrature (SciPy)", color=INK_2, fontsize=8.5)
    bx.set_xlim(1, 10.2)
    bx.set_ylim(1.6, 6.0)
    bx.set_xlabel("p")
    bx.set_title(r"$\pi_p$ as p varies", pad=10)

    viz.headline(fig, r"$\pi_p = 2\pi\,/\,(p\,\sin(\pi/p))$ for every p > 1, proved in Lean",
                 r"Left: the integrand behind $\pi_p$ blows up at s = 1 but encloses a finite area. Right: the closed form against quadrature",
                 extra_top=14)  # fmt: skip
    fig.subplots_adjust(wspace=0.18)
    return fig


# ── 05 · time scales ────────────────────────────────────────────────────────
def fig_time_scales():
    c = 1.0
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(12, 4.8))
    t = np.linspace(0, 2, 300)
    ax.plot(t, np.exp(c * t), color=INK, lw=1.6)
    ax.text(1.93, np.exp(1.93) + 0.25, r"$e^t$ on $\mathbb{R}$", color=INK, fontsize=9.5, ha="right")
    for h, col, lab in [(1.0, AMBER, "h = 1"), (0.5, NAVY, "h = 1/2"), (0.25, NAVY_LIGHT, "h = 1/4")]:
        n = np.arange(0, int(round(2 / h)) + 1)
        y = (1 + h * c) ** n
        ax.step(h * n, y, where="post", color=col, lw=1.2, alpha=0.9)
        ax.scatter(h * n, y, s=26 if h == 1.0 else 16, color=col, zorder=3)
        ax.text(h * n[-1] + 0.04, y[-1], lab, color=col if h != 0.25 else INK_2, fontsize=9, va="center")
    ax.set_xlim(0, 2.35)
    ax.set_xlabel("t")
    ax.set_title(r"Hilger exponential $(1+h)^{t/h}$ on $h\mathbb{Z}$ against $e^t$", pad=10)

    Ns = np.array([1, 2, 3, 5, 10, 20, 50, 100, 300, 1000])
    vals = (1 + 1 / Ns) ** Ns
    bx.axhline(np.e, color=INK, lw=1.4)
    bx.text(1000, np.e + 0.012, "e", color=INK, fontsize=11, ha="right", va="bottom")
    bx.plot(Ns, vals, color=NAVY_LIGHT, lw=1.0)
    bx.scatter(Ns, vals, s=22, color=NAVY, zorder=3)
    bx.scatter([1], [2], s=60, color=AMBER, zorder=4)
    bx.text(1.25, 2.0, "h = 1: value 2, not e", color=AMBER, fontsize=10, fontweight="semibold", va="center")
    bx.set_xscale("log")
    bx.set_xticks([1, 10, 100, 1000], ["1", "10", "100", "1000"])
    bx.minorticks_off()
    bx.set_ylim(1.9, 2.8)
    bx.set_xlabel("N = 1/h, number of steps to reach t = 1 (log scale)")
    bx.set_title("Value at t = 1 as the graininess h → 0", pad=10)
    viz.headline(fig, r"On $\mathbb{Z}$ the exponential grows like $2^n$, not $e^n$; it only becomes $e$ as h → 0",
                 r"Solutions of $y^\Delta = y$, $y(0) = 1$ on the time scale $h\mathbb{Z}$. All of it is proved in Lean",
                 extra_top=8)  # fmt: skip
    fig.subplots_adjust(wspace=0.2)
    return fig


# ── 06 · Dirac ──────────────────────────────────────────────────────────────
def fig_dirac():
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(12, 4.6))

    def bump(x, eps):
        """A smooth bump equal to 1 on [-eps/2, eps/2] and 0 outside (-eps, eps)."""
        def g(u):
            return np.where(u > 0, np.exp(-1 / np.where(u > 0, u, 1)), 0.0)

        r = np.abs(x)
        s = (r - eps / 2) / (eps / 2)
        return np.where(r <= eps / 2, 1.0, g(1 - s) / (g(1 - s) + g(s)))

    x = np.linspace(-1.1, 1.1, 2000)
    for eps, col, lw in [(1.0, NAVY_LIGHT, 1.2), (0.5, NAVY, 1.6), (0.2, AMBER, 2.2)]:
        ax.plot(x, bump(x, eps), color=col, lw=lw)
    ax.text(-1.08, 1.1, r"$\varphi_\varepsilon(0) = 1$ for every ε", color=INK, fontsize=9.5)
    ax.text(0.95, 0.12, "ε = 1", color=INK_2, fontsize=9)
    ax.text(0.47, 0.12, "ε = 1/2", color=NAVY, fontsize=9)
    ax.text(0.0, 1.04, "ε = 1/5", color=AMBER, fontsize=9.5, fontweight="semibold", ha="center")
    ax.set_ylim(-0.05, 1.22)
    ax.set_xlabel("x")
    ax.set_title("Test functions concentrating at 0", pad=10)

    r = np.logspace(-4, 0, 200)
    bx.plot(r, 4 * np.sqrt(r), color=NAVY, lw=2.0)
    bx.axhline(1, color=AMBER, lw=2.0)
    bx.text(1.2e-4, 1.08, r"what $\int f\varphi_\varepsilon$ must equal: $\varphi_\varepsilon(0) = 1$", color=AMBER, fontsize=9.5, fontweight="semibold")
    bx.text(1.2e-4, 3.0, r"upper bound $\int_{-\varepsilon}^{\varepsilon}|f|$, here for" "\n" r"$f(x) = |x|^{-1/2}$: $4\sqrt{\varepsilon} \to 0$",
            color=NAVY, fontsize=9)  # fmt: skip
    bx.set_xscale("log")
    bx.minorticks_off()
    bx.set_ylim(0, 4.2)
    bx.set_xlabel("ε (log scale)")
    bx.set_title("The integral is squeezed below 1", pad=10)
    viz.headline(fig, "No function f can satisfy ∫ f φ = φ(0) for every test function",
                 r"The proof in Lean: $\varphi_\varepsilon(0) = 1$ always, but $|\int f\varphi_\varepsilon| \leq \int_{-\varepsilon}^{\varepsilon} |f|$, which tends to 0",
                 extra_top=8)  # fmt: skip
    fig.subplots_adjust(wspace=0.2)
    return fig


# ── 07 · Ekeland ────────────────────────────────────────────────────────────
def ekeland_f(x):
    """A wavy function on the line, bounded below, used to draw the principle."""
    return 1.1 + 0.45 * np.sin(2.2 * x) + 0.05 * (x - 0.6) ** 2


def ekeland_point(x0: float, eps: float, grid: np.ndarray) -> float:
    """A point given by Ekeland's principle: a minimizer of z -> f(z) + eps |z - x0|."""
    return float(grid[np.argmin(ekeland_f(grid) + eps * np.abs(grid - x0))])


def fig_ekeland():
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(12, 4.8), gridspec_kw={"width_ratios": [1.35, 1]})

    x = np.linspace(-3.2, 3.2, 4001)
    x0, eps = 2.6, 0.35
    y = ekeland_point(x0, eps, x)
    fy = float(ekeland_f(y))
    cone = fy - eps * np.abs(x - y)
    ax.fill_between(x, cone, -0.2, color=AMBER_WASH, lw=0)
    ax.plot(x, cone, color=AMBER, lw=1.4, ls=(0, (5, 3)))
    ax.plot(x, ekeland_f(x), color=NAVY, lw=2.2)
    ax.scatter([x0], [ekeland_f(x0)], s=40, color=PAPER, edgecolors=INK, linewidths=1.5, zorder=5)
    ax.scatter([y], [fy], s=70, color=AMBER, zorder=6)
    ax.text(x0 - 0.1, ekeland_f(x0) + 0.03, r"start $x_0$", color=INK, fontsize=9.5, ha="right")
    ax.text(y, 0.28, "Ekeland point y", color=AMBER, fontsize=10, fontweight="semibold", ha="center")
    ax.text(-3.1, -0.12, "cone " r"$z \mapsto f(y) - \varepsilon\,|z - y|$" "\nstays below the graph", color=AMBER,
            fontsize=9)  # fmt: skip
    zmin = float(x[np.argmin(ekeland_f(x))])
    ax.text(zmin, float(ekeland_f(zmin)) - 0.14, "global minimum,\nnot needed", color=INK_3, fontsize=8.5,
            ha="center", va="top")  # fmt: skip
    ax.text(-3.1, 2.02, "f, bounded below", color=NAVY, fontsize=9.5)
    ax.set_ylim(-0.2, 2.3)
    ax.set_xlabel("z")
    ax.set_title("The principle: a point that the cone touches only once", pad=10)

    epss = np.array([0.5, 0.25, 0.1, 0.05, 0.02, 0.01])
    us = np.log(1 / epss)
    t = np.linspace(-0.5, 5.2, 400)
    bx.plot(t, np.exp(-t), color=NAVY, lw=2.0)
    bx.axhline(0, color=CONTEXT, lw=1.0)
    bx.scatter(us, np.exp(-us), s=34, color=AMBER, zorder=4)
    for e, u in zip(epss[[0, 2, 5]], us[[0, 2, 5]]):
        bx.text(u, np.exp(-u) + 0.09, f"ε = {e:g}", color=INK_2, fontsize=8.5, ha="center")
    bx.text(1.3, 1.25, r"$f(x) = e^{-x}$: infimum 0, never attained", color=NAVY, fontsize=9.5)
    bx.text(5.1, 0.42, "almost critical points\n" r"$|f'(u_\varepsilon)| \leq \varepsilon$ run off to $+\infty$",
            color=AMBER, fontsize=9, fontweight="semibold", ha="right")  # fmt: skip
    bx.set_ylim(-0.08, 1.5)
    bx.set_xlabel("x")
    bx.set_title("Without Palais-Smale the minimum can escape", pad=10)
    viz.headline(fig, "Every function bounded below has almost minimizers that are almost critical",
                 r"Ekeland's principle in Lean, and its corollary: $f(u) \leq \inf f + \varepsilon$ with "
                 r"$\|f'(u)\| \leq \varepsilon$. Palais-Smale turns them into a true minimum",
                 extra_top=8)  # fmt: skip
    fig.subplots_adjust(wspace=0.2)
    return fig


# ── 08 · plane coloring ─────────────────────────────────────────────────────
BRICK_COLORS = ["#24609C", "#C07A1E", "#5E8C4A", "#9C4F6B", "#3E9AA6", "#7A64AE", "#B49A2C"]


def brick_of(x: float, y: float) -> tuple[int, int]:
    """The brick (i, j) containing (x, y), exactly as `brickCol` and `brickRow` in Lean."""
    j = math.floor(5 * y / 3)
    return math.floor(5 * x / 4 - 2 * j / 5), j


def fig_plane_coloring():
    from fractions import Fraction as F
    from matplotlib.patches import Circle, Rectangle

    fig, (ax, bx) = plt.subplots(1, 2, figsize=(12, 5.0), gridspec_kw={"width_ratios": [1.45, 1]})
    p = (0.4, 0.3)
    c0 = 0
    for j in range(-4, 5):
        for i in range(-7, 8):
            x, y = 4 * i / 5 + 8 * j / 25, 3 * j / 5
            c = (i + 5 * j) % 7
            same = c == c0
            ax.add_patch(Rectangle((x, y), 0.8, 0.6, facecolor=BRICK_COLORS[c], alpha=0.95 if same else 0.32,
                                   edgecolor=INK if same else PAPER, lw=1.4 if same else 1.0))  # fmt: skip
    ax.add_patch(Circle(p, 1.0, fill=False, ls=(0, (5, 3)), lw=1.6, color=INK))
    ax.scatter([p[0]], [p[1]], s=22, color=INK, zorder=5)
    ax.annotate("", xy=(p[0] + 1, p[1]), xytext=p, arrowprops=dict(arrowstyle="-", color=INK, lw=1.0))
    ax.text(p[0] + 0.5, p[1] + 0.05, "1", color=INK, fontsize=10, ha="center", va="bottom")
    ax.set_xlim(-2.4, 2.4)
    ax.set_ylim(-1.5, 1.5)
    ax.set_aspect("equal")
    ax.grid(False)
    ax.set_xticks([])
    ax.set_yticks([])
    for side in ax.spines.values():
        side.set_visible(False)
    ax.set_title("Bricks 4/5 × 3/5, row shift 2/5, color (i + 5j) mod 7", pad=10)

    cases = [((2, 1), "(2, 1)"), ((-2, -1), "(−2, −1)"), ((-3, 2), "(−3, 2)"), ((3, -2), "(3, −2)")]
    w, h, sh = F(4, 5), F(3, 5), F(2, 5)
    gaps = []
    for (di, dj), _ in cases:
        gx = max(F(0), abs(di + sh * dj) * w - w)
        gy = max(F(0), (abs(dj) - 1) * h)
        gaps.append(gx * gx + gy * gy)
    ys = np.arange(len(cases))
    bx.barh(ys, [float(g) for g in gaps], color=AMBER, height=0.55)
    bx.axvline(1, color=INK, lw=1.4)
    bx.text(1.02, len(cases) - 0.35, "distance² = 1", color=INK, fontsize=9, ha="left")
    for y, g in zip(ys, gaps):
        bx.text(float(g) + 0.02, y, f"{g.numerator}/{g.denominator}", color=INK, fontsize=9.5, va="center")
    bx.set_yticks(ys, [lab for _, lab in cases])
    bx.set_xlim(0, 1.55)
    bx.set_ylim(-0.6, len(cases) - 0.1)
    bx.invert_yaxis()
    bx.set_xlabel("smallest squared distance between the two bricks")
    bx.set_title("Offsets (di, dj) that repeat the color: all too far", pad=10)
    viz.headline(fig, "Seven colors suffice: no two points at distance 1 share a color",
                 "The circle of radius 1 never meets the color of its center. Proved in Lean for the "
                 "openai-math task plane-coloring", extra_top=8)  # fmt: skip
    fig.subplots_adjust(wspace=0.22)
    return fig


def main() -> None:
    for name, build in [
        ("00_overview.png", fig_overview),
        ("01_log_bound.png", fig_log_bound),
        ("02_telescoping_cancellation.png", fig_cancellation),
        ("03_telescoping_limit.png", fig_telescoping_limit),
        ("04_pi_p.png", fig_pi_p),
        ("05_time_scales.png", fig_time_scales),
        ("06_dirac.png", fig_dirac),
        ("07_ekeland.png", fig_ekeland),
        ("08_plane_coloring.png", fig_plane_coloring),
    ]:
        print("wrote", viz.save(build(), FIGURES / name).relative_to(ROOT))


if __name__ == "__main__":
    main()
