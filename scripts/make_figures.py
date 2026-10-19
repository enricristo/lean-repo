"""Regenerate every figure in ``figures/``.

Usage, from the repository root::

    python scripts/make_figures.py

The overview numbers are read from the Lean sources, so they stay true when
new results are added.
"""

from __future__ import annotations

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


def main() -> None:
    for name, build in [
        ("00_overview.png", fig_overview),
        ("01_log_bound.png", fig_log_bound),
        ("02_telescoping_cancellation.png", fig_cancellation),
        ("03_telescoping_limit.png", fig_telescoping_limit),
        ("04_pi_p.png", fig_pi_p),
    ]:
        print("wrote", viz.save(build(), FIGURES / name).relative_to(ROOT))


if __name__ == "__main__":
    main()
