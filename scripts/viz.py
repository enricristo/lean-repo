"""Visual system shared by every figure in this repository.

The same system used across my other repositories:

* white paper, a navy ink for the data and amber only for the one mark that
  carries the point of the figure;
* IBM Plex Sans (bundled in ``scripts/fonts`` under the SIL Open Font
  License, so a figure renders the same on any machine);
* a title that states the finding, a subtitle that says what is plotted, and
  a source line; thin marks, a recessive grid, direct labels instead of
  legends wherever a label fits;
* text always in ink tones, never in the series color.
"""

from __future__ import annotations

from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib import font_manager
from matplotlib.patches import FancyBboxPatch
from matplotlib.transforms import offset_copy

# ── palette ─────────────────────────────────────────────────────────────────
PAPER = "#FFFFFF"
INK = "#141A18"
INK_2 = "#5D6862"
INK_3 = "#8E9791"
RULE = "#D9DED6"
GRID = "#EDF0EA"
TITLE = "#1F4E79"
NAVY = "#24609C"  # data ink
NAVY_LIGHT = "#A9C3DF"
NAVY_WASH = "#EEF3F8"
AMBER = "#C07A1E"  # the one mark that carries the point
AMBER_WASH = "#FBF1E3"
CONTEXT = "#C9CEC8"
TILE = "#F3F6F2"

SOURCE = "Proofs checked by Lean 4 and Mathlib · github.com/enricristo/lean-repo"

# ── typography ──────────────────────────────────────────────────────────────
_FONTS = Path(__file__).resolve().parent / "fonts"
for _f in _FONTS.glob("*.ttf"):
    font_manager.fontManager.addfont(str(_f))
_FAMILY = "IBM Plex Sans" if any(_FONTS.glob("*.ttf")) else "DejaVu Sans"

plt.rcParams.update(
    {
        "figure.facecolor": PAPER,
        "axes.facecolor": PAPER,
        "savefig.facecolor": PAPER,
        "font.family": _FAMILY,
        "font.size": 9.5,
        "mathtext.fontset": "dejavusans",
        "axes.edgecolor": RULE,
        "axes.linewidth": 0.9,
        "axes.labelcolor": INK_2,
        "axes.labelsize": 9,
        "xtick.color": INK_2,
        "ytick.color": INK_2,
        "xtick.labelsize": 8.5,
        "ytick.labelsize": 8.5,
        "xtick.major.size": 0,
        "ytick.major.size": 0,
        "xtick.major.pad": 5,
        "ytick.major.pad": 6,
        "axes.titlesize": 10,
        "axes.titleweight": "semibold",
        "axes.titlecolor": INK,
        "axes.titlelocation": "left",
        "axes.titlepad": 8,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.grid": True,
        "grid.color": GRID,
        "grid.linewidth": 0.8,
        "axes.axisbelow": True,
        "legend.frameon": False,
        "legend.fontsize": 8.5,
        "figure.dpi": 100,
    }
)


def headline(fig, title: str, subtitle: str | None = None, source: str | None = SOURCE, extra_top: float = 0) -> None:
    """Title that states the finding, a subtitle, and a source line.

    Positions are in points from the figure edges and the subplots are moved
    by the same amount, so text and axes never overlap at any figure size.
    """
    top = fig.transFigure
    fig.text(
        0.0, 1.0, title, transform=offset_copy(top, fig, x=2, y=-4, units="points"),
        ha="left", va="top", fontsize=14, fontweight="semibold", color=TITLE,
    )  # fmt: skip
    used = 26
    if subtitle:
        fig.text(
            0.0, 1.0, subtitle, transform=offset_copy(top, fig, x=2, y=-26, units="points"),
            ha="left", va="top", fontsize=10, color=INK_2,
        )  # fmt: skip
        used = 46
    bottom_pts = 0
    if source:
        fig.text(
            0.0, 0.0, source, transform=offset_copy(top, fig, x=2, y=4, units="points"),
            ha="left", va="bottom", fontsize=7.5, color=INK_3,
        )  # fmt: skip
        bottom_pts = 20
    h = fig.get_figheight() * 72
    fig.subplots_adjust(top=1 - (used + 16 + extra_top) / h, bottom=max(fig.subplotpars.bottom, (bottom_pts + 34) / h))


def save(fig, path: Path | str) -> Path:
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(path, dpi=200, bbox_inches="tight", pad_inches=0.28, metadata={"Software": None})
    plt.close(fig)
    return path


def overview(tiles: list[tuple[str, str, str]]):
    """A row of stat tiles: (big number, label, note). The last tile is the one in amber."""
    fig = plt.figure(figsize=(12, 2.5))
    n = len(tiles)
    gap = 0.018
    w = (1 - gap * (n - 1)) / n
    for i, (value, label, note) in enumerate(tiles):
        ax = fig.add_axes([i * (w + gap), 0, w, 1])
        ax.set_axis_off()
        ax.add_patch(
            FancyBboxPatch((0, 0), 1, 1, boxstyle="round,pad=0,rounding_size=0.06", facecolor=TILE,
                           edgecolor="none", transform=ax.transAxes)
        )  # fmt: skip
        ax.text(0.08, 0.66, value, fontsize=30, fontweight="semibold", color=AMBER if i == n - 1 else TITLE,
                transform=ax.transAxes, va="center")  # fmt: skip
        ax.text(0.08, 0.36, label, fontsize=10.5, fontweight="medium", color=INK, transform=ax.transAxes, va="center")
        ax.text(0.08, 0.18, note, fontsize=8.5, color=INK_2, transform=ax.transAxes, va="center")
    return fig
