"""Manim animation of the polyhex complete-coloring sequence.

Single continuous slide (Peter standing preference, 2026-05-07): the
union of every minimal witness across n=1..10 is drawn once as a fixed
hex canvas, sized so all ten solutions fit. For each n the cells flip
color in place to show that n's minimum connected polyhex carrying a
complete n-coloring -- every cell tinted by its color class. No redraws
between n; only color transitions on the same fixed cell objects, so
the viewer watches the problem being built term by term.

Hex geometry comes from the shared figure_gen_utils.manim_grids
helpers (flat-top axial layout, identical orientation to the figures
PDF). The per-n witnesses are NOT nested -- each is an independent
optimal coloring -- so cells outside the current witness fade to the
background grid rather than persisting.

Run:
    manim -ql generate-animation.py PolyhexColoringExplainer --format=gif
"""

import json
import os
import sys

import numpy as np
from manim import (
    Scene, Polygon, VGroup, Text, FadeIn, FadeOut, Write,
    ORIGIN, UP, DOWN, BOLD, WHITE, GREY, GREY_B, GREY_D,
    RED, BLUE, GREEN, YELLOW, PURPLE, ORANGE, TEAL, PINK,
    MAROON, GOLD,
)

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..'))

from figure_gen_utils.manim_grids import hex_vertices
from figure_gen_utils.solver_log import STATUS_PROVED

# One distinct hue per color class 0..9 (this is a coloring sequence --
# n distinct colors is intrinsic to the object, not decoration).
CLASS_COLORS = [RED, BLUE, GREEN, YELLOW, PURPLE,
                ORANGE, TEAL, PINK, MAROON, GOLD]

EMPTY_FILL = GREY
EMPTY_OPACITY = 0.06
CLASS_OPACITY = 0.92
BG_STROKE = GREY_D
TARGET_HALF_WIDTH = 5.6
TARGET_HALF_HEIGHT = 2.7
TRANSITION_TIME = 0.4
HOLD_TIME = 1.0


def _parse_cell(key):
    a, b = key.split(",")
    return (int(a), int(b))


class PolyhexColoringExplainer(Scene):
    """a(1..10): the smallest connected polyhex admitting a complete
    n-coloring (every color pair on a cell-cell edge)."""

    def construct(self):
        title = Text("Polyhex complete coloring",
                     font_size=42, weight=BOLD)
        sub = Text("Smallest connected polyhex whose cells admit an "
                   "n-coloring with every color pair on an edge",
                   font_size=22, color=GREY_B, weight=BOLD)
        sub.next_to(title, DOWN, buff=0.3)
        self.play(Write(title), FadeIn(sub))
        self.wait(1.0)
        self.play(FadeOut(title), FadeOut(sub))

        results_path = os.path.join(
            os.path.dirname(__file__), "..", "research",
            "solver-results.json",
        )
        with open(results_path, encoding="utf-8") as f:
            results = json.load(f)

        ns = sorted(int(k) for k in results
                    if results[k].get("status") == STATUS_PROVED)

        # Per-n coloring: {(q, r): class_int}.
        colorings = {}
        for n in ns:
            rec = results[str(n)]
            colorings[n] = {_parse_cell(k): int(v)
                            for k, v in rec["coloring"].items()}

        focus_cells = set()
        for n in ns:
            focus_cells.update(colorings[n].keys())

        # Raw flat-top vertices at unit circumradius, then a single
        # uniform scale + recentre so every witness fits the viewport.
        raw_verts = {qr: hex_vertices(qr[0], qr[1], R=1.0)
                     for qr in focus_cells}
        xs = [v[0] for vs in raw_verts.values() for v in vs]
        ys = [v[1] for vs in raw_verts.values() for v in vs]
        fcx = (min(xs) + max(xs)) / 2.0
        fcy = (min(ys) + max(ys)) / 2.0
        half_w = (max(xs) - min(xs)) / 2.0 + 0.3
        half_h = (max(ys) - min(ys)) / 2.0 + 0.3
        s = min(TARGET_HALF_WIDTH / half_w, TARGET_HALF_HEIGHT / half_h)

        cell_polys = {}
        for qr, vs in raw_verts.items():
            arr = [np.array([(v[0] - fcx) * s, (v[1] - fcy) * s, 0.0])
                   for v in vs]
            cell_polys[qr] = Polygon(
                *arr, fill_color=EMPTY_FILL, fill_opacity=EMPTY_OPACITY,
                stroke_color=BG_STROKE, stroke_width=1.0)

        all_group = VGroup(*cell_polys.values())
        self.play(FadeIn(all_group), run_time=1.0)
        self.wait(0.4)

        header = Text("a(1) = 1", font_size=44, color=YELLOW, weight=BOLD)
        header.to_edge(UP, buff=0.4)
        legend = Text("Each color used; every color pair meets at an edge",
                      font_size=22, color=GREY_B, weight=BOLD)
        legend.move_to([0, -3.45, 0])
        self.play(Write(header), FadeIn(legend))

        prev = set()
        for i, n in enumerate(ns):
            col = colorings[n]
            cur = set(col.keys())
            anims = []
            for qr in (prev | cur):
                poly = cell_polys[qr]
                if qr in col:
                    anims.append(poly.animate.set_fill(
                        CLASS_COLORS[col[qr] % len(CLASS_COLORS)],
                        opacity=CLASS_OPACITY,
                    ).set_stroke(WHITE, width=1.6))
                else:
                    anims.append(poly.animate.set_fill(
                        EMPTY_FILL, opacity=EMPTY_OPACITY,
                    ).set_stroke(BG_STROKE, width=1.0))

            new_header = Text(f"a({n}) = {results[str(n)]['value']}",
                              font_size=44, color=YELLOW, weight=BOLD)
            new_header.to_edge(UP, buff=0.4)

            if i == 0:
                self.play(*anims, run_time=TRANSITION_TIME)
            else:
                self.play(*anims,
                          header.animate.become(new_header),
                          run_time=TRANSITION_TIME)
            self.wait(HOLD_TIME)
            prev = cur

        self.wait(0.6)
        self.play(FadeOut(header), FadeOut(legend),
                  FadeOut(all_group), run_time=0.6)

        seq = ", ".join(str(results[str(n)]["value"]) for n in ns)
        f1 = Text("a(n) = fewest cells in a connected polyhex with a "
                  "complete n-coloring", font_size=26, weight=BOLD)
        f2 = Text(f"a(1..{ns[-1]}) = {seq}",
                  font_size=28, color=YELLOW, weight=BOLD)
        fg = VGroup(f1, f2).arrange(DOWN, buff=0.5).move_to(ORIGIN)
        self.play(Write(f1))
        self.wait(0.5)
        self.play(Write(f2))
        self.wait(1.5)
        self.play(FadeOut(fg))
