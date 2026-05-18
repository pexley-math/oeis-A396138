"""
Independent geometric verifier for the polyhex coloring solver.

Disjoint code path -- no imports from solve_polyhex, no SAT backend, no
shared geometry import (hex neighbours defined inline below). Reads the
solver's claimed witnesses from research/solver-results.json and checks
each one against three independent properties:

  1. cell count equals the reported a(n)
  2. cells form a connected polyhex (independent BFS)
  3. every unordered pair of distinct colours appears at some cell-cell
     edge in the witness coloring

This certifies the SAT side of the proof of a(n). The UNSAT side
(no smaller k admits a valid coloring) is certified by the LRAT
machine-checked proof emitted by /solver-iterate.

Usage:
    python verify_method1.py 7
    python verify_method1.py --n 5 --per-term-timeout 600
    python verify_method1.py 10 --no-timeout
"""

from __future__ import annotations

import json
import os
import sys

sys.stdout.reconfigure(line_buffering=True)

from figure_gen_utils.pipeline_timeouts import VERIFIER_TIMEOUT_S
from figure_gen_utils.versioned_output import save_versioned
from figure_gen_utils.solver_log import STATUS_PROVED
from sat_utils.verifier_base import VerifierBase
from sat_utils.coloring_witness import verify_coloring_witness


# Inline hex axial neighbours -- intentionally NOT imported from
# sat_utils.tilings.polyhex so that a bug in the shared geometry would
# still be caught here. The shared sat_utils.coloring_witness orchestration
# (connectivity + pair-coverage iteration) is geometry-free; we pass our
# own neighbours_fn, preserving disjointness.
_HEX_DIRS = ((1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1))


def _hex_neighbours(cell):
    q, r = cell
    return [(q + dq, r + dr) for dq, dr in _HEX_DIRS]


def _verify_one(n, rec):
    """Returns (status, detail) where status in {'OK', 'FAIL'}."""
    return verify_coloring_witness(n, rec, _hex_neighbours)


class PolyhexColoringVerifier(VerifierBase):
    """Independent witness verifier for the polyhex coloring solver."""

    name = "verify_method1"
    description = ("Polyhex coloring witness verifier (independent geometric "
                   "check: connectivity + pair coverage).")
    default_per_term_timeout = VERIFIER_TIMEOUT_S
    verify_tag = "1"

    def __init__(self):
        super().__init__()
        here = os.path.dirname(os.path.abspath(__file__))
        self._research_dir = os.path.normpath(os.path.join(here, "..", "research"))
        self._results_path = os.path.join(self._research_dir,
                                          "solver-results.json")
        self._results = None

    def _load(self):
        if self._results is None:
            with open(self._results_path, encoding="utf-8") as f:
                self._results = json.load(f)
        return self._results

    @classmethod
    def select_ns(cls, args):
        inst = cls()
        results = inst._load()
        proved = sorted(
            int(k) for k, v in results.items()
            if isinstance(v, dict) and v.get("status") == STATUS_PROVED
        )
        if getattr(args, "n", None):
            return [int(args.n)]
        max_n = getattr(args, "max_n", None) or inst.default_max_n
        return [n for n in proved if n <= max_n]

    def expected(self, n):
        rec = self._load().get(str(n)) or {}
        return rec.get("value")

    def verify_n(self, n):
        rec = self._load().get(str(n)) or {}
        try:
            status, detail = _verify_one(n, rec)
        except Exception as exc:  # pylint: disable=broad-except
            return None, f"verifier exception: {exc}"
        if status == "OK":
            return rec.get("value"), detail
        return None, detail

    def save_artifacts(self, summary, log_text):
        save_versioned(summary, os.path.join(
            self._research_dir, "verify_method1-results.json"))
        save_versioned(log_text, os.path.join(
            self._research_dir, "verify_method1-run-log.txt"))


if __name__ == "__main__":
    sys.exit(PolyhexColoringVerifier.run())
