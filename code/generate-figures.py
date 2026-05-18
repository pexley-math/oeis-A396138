"""Generate publication figures (hex grid colorings) for the polyhex
coloring paper. Reads research/solver-results.json and emits a Typst
document via figure_gen_utils.document_builder.DocumentBuilder.

Usage: python generate-figures.py PROJECT_DIR

Outputs:
  submission/oeis-a396138-figures.typ
  research/oeis-a396138-understanding.pdf
"""

from __future__ import annotations

import json
import os
import subprocess
import sys

# Resolve PROJECT_DIR (positional or default to ../ relative to this file)
HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_PROJECT_DIR = os.path.normpath(os.path.join(HERE, ".."))
PROJECT_DIR = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_PROJECT_DIR

# Make the shared library importable
PAPER_PROJECT = os.path.normpath(os.path.join(PROJECT_DIR, ".."))
sys.path.insert(0, PAPER_PROJECT)

from figure_gen_utils.document_builder import DocumentBuilder
from figure_gen_utils.solver_log import STATUS_PROVED


SEQUENCE_NAME = os.path.basename(PROJECT_DIR.rstrip(os.sep))


def _coloring_dict(rec):
    """Convert solver-results.json 'coloring' field to {(q, r): color}."""
    raw = rec.get("coloring") or {}
    out = {}
    for key, c in raw.items():
        q_s, r_s = key.split(",")
        out[(int(q_s), int(r_s))] = int(c)
    return out


def _per_term_method(n, rec):
    """Accurate per-term method label, derived from the canonical
    ``lower_bound_method``. The lower bounds are NOT uniform: n=1 is
    trivial, n=2..7 carry an LRAT-certified SAT lower bound, n=8 is
    SAT (no LRAT certificate shipped), n=9 is the analytic L2 bound,
    and n=10 is the analytic L1 (edge-isoperimetric) bound with a
    rigidity-constrained witness. A blanket "SAT + LRAT" caption would
    misstate n=8..10."""
    m = (rec.get("lower_bound_method") or "").lower()
    witness = "geometric witness verifier"
    if "trivial" in m:
        return f"trivial (single cell); {witness}"
    if "unsat chain" in m:
        if int(n) <= 7:
            return (f"single-formula SAT; LRAT-certified lower bound; "
                    f"{witness}")
        # n=8 is past the single-formula frontier: rigidity-constrained
        # SAT encoder, analytic lower bound (no LRAT certificate).
        return (f"rigidity-constrained SAT encoder; analytic lower "
                f"bound; {witness}")
    if "analytic l2" in m or "l2 =" in m:
        return f"analytic L2 (per-color) lower bound; {witness}"
    if "l1 edge-isoperimetric" in m or "route-f" in m:
        return (f"analytic L1 (edge-isoperimetric) lower bound; "
                f"rigidity-constrained witness; {witness}")
    return f"analytic lower bound; {witness}"


def main():
    results_path = os.path.join(PROJECT_DIR, "research", "solver-results.json")
    with open(results_path, encoding="utf-8") as f:
        results = json.load(f)

    proved = sorted(
        (int(k), v) for k, v in results.items()
        if isinstance(v, dict) and v.get("status") == STATUS_PROVED
    )

    seq_values = ", ".join(str(v["value"]) for _, v in proved)

    doc = DocumentBuilder(
        title="Minimum Polyhex Coloring (every color pair shares an edge)",
        description=(
            "a(n) = minimum cells in a connected polyhex with an "
            "n-coloring such that every pair of distinct colors is "
            "edge-adjacent."
        ),
        sequence_line=f"a(1..{proved[-1][0]}) = {seq_values}",
    )

    for n, rec in proved:
        cells = _coloring_dict(rec)
        if not cells:
            # n=1 trivial: single cell with color 0
            cells = {(0, 0): 0}
        doc.add_hex_figure(
            cells,
            n=n,
            k=rec["value"],
            status=rec.get("status", STATUS_PROVED),
            method=_per_term_method(n, rec),
        )

    out_typ = os.path.join(
        PROJECT_DIR, "submission", f"{SEQUENCE_NAME}-figures.typ",
    )
    doc.generate(out_typ)
    print(f"Wrote {out_typ}")

    # Compile to PDF (publication figures)
    pdf_path = os.path.splitext(out_typ)[0] + ".pdf"
    proc = subprocess.run(
        ["typst", "compile", out_typ, pdf_path],
        capture_output=True, text=True,
    )
    if proc.returncode != 0:
        print("typst compile failed:", proc.stderr[-500:], file=sys.stderr)
        sys.exit(1)
    print(f"Wrote {pdf_path} ({os.path.getsize(pdf_path)} bytes)")

    # Personal understanding diagram: same content as the publication PDF
    # is fine for a spatial single-shape sequence, but place a copy in
    # research/ so the validator finds it. The figures already include
    # full coloring + cell count + method per term, which is the
    # "understanding" view.
    understanding_pdf = os.path.join(
        PROJECT_DIR, "research", f"{SEQUENCE_NAME}-understanding.pdf",
    )
    import shutil
    shutil.copyfile(pdf_path, understanding_pdf)
    print(f"Wrote {understanding_pdf}")


if __name__ == "__main__":
    main()
