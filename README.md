# OEIS A396138 -- Minimum Polyhex Coloring Such That Every Color Pair Shares an Edge

Solver code, data, and figures for [OEIS A396138](https://oeis.org/A396138).

## The Problem

A *polyhex* is a connected, edge-joined set of unit hexagons. **a(n)** is
the fewest cells in a polyhex admitting a *complete n-coloring*: a
coloring (not necessarily proper -- adjacent cells may share a color) in
which all binomial(n,2) color pairs occur on some cell-cell edge. It is
the hexagonal analog of the square-grid sequence
[A278299](https://oeis.org/A278299) (Jones and Kagey, 2016); the two are
distinct sequences and no numerical relation is asserted.

## Results

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| **a(n)** | **1** | **2** | **3** | **5** | **7** | **9** | **12** | **16** | **18** | **21** |
| **bbox** | 1x1 | 2x1 | 2x2 | 2x4 | 4x4 | 4x4 | 4x4 | 5x4 | 6x5 | 6x6 |

All ten are proved: an explicit witness coloring for each upper bound and
an analytic lower bound for each (with an additional machine-checked LRAT
proof for n <= 7). A live OEIS search on the proved prefix returns no
match -- the sequence is new.

## Method

- **Upper bounds (witnesses).** n <= 7: ascending-k single-formula SAT
  (CaDiCaL) over a connectivity- and symmetry-broken CNF. n = 8, 9, 10:
  a rigidity-constrained witness search -- a rigidity lemma at bounded
  edge slack forces the color-class-size multiset, making the per-shape
  decision terminate.
- **Lower bounds (analytic).** An edge-isoperimetric bound
  L1(n) = min { k : 3k - ceiling(sqrt(12k - 3)) >= binomial(n, 2) }
  (from 6k = 2*interior_edges + perimeter and the polyhex minimum
  perimeter, [A135711](https://oeis.org/A135711)), and a per-color bound
  L2(n) = n * ceiling((n - 1) / 6). max(L1, L2) = a(n) for every proved n
  except n = 7, and is the full lower bound for n = 8 (16), 9 (18),
  10 (21). For n <= 7 the UNSAT at k = a(n) - 1 was additionally
  LRAT-certified (verdicts/sizes in
  `research/drat-certification-summary.json`; the proofs are regenerable
  and not shipped).
- **Verification.** Every witness is checked by three algorithmically
  disjoint verifiers; the n = 10 witness seven disjoint ways, including a
  zero-dependency standalone oracle.

The L1-vs-L1+1 dichotomy (n = 7 exceeds the bound by one; n = 10 is
tight) is an open problem; no conjecture is made.

## Verification (no private libraries needed)

The `code/` scripts are reference-only -- they import a private
shared-library monorepo not published here. Independent verification
needs only the Python standard library:

```bash
python research/n9_solve.py      # cold-certifies the values/witnesses a(1..10)
python research/verify_l1_l2.py  # re-derives the analytic lower bounds (reproduces A001207)
```

## Files

| File | Description |
|------|-------------|
| `code/solve_polyhex.py`, `code/solve_polyhex_ext.py` | SAT solver (single-formula; external-streaming/LRAT variant) |
| `code/verify_method1.py` | Independent geometric verifier (disjoint code path, no SAT) |
| `code/generate-figures.py` | Publication figure generator |
| `research/solver-results.json`, `research/solver-run-log.txt` | Proved values/witnesses/timings; reviewer-grade run log |
| `research/verify_method1-results.json`, `research/verify_method1-run-log.txt` | Geometric verifier output, n = 1..10 |
| `research/n9_solve.py` | Zero-dependency standalone oracle (cold-certifies a(1..10)) |
| `research/verify_l1_l2.py` | Self-contained L1/L2 re-derivation (cross-checked vs A001207) |
| `research/drat-certification-summary.json` | LRAT-certification record, n <= 7 (proof artifacts not shipped) |
| `submission/oeis-a396138-figures.pdf` | Publication figures |
| `README.md`, `LICENSE` | This file; CC-BY-4.0 |

## Prior Art and Acknowledgments

No prior OEIS entry exists for this problem. The square-grid analog
[A278299](https://oeis.org/A278299) (Alec Jones and Peter Kagey, 2016)
motivated the hexagonal version; polyhexes are enumerated by
[A000228](https://oeis.org/A000228) (free) and
[A001207](https://oeis.org/A001207) (fixed), and the edge bound uses
[A135711](https://oeis.org/A135711). Inspired by the
[OEIS](https://oeis.org/) and its contributors.

## Hardware

AMD Ryzen 5 5600 (6-core / 12-thread), 16 GB RAM, Windows 11,
single-threaded.

## License

[CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/) -- Peter Exley, 2026.
Freely available; a citation or acknowledgment is appreciated but not required.

## Links

- **A000228** (free polyhexes with n cells): https://oeis.org/A000228
- **A001207** (fixed polyhexes with n cells; enumerator cross-check): https://oeis.org/A001207
- **A135711** (minimal perimeter of a polyhex with n cells): https://oeis.org/A135711
- **A278299** (square-grid analog, distinct sequence): https://oeis.org/A278299
- **A396138** (this sequence): https://oeis.org/A396138
