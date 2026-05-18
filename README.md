# OEIS A396138 -- Minimum Polyhex Coloring Such That Every Color Pair Shares an Edge

Solver code, data, and figures for [OEIS A396138](https://oeis.org/A396138):
the minimum number of cells in a connected polyhex that admits a complete
n-coloring.

## The Problem

A *polyhex* is a connected, edge-joined set of unit regular hexagons on
the planar hexagonal lattice (every cell has six edge-neighbors).
**a(n)** is the fewest cells in such a polyhex that admits a *complete
n-coloring*: an assignment of n colors to the cells in which every one
of the binomial(n,2) unordered color pairs appears on at least one
cell-cell edge. The coloring need not be proper, so two edge-adjacent
cells may share a color. This is the hexagonal-lattice analog of the
square-grid sequence [A278299](https://oeis.org/A278299) (Jones and
Kagey, 2016); the two are distinct sequences and no numerical relation
between them is asserted.

## Results

**New proved terms (this work):**

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| **a(n)** | **1** | **2** | **3** | **5** | **7** | **9** | **12** | **16** | **18** | **21** |
| **Witness bbox** | 1x1 | 2x1 | 2x2 | 2x4 | 4x4 | 4x4 | 4x4 | 5x4 | 6x5 | 6x6 |
| **Time (s)** | 0.3 | 0.0 | 0.0 | 0.0 | 0.1 | 0.8 | 504.8 | 1420.7 | 53.3 | 9.0 |

Each upper bound is an explicit witness coloring; each lower bound is
analytic (an edge-isoperimetric bound and a per-color contact bound),
with n = 7 additionally carrying a machine-checked LRAT proof that no
11-cell polyhex admits a complete 7-coloring. Every witness is
independently checked by three algorithmically disjoint verifiers; the
n = 10 witness is checked seven disjoint ways. A live OEIS search on
the proved 10-term prefix and its standard transformations returns no
match: the sequence is new.

## Method

Exact values via Boolean satisfiability for small n, analytic lower
bounds throughout, and a rigidity-constrained search for the larger
terms.

- **SAT (n <= 7):** for each n, ascend k = LB(n), LB(n)+1, ... building
  a CNF that is satisfiable iff some connected k-cell polyhex admits a
  complete n-coloring (per-cell activity/color variables,
  Plaisted-Greenbaum pair-coverage, breadth-first-search reachability
  for connectivity, reflection lex-leader plus spatial-anchor symmetry
  breaking, Sinz sequential-counter cardinality). The first satisfiable
  k is a(n).
- **Analytic lower bounds:** an edge-isoperimetric bound
  L1(n) = min { k : 3k - ceiling(sqrt(12k - 3)) >= binomial(n, 2) },
  proved from the exact identity 6k = 2*(interior edges) + perimeter
  plus the closed-form minimum perimeter of a polyhex
  ([A135711](https://oeis.org/A135711)); and a per-color contact bound
  L2(n) = n * ceiling((n - 1) / 6). max(L1(n), L2(n)) = a(n) for every
  proved n except n = 7, so the analytic bounds alone supply the full
  lower bound for n = 8 (L2 = 16), n = 9 (L2 = 18) and n = 10 (L1 = 21)
  -- no SAT certificate is needed for these terms. Both bounds are
  independently re-derived and checked by `research/verify_l1_l2.py`,
  a self-contained reproducer (it enumerates the relevant polyhexes
  and reproduces [A001207](https://oeis.org/A001207)); it is the
  in-repo verification of every lower bound.
- **Lower-bound certificates (n <= 7):** for the SAT-bound terms the
  unsatisfiable instance at k = a(n) - 1 was additionally machine-
  certified by an external LRAT proof; the per-n verdicts, sizes and
  timings are recorded in `research/drat-certification-summary.json`.
  The CNF/LRAT proof artifacts themselves are not shipped (regenerable;
  the n = 7 LRAT alone is ~312 MB). n >= 8 lower bounds are analytic
  (previous bullet), not SAT, by design.
- **Rigidity-constrained witness search (n = 8, 9, 10):** with the
  lower bound already fixed analytically, a rigidity lemma at bounded
  edge slack forces the color-class-size multiset and yields a
  constrained encoder that makes the per-shape decision terminate,
  supplying the matching witness (upper bound); decisive shapes are
  streamed by a span-and-edge-pruned Redelmeier-style enumerator,
  complete by construction and cross-checked by a second, disjoint
  canonical enumerator and an independent fixed-by-edge count
  certificate.
- **Independent verification:** three disjoint verifiers (V1
  breadth-first-search connectivity + pair iteration; V2 union-find +
  independent edge scan; V3 depth-first-search + combined degree/pair
  pass). The n = 10 witness is additionally re-derived by independent
  cube-coordinate arithmetic and by a zero-dependency standalone
  solver.

## Key Findings

- The analytic bound max(L1(n), L2(n)) equals a(n) for every proved
  n except n = 7, where a(7) = 12 exceeds it by exactly one. n = 7 is
  the unique non-tight term in the proved range.
- A **rigidity lemma**: at bounded edge slack a complete n-coloring has
  a forced color-class-size multiset, and at zero slack the coloring is
  forced proper with class quotient exactly K_n. For n = 10, k = 21 this
  forces the class multiset [2^9, 3] (nine colors used twice, one three
  times) -- exactly the structure of the 21-cell witness.
- The lemma yields a solver-free necessary-condition filter that
  re-proves a(7) = 12 with zero solver calls and decides roughly
  three-quarters of the decisive 21-cell family without a SAT call.
- **Open problem (no conjecture made).** It is open for which n the
  edge bound is tight, i.e. a(n) = L1(n) versus a(n) = L1(n) + 1. Both
  n = 7 (bumped) and n = 10 (tight) are edge-binding; one anomaly is
  not a law, so this is recorded as an open problem, not a conjecture.

## Running the Solver

> **Note.** The scripts in `code/` are not runnable as-is from this
> repository alone. They import from a private shared-library monorepo
> that is not published here, and their `sys.path` insertions assume
> the monorepo layout. The code is shipped as a reference for the
> method and for diff-style audit against the canonical results in
> `research/`. Independent verification does not need the private
> libraries or any solver run: `research/n9_solve.py` is a
> zero-dependency (Python standard library only) oracle that
> cold-certifies a(1..10), and `research/verify_l1_l2.py` independently
> re-derives the analytic lower bounds. The external LRAT certification
> of the n <= 7 lower bounds is recorded in
> `research/drat-certification-summary.json`; the CNF/LRAT proof
> artifacts are not shipped (regenerable; the n = 7 LRAT alone is
> ~312 MB).

**Requirements:** Python 3.12+ for the two self-contained verification
scripts below (standard library only -- no third-party packages). The
`code/` solver scripts additionally require the private shared-library
monorepo and are reference-only.

```bash
# Independent verification from this repo alone (no private libraries):
# 1. cold-certify the values/witnesses a(1..10)
python research/n9_solve.py
# 2. re-derive the analytic lower bounds (reproduces A001207)
python research/verify_l1_l2.py

# Example solver commands (require the private monorepo):
python code/solve_polyhex.py --n 1-7
python code/verify_method1.py 10
```

## Files

| File | Description |
|------|-------------|
| `code/solve_polyhex.py` | Primary single-formula SAT solver (n <= 7) |
| `code/solve_polyhex_ext.py` | External-solver streaming variant (LRAT, OS-level timeout) |
| `code/verify_method1.py` | Independent geometric verifier (disjoint code path, no SAT) |
| `code/generate-figures.py` | Publication figure generator |
| `research/solver-results.json` | Machine-readable results: witnesses, colorings, timings |
| `research/solver-run-log.txt` | Reviewer-grade run log (rendered from solver-results.json) |
| `research/verify_method1-results.json` | Independent geometric verifier results, n = 1..10 |
| `research/verify_method1-run-log.txt` | Independent geometric verifier run log |
| `research/n9_solve.py` | Zero-dependency standalone solver/verifier (independent oracle, cold-certifies a(1..10)) |
| `research/verify_l1_l2.py` | Self-contained re-derivation of the L1/L2 lower bounds, cross-checked against A001207 |
| `research/drat-certification-summary.json` | External LRAT-certification audit record for the n <= 7 lower bounds (per-n verdicts/sizes/timings; the CNF and LRAT proof artifacts are not shipped) |
| `submission/oeis-a396138-figures.pdf` | Publication figures |
| `README.md` | This file |
| `LICENSE` | CC-BY-4.0 |

## Prior Art and Acknowledgments

This is a new sequence -- no prior OEIS entry exists for the minimum
polyhex admitting a complete n-coloring. The square-grid analog is
[A278299](https://oeis.org/A278299), submitted by Alec Jones and Peter
Kagey (2016), whose problem statement motivated the hexagonal version
studied here. Polyhexes are enumerated by
[A000228](https://oeis.org/A000228) (free) and
[A001207](https://oeis.org/A001207) (fixed); the edge-isoperimetric
bound uses the minimum-perimeter relation
[A135711](https://oeis.org/A135711). Methodologically this work follows
the SAT-with-checkable-proof tradition in computational combinatorics.
This work was inspired by the [OEIS](https://oeis.org/) and the
community of contributors who maintain it.

## Hardware

AMD Ryzen 5 5600 (6-core / 12-thread), 16 GB RAM, Windows 11,
single-threaded.

## License

[CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/) -- Peter Exley, 2026.

This work is freely available. If you find it useful, a citation or acknowledgment is appreciated but not required.

## Links

- **A000228** (free polyhexes with n cells): https://oeis.org/A000228
- **A001207** (fixed polyhexes with n cells; enumerator cross-check): https://oeis.org/A001207
- **A135711** (minimal perimeter of a polyhex with n cells): https://oeis.org/A135711
- **A278299** (square-grid analog, distinct sequence): https://oeis.org/A278299
- **A396138** (this sequence): https://oeis.org/A396138
