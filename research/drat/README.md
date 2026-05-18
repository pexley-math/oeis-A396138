# Proof certificates (lower bounds)

This directory holds the machine-checkable lower-bound certificates for
the polyhex complete-coloring sequence OEIS A396138,
a(n) = 1, 2, 3, 5, 7, 9, 12, 16, 18, 21 (n = 1..10).

For each n the certified fact is a(n) >= K + 1, established by the
unsatisfiability of a CNF at k = K, where K is the integer in the
filename:

- `n<N>_k<K>.cnf` -- the CNF that is UNSAT iff no connected K-cell
  polyhex admits a complete N-coloring. Its UNSAT proves a(N) >= K + 1.

K is always a(N) - 1, so the UNSAT pins the lower bound exactly at the
proved value. Combined with the explicit N-coloring witness of size
a(N) recorded in `../solver-results.json` (the upper-bound half), this
sandwiches a(N) to its exact value. n = 1 is trivial (a single cell, no
smaller k exists) and carries no CNF.

The directory is named `drat/` by pipeline convention; the proofs are
LRAT, not DRAT.

## What is shipped (CNF only -- proofs are regenerable, not committed)

Only the CNF inputs are shipped. The LRAT proofs are **not** committed:
an LRAT proof is not unique (any LRAT-emitting solver run on the same
CNF yields an equally valid proof of the same UNSAT), the proofs are
large (the n = 7 LRAT alone is 311,997,483 bytes -- see
`../drat-certification-summary.json`), and a reader can regenerate and
check any of them from the shipped `.cnf` in seconds to minutes with
two stock open-source binaries. The CNF is the load-bearing artifact.

| n | a(n) | k (UNSAT) | shipped CNF | LRAT |
|:--:|:--:|:--:|:--:|:--:|
| 2 | 2 | 1 | `n2_k1.cnf` | regenerable |
| 3 | 3 | 2 | `n3_k2.cnf` | regenerable |
| 4 | 5 | 4 | `n4_k4.cnf` | regenerable |
| 5 | 7 | 6 | `n5_k6.cnf` | regenerable |
| 6 | 9 | 8 | `n6_k8.cnf` | regenerable |
| 7 | 12 | 11 | `n7_k11.cnf` | regenerable |

Regenerating a proof does **not** require the project's solver or any
private library -- only the shipped `.cnf` and two open-source binaries.

## Verify any term (regenerate the LRAT, then check it)

Two open-source binaries are needed: `cadical` (any release with LRAT
support, i.e. `--lrat=true`) and `lrat-check`. From this directory, for
the file pair `n<N>_k<K>`:

```
cadical --lrat=true n7_k11.cnf n7_k11.lrat
lrat-check n7_k11.cnf n7_k11.lrat
```

On success `lrat-check` reports `s VERIFIED` (some builds print
`c VERIFIED`): the empty clause is derived, the CNF is refuted, so
a(7) >= 12. The same two commands verify any other term by substituting
its `n<N>_k<K>` stem (e.g. `n6_k8`, giving a(6) >= 9). Approximate
single-term wall times on a desktop CPU:

| n | emit (cadical) | check (lrat-check) |
|:--:|:--:|:--:|
| 2..5 | < 1 s | < 1 s |
| 6 | ~0.1 s | ~0.1 s |
| 7 | ~27 s | ~13 s |

(Timings from the certification run recorded in
`../drat-certification-summary.json`.)

## drat-certification-summary.json

`../drat-certification-summary.json` is the audit record, one entry per
n. Fields:

- `n`, `k_star` (= a(n)), `k_unsat` (= a(n) - 1, the certified UNSAT k);
- `certified` -- true iff `lrat-check` returned the verified verdict on
  the run host;
- `cnf_bytes`, `lrat_bytes` -- sizes of the artifacts on the run host
  (the size anchor; `lrat_bytes` lets a re-runner sanity-check scale,
  noting LRAT is not bit-reproducible across solver versions);
- `emit_seconds`, `check_seconds` -- generation and verification wall
  time;
- `verifier` -- the checker used (`lrat-check`);
- `stage` -- the last completed pipeline stage for that n.

n = 1 records `method: "trivial (n=1, no smaller k)"` and no CNF.

## The witness (upper-bound) side

A lower bound alone does not pin a(n). The matching upper bound for
each n is an explicit connected polyhex with a complete n-coloring,
stored as the `coloring` map in `../solver-results.json`. Any tool that
rebuilds the hexagonal cell-adjacency graph from the listed cells and
checks that

1. the cell set is edge-connected,
2. the coloring uses exactly n colors,
3. every one of the binomial(n, 2) color pairs occurs on some
   cell-cell edge,
4. the cell count equals a(n),

certifies a(n) <= a(n), the upper-bound half of the sandwich. The
project ships three algorithmically disjoint verifiers for this
(breadth-first, union-find, and depth-first connectivity with
independent edge scans) in the repository's `code/` directory, not in
this `drat/` directory; they are not needed for the lower-bound checks
above. The n = 10 witness is additionally re-derived by independent
cube-coordinate arithmetic and by a zero-dependency standalone solver.
The hexagonal lattice convention (axial coordinates, six neighbors) is
specified in the project README and paper.
