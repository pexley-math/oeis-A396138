# Two Lower Bounds on the Polyhex Coloring Sequence

This note derives the two analytical lower bounds used in the solver
for `a(n)` -- the minimum number of cells in a connected polyhex
admitting an `n`-coloring such that every unordered pair of distinct
colors shares at least one cell-cell edge.

We prove

```
L2(n) = n * ceil((n - 1) / 6)                       (per-color)
L1(n) = min { k : 3k - ceil(sqrt(12k - 3)) >= n(n-1)/2 }  (edge)
```

and confirm `a(n) >= max(L1(n), L2(n))` for every `n`. The closed-form
expression for `L1` is verified against direct enumeration of every
fixed polyhex up to size `k = 11` (`research/verify_l1_l2.py`).

The two bounds cover complementary regimes: `L1` dominates for small
`n`, `L2` for large `n`. Together they are tight at every proved
`n != 7`; at `n = 7`, `L1` is short by exactly 1 and SAT closes the
gap to give `a(7) = 12`.

---

## L2 -- per-color cell-count bound

**Claim.** `a(n) >= n * ceil((n - 1) / 6)`.

**Proof.** Fix a valid `n`-coloring `f: P -> {1, ..., n}` of a polyhex
`P` and pick any color `i`. Let `C_i` denote the set of cells colored
`i` and write `c_i = |C_i|`.

Each cell of `P` has at most 6 cell-cell edges (the hex lattice has
degree 6). Therefore the number of cell-cell edges incident to `C_i`
is at most `6 * c_i`.

For the coloring to cover every pair `{i, j}` with `j != i`, each of
the `n - 1` remaining colors must appear at the other end of at least
one such edge. Distinct colors require distinct edges (an edge has
only two endpoints, hence one color pair). So

```
6 * c_i  >=  n - 1
c_i      >=  ceil( (n - 1) / 6 ).
```

Summing over `i = 1, ..., n`:

```
a(n)  =  |P|  =  sum_i c_i  >=  n * ceil( (n - 1) / 6 ).
```

**Tabulated.**

| n  | ceil((n-1)/6) | L2(n) |
|----|---------------|-------|
| 1  | 0             | 0     |
| 2  | 1             | 2     |
| 3  | 1             | 3     |
| 4  | 1             | 4     |
| 5  | 1             | 5     |
| 6  | 1             | 6     |
| 7  | 1             | 7     |
| 8  | 2             | 16    |
| 9  | 2             | 18    |
| 10 | 2             | 20    |
| 13 | 2             | 26    |

`L2` jumps from 7 to 16 between `n = 7` and `n = 8` because the
ceiling jumps from 1 to 2; this is also where `L2` takes over from
`L1` as the dominant bound.

---

## L1 -- hex isoperimetric edge bound

**Claim.** Let `n_pairs = n(n-1)/2`. Then

```
a(n)  >=  L1(n)  :=  min { k : 3k - ceil(sqrt(12k - 3))  >=  n_pairs }.
```

The proof has two parts: (1) any valid coloring needs at least
`n_pairs` interior edges, and (2) the maximum number of interior
edges in any `k`-cell connected polyhex is exactly
`3k - ceil(sqrt(12k - 3))`.

### Step 1. Each color pair needs its own interior edge

For each unordered pair `{i, j}` of distinct colors there must exist
at least one cell-cell edge of `P` with endpoints colored `i` and `j`.
Distinct pairs need distinct edges (one edge supplies one pair). So
the number of interior (cell-cell) edges `I` of `P` satisfies

```
I  >=  binomial(n, 2)  =  n(n - 1) / 2.
```

### Step 2. Maximum interior edges of a k-cell polyhex

Let `I_max(k)` denote the largest possible interior-edge count over
all connected k-cell polyhexes. We claim

```
I_max(k)  =  3k - ceil(sqrt(12k - 3)).
```

**Proof.** Every hex cell has exactly 6 sides. Sum over the `k` cells
of `P`:

```
6k  =  sum over all cells of (sides of that cell).
```

Each side of each cell is either *interior* (shared with an adjacent
cell in `P`, in which case the same lattice edge appears as a side of
two cells) or *boundary* (the adjacent lattice cell is outside `P`,
in which case the lattice edge appears as a side of only one cell).
Writing `I` for the number of interior cell-cell edges and `p` for
the perimeter (number of boundary lattice edges, counted once each):

```
6k  =  2 I  +  p
=>  I  =  ( 6k - p ) / 2.                              (*)
```

To maximize `I`, minimize `p`. The minimum perimeter of a connected
k-cell polyhex is

```
p_min(k)  =  2 * ceil( sqrt(12k - 3) )
```

a hexagonal isoperimetric inequality due to Harary and Harborth
(1976); the closed-form expression `ceil(sqrt(12k - 3))` corresponds
to OEIS **A135711** (half-perimeter / "minimal hex side-length"). The
inequality is attained by the "as round as possible" polyhexes
(nested hexagonal rings starting from a central cell).

Substituting into (*):

```
I_max(k)  =  ( 6k - p_min(k) ) / 2
         =  ( 6k - 2 ceil(sqrt(12k - 3)) ) / 2
         =  3k - ceil( sqrt(12k - 3) ).
```

### Verification by exhaustive enumeration

We checked `I_max(k)` against direct enumeration of every fixed
k-cell polyhex (axial coordinates, anchored at the origin) for
`k = 1, ..., 11`. The enumerator counts and `I_max` values:

| k  | fixed polyhexes | I_max (enumerated) | I_max (formula) | match |
|----|-----------------|---------------------|------------------|-------|
|  1 |       1         |  0                  |  0               | yes   |
|  2 |       3         |  1                  |  1               | yes   |
|  3 |      11         |  3                  |  3               | yes   |
|  4 |      44         |  5                  |  5               | yes   |
|  5 |     186         |  7                  |  7               | yes   |
|  6 |     814         |  9                  |  9               | yes   |
|  7 |    3,652        | 12                  | 12               | yes   |
|  8 |   16,689        | 14                  | 14               | yes   |
|  9 |   77,359        | 16                  | 16               | yes   |
| 10 |  362,671        | 19                  | 19               | yes   |
| 11 | 1,716,033       | 21                  | 21               | yes   |

The fixed-polyhex counts reproduce OEIS **A001207** exactly
(an independent sanity check on the enumerator). At `k = 11` the
enumeration of 1.7 million fixed polyhexes completes in roughly one
minute on a desktop CPU and confirms `I_max(11) = 21` -- which is
exactly `binomial(7, 2)`, the count of colour pairs at `n = 7`.

### Combining the two ingredients

From `I >= n(n-1)/2` and `I <= I_max(k) = 3k - ceil(sqrt(12k - 3))`,
any feasible `k` must satisfy

```
3k - ceil( sqrt(12k - 3) )  >=  n(n - 1)/2.
```

So `a(n) >= L1(n) = min { k : 3k - ceil(sqrt(12k - 3)) >= n(n-1)/2 }`.

---

## Combined bound vs. proved values

`LB(n) = max(L1(n), L2(n))` against the seven proved terms:

| n  | n_pairs | L1(n) | L2(n) | LB(n) | proved a(n) |
|----|---------|-------|-------|-------|-------------|
|  1 |   0     |  1    |  0    |  1    |  1          |
|  2 |   1     |  2    |  2    |  2    |  2          |
|  3 |   3     |  3    |  3    |  3    |  3          |
|  4 |   6     |  5    |  4    |  5    |  5          |
|  5 |  10     |  7    |  5    |  7    |  7          |
|  6 |  15     |  9    |  6    |  9    |  9          |
|  7 |  21     | 11    |  7    | 11    | **12**      |

For `n = 1..6`, `LB(n) = a(n)` exactly; both bounds together fully
account for the value. At `n = 7` the edge bound is tight in the
sense that `I_max(11) = 33 - ceil(sqrt(129)) = 33 - 12 = 21`, which
equals `binomial(7, 2) = 21` exactly; the threshold is first met at
`k = 11`, so `L1(7) = 11`. But every interior edge in an 11-cell
"as round as possible" polyhex would then have to host a distinct
colour pair with zero slack, and SAT shows that no 11-cell polyhex
admits a 7-coloring satisfying this, so `a(7) = 12` instead. This is
the unique boundary case where the structural lower bounds fall
short by exactly 1.

For `n >= 8`, `L2(n) > L1(n)` and the per-color bound dominates. At
`n = 8` the bound is tight: SAT proves `a(8) = 16 = L2(8)` (k=16 is
satisfiable; 24 min wall, May 15 2026). `L2(9) = 18` and `L2(10) = 20`
are lower bounds only; `a(9)` and `a(10)` are not yet proved and are
not claimed here.

---

## Reproducibility

A direct reproduction of every table above is in
`research/verify_l1_l2.py`. It enumerates every fixed `k`-cell
polyhex for `k = 1..11`, counts interior edges by direct adjacency
check, compares against the closed-form `3k - ceil(sqrt(12k - 3))`,
and emits the L1/L2 tables. No formula is trusted; every value is
recomputed from the polyhex set. The `k = 1..11` sweep runs in about
75 seconds.

## References

- Harary, F. and Harborth, H. (1976). *Extremal animals.* Journal of
  Combinatorics, Information & System Sciences 1(1), 1-8.
  (Minimum perimeter of hexagonal polyforms.)
- OEIS A135711 -- Minimum perimeter of a polyhex with `n` cells.
  Closed form `ceil(sqrt(12n - 3))` (half of `p_min`).
- OEIS A001207 -- Number of fixed `n`-celled polyhexes. Used as
  independent sanity check on the enumerator.
- OEIS A278299 -- Square-grid analog of the present sequence
  (Jones and Kagey, 2016).
