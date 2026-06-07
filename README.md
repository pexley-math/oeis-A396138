# Smallest polyhex carrying a complete n-coloring (OEIS A396138)

*Peter Exley, Independent Researcher, Brisbane, Australia. Submitted: May 18 2026.*

How few hexagonal cells must a connected shape have before you can color it
with `n` colors so that every pair of colors meets along some edge? On the
square grid this is a known sequence; here we answer the hexagonal version, and
the answer grows in an uneven way that two simple geometric bounds explain
almost completely -- with one stubborn exception.

## The problem

A polyhex is a connected, edge-to-edge set of unit regular hexagons in the
planar hexagonal lattice; every cell has exactly six edge-neighbors. Color the
cells with `n` colors. The coloring is *complete* if every one of the
`binomial(n,2)` unordered pairs of distinct colors occurs on at least one
cell-cell edge. The coloring need not be proper: two edge-adjacent cells may
share a color. We study

```
a(n) = the minimum number of cells in a connected polyhex
       that admits a complete n-coloring.
```

This is OEIS A396138, the hexagonal-lattice analog of the square-grid sequence
A278299 of Jones and Kagey. The two are different sequences on different
lattices; we assert no numerical relation between them, only the shared problem
statement.

## Definitions

- **Polyhex:** a finite, edge-connected set of unit hexagons on the hexagonal
  lattice. Free polyhexes are counted by A000228, fixed polyhexes by A001207.
- **Interior edge:** an edge shared by two cells of the polyhex. A complete
  `n`-coloring needs at least `binomial(n,2)` interior edges, one for each color
  pair, so dense (edge-rich) shapes are the only candidates at the minimum.
- **Complete n-coloring:** an assignment of `n` colors to the cells in which
  every unordered color pair appears on some interior edge. Not required to be
  proper.
- **min_per(n):** the least number of cells any single color must occupy. A cell
  has six edges, so a color must use at least `ceiling((n-1)/6)` cells to touch
  the other `n-1` colors; thus `min_per(n) = max(1, ceiling((n-1)/6))`.

## The values

**Result.** The first ten terms are

| n    | 1 | 2 | 3 | 4 | 5 | 6 | 7  | 8  | 9  | 10 |
| :--: |:-:|:-:|:-:|:-:|:-:|:-:|:--:|:--:|:--:|:--:|
| a(n) | 1 | 2 | 3 | 5 | 7 | 9 | 12 | 16 | 18 | 21 |

Each value is proved: an explicit minimal polyhex and complete coloring give
the upper bound, and a matching lower bound (below) shows no smaller polyhex can
work. The minimal shapes are compact, near-round polyhexes; as `n` grows the
witness adds a thin outer layer of cells to supply the extra color pairs. The
shapes themselves are collected in the figure gallery
[`figures.pdf`](figures.pdf).

## How we know

Two lower bounds, both proved and both holding for every connected polyhex, do
most of the work. Writing `k` for the cell count:

```
L1(n) = min { k : 3*k - ceiling(sqrt(12*k - 3)) >= binomial(n,2) }   (edge bound)
L2(n) = n * ceiling((n-1)/6)                                          (per-color bound)
```

`L1` is an edge-isoperimetric bound: a connected `k`-cell polyhex has at most
`3*k - ceiling(sqrt(12*k - 3))` interior edges, and a complete `n`-coloring
needs at least `binomial(n,2)` of them. `L2` is the per-color count above. Both
are necessary, so `a(n) >= max(L1(n), L2(n))` always.

For every `n` in the proved range except `n = 7`, that maximum is exactly `a(n)`:
we exhibit a polyhex of size `max(L1(n), L2(n))` carrying a complete coloring, so
the bound is tight. `L1` binds for small `n` and at `n = 10`; `L2` binds at
`n = 8` and `n = 9`. This change of which bound is active is why the values rise
unevenly.

The exception is `n = 7`, where `max(L1(7), L2(7)) = 11` but `a(7) = 12`. To
prove `a(7) >= 12` we enumerate the complete family of candidate 11-cell
polyhexes -- every shape dense enough to possibly carry a complete 7-coloring --
and show, exhaustively, that none admits one. The enumeration is certified
complete by an independent recount, so the impossibility is not a sampling
artifact.

Every minimal coloring we report was confirmed two independent ways: a breadth-
first connectivity-and-pair check and a disjoint union-find-and-edge-scan check,
which must agree before a witness is accepted; a separate, independently written
geometric verifier re-checks each one from the stored shape. The methods we used
are a constraint solver for the per-shape coloring decisions and exhaustive
geometric enumeration for the completeness arguments; the results do not depend
on any single program.

## Patterns and open questions

The first differences are `1, 1, 2, 2, 2, 3, 4, 2, 3` -- not monotone, with a
conspicuous `4` at `n = 7` (the exceptional term) followed by a drop to `2` as
the per-color bound takes over at `n = 8, 9`. No low-degree polynomial and no
short linear recurrence fits the ten terms.

This suggests a single clean description with one caveat:

> **Conjecture (UNVERIFIED).** For all `n` other than `n = 7`,
> `a(n) = max(L1(n), L2(n))`.

The two bounds are proved, so this is the claim that the maximum is *tight* for
every `n` past the lone exception. It holds across `n = 1..10`. We do not know
whether `n = 7` is the only exceptional term; the square-grid analog A278299 has
its own irregularities, so further exceptions would not be surprising.

The frontier is `a(11)`. Here `max(L1(11), L2(11)) = max(24, 22) = 24`, so
`a(11) >= 24` is already proved by the edge bound, and the conjecture predicts
`a(11) = 24`. We did not settle it within our per-term computation budget: at
`k = 24` the edge bound forces the candidate family to consist only of
maximally compact 24-cell polyhexes, and enumerating that family proved too
large to finish in the allotted time. Establishing `a(11) = 24` therefore awaits
either a single colorable 24-cell witness (which, with the tight bound, would
prove the value outright) or a faster completeness argument.

## Further reading

This work was inspired by the OEIS and the community of contributors who
maintain it.

- Jones, A. and Kagey, P. (2016). "A278299: Tile count of the smallest
  polyomino with an n-coloring such that every color is adjacent to every other
  distinct color at least once." https://oeis.org/A278299
- "A000228: Number of hexagonal polyominoes (or polyhexes) with n cells."
  https://oeis.org/A000228
- "A001207: Number of fixed hexagonal polyominoes with n cells."
  https://oeis.org/A001207

## License

[CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/) -- see `LICENSE`. This work is freely available; a citation or acknowledgment is appreciated but not required.
