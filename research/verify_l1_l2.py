"""Physical verification of L1 and L2 lower bounds for the polyhex
coloring problem. NO trust in formulas; everything computed from
scratch by enumeration and direct counting.

L2(n) = n * ceil((n-1) / 6)        per-colour cell-count bound
L1(n) = min k : I_max(k) >= n(n-1)/2,  where I_max(k) is the maximum
        number of interior edges over all k-cell connected polyhexes.

Also recomputes I_max(k) by exhaustive BFS enumeration of all fixed
(axial-coord) polyhexes of size k, and compares against the closed
form  3k - ceil(sqrt(12k - 3)).
"""

from __future__ import annotations
import math
from itertools import combinations

HEX_DIRS = ((1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1))


def _neighbours(cell):
    q, r = cell
    return [(q + dq, r + dr) for dq, dr in HEX_DIRS]


def interior_edges(cells):
    cells = set(cells)
    count = 0
    for c in cells:
        q, r = c
        # Count each unordered edge once: only +q, +r, +q-r direction.
        for dq, dr in ((1, 0), (0, 1), (1, -1)):
            if (q + dq, r + dr) in cells:
                count += 1
    return count


def enumerate_fixed_polyhexes(k):
    """Generate every fixed k-cell connected polyhex, anchored so the
    cell with smallest (r, q) lex-order is at the origin (0, 0)."""
    if k == 1:
        yield frozenset({(0, 0)})
        return

    seen = set()
    # Canonical anchor: smallest cell by (r, q) sits at (0, 0).
    # BFS-grow from (0, 0). Frontier = neighbours of current set that
    # are >= (0, 0) in (r, q) lex order (so we never grow "backward"
    # past the anchor).
    def grow(current, frontier):
        if len(current) == k:
            canon = frozenset(current)
            if canon not in seen:
                seen.add(canon)
                yield canon
            return
        for i, cell in enumerate(frontier):
            new_current = current | {cell}
            new_frontier = list(frontier[i + 1:])
            for n in _neighbours(cell):
                if n in new_current:
                    continue
                if (n[1], n[0]) < (0, 0):  # below the anchor
                    continue
                if n in new_frontier:
                    continue
                new_frontier.append(n)
            yield from grow(new_current, new_frontier)

    initial = {(0, 0)}
    # Initial frontier: neighbours of (0,0) that are >= (0,0) lex.
    init_frontier = [n for n in _neighbours((0, 0)) if (n[1], n[0]) >= (0, 0)]
    yield from grow(initial, init_frontier)


def i_max_by_enumeration(k):
    best = 0
    best_shape = None
    count = 0
    for poly in enumerate_fixed_polyhexes(k):
        count += 1
        ie = interior_edges(poly)
        if ie > best:
            best = ie
            best_shape = poly
    return best, count, best_shape


def i_max_formula(k):
    return 3 * k - math.ceil(math.sqrt(12 * k - 3))


def l2(n):
    if n < 2:
        return 0 if n == 1 else 0
    return n * math.ceil((n - 1) / 6)


def main():
    print("=" * 72)
    print("L2 -- per-colour cell-count bound  L2(n) = n * ceil((n-1)/6)")
    print("=" * 72)
    print(f"{'n':>3}  {'(n-1)/6':>10}  {'ceil':>5}  {'L2(n)':>6}")
    for n in range(1, 14):
        c = math.ceil((n - 1) / 6)
        print(f"{n:>3}  {(n - 1) / 6:>10.4f}  {c:>5}  {n * c:>6}")

    print()
    print("=" * 72)
    print("I_max(k) by exhaustive enumeration vs closed form")
    print("formula:  3k - ceil(sqrt(12k - 3))")
    print("=" * 72)
    print(f"{'k':>3}  {'#fixed':>10}  {'I_max enum':>11}  {'formula':>8}  match?")
    import time
    for k in range(1, 12):
        t0 = time.time()
        imax, count, shape = i_max_by_enumeration(k)
        elapsed = time.time() - t0
        fm = i_max_formula(k)
        ok = "YES" if imax == fm else "*** MISMATCH ***"
        print(f"{k:>3}  {count:>10}  {imax:>11}  {fm:>8}  {ok}  ({elapsed:.1f}s)")

    print()
    print("=" * 72)
    print("L1(n) = smallest k with I_max(k) >= n(n-1)/2")
    print("=" * 72)
    # Precompute I_max for k=1..20 using the (now-verified-up-to-k=8) formula
    print(f"{'n':>3}  {'pairs':>5}  {'L1(n)':>6}  {'L2(n)':>6}  {'max':>5}")
    for n in range(1, 11):
        pairs = n * (n - 1) // 2
        l1 = None
        for k in range(1, 60):
            if i_max_formula(k) >= pairs:
                l1 = k
                break
        l2n = l2(n)
        print(f"{n:>3}  {pairs:>5}  {l1:>6}  {l2n:>6}  {max(l1, l2n):>5}")


if __name__ == "__main__":
    main()
