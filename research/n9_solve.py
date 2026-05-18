"""Standalone pure-Python a(9) solver + verifier for oeis-a396138.

ZERO third-party dependencies (Python 3 stdlib only). No pysat, no numpy, no
sat_utils, no Cython. Safe to run cold in an ephemeral container. (PySAT is
used as an OPTIONAL fast colourer if importable; the pure-Python exact
backtracking colourer is the always-available equivalent.)

Problem: a(n) = min cells in a connected polyhex with an n-colouring where
every unordered pair of distinct colours shares a cell-cell edge. n=1..8 are
PROVED (1,2,3,5,7,9,12,16) in research/solver-results.json. a(9) is open.

a(9) >= 18 is ANALYTIC: L2(9) = 9*ceil(8/6) = 18 (see research/lower-bounds.md,
re-derived cold by research/verify_l1_l2.py). This driver settles a(9)
DECISIVELY, not just by witness-rubber-stamp:

  * For each k = 18, 19, 20, ... it enumerates the COMPLETE finite family
    F_k = {free k-cell polyhexes with >= 36 interior edges} and SAT/BT-colours
    every member with 9 colours, each colour used >= 2 times (L2 necessity),
    all C(9,2)=36 pairs edge-adjacent.
  * Key lemma (proved in research/lower-bounds.md and the certificate): ANY
    k-cell witness needs 36 DISTINCT bichromatic interior edges (one edge
    carries exactly one colour-pair label), and bichromatic edges are a
    subset of interior edges, so a witness shape has >= 36 interior edges --
    for EVERY k. Hence F_k is the decisive family at each k.
  * First k with a SAT member  ==>  a(9) = k  (upper bound by explicit
    double-verified witness; lower bound a(9) >= k from F_18..F_{k-1} all
    complete-and-UNSAT, the floor being the analytic L2 for k=18).
  * The enumerator is COMPLETE BY CONSTRUCTION: Redelmeier visits every
    fixed k-polyhex exactly once; a subtree is pruned only when the SOUND
    bound  min(I_max(k), e_partial + 6*(k - m)) < 36  proves no completion
    can reach 36 interior edges. No bounding-box parameter, no empirical
    "re-run larger and hope the count is stable" -- completeness is a
    theorem about the search, not an observation.

Two algorithmically disjoint search methods + two disjoint verifiers:
  M1  exact colourer (PySAT-Cadical195 if available, else pure-Python
      backtracking) over the complete F_k family (deterministic, complete)
  M2  simulated annealing over (shape (+) colouring) jointly (stochastic,
      corroboration only -- never load-bearing)
  V1  orchestration-style verifier (BFS connectivity + pair iteration)
  V2  from-scratch verifier (union-find connectivity + independent pair scan)

Outputs (NEVER touches research/solver-results.json):
  research/solver-n9-results.json   research/n9-certificate.md
  research/n9-runbook-log.txt

License: CC-BY-4.0
"""
from __future__ import annotations

import argparse
import json
import math
import os
import random
import signal
import sys
import time
from collections import deque

sys.stdout.reconfigure(line_buffering=True)

# Canonical solver-status constants. Imported from the shared library when
# available; the except-branch is the sanctioned compat fallback (keeps
# this driver ZERO-dependency for the cold ephemeral container, where the
# shared lib is absent). The `STATUS_* = "..."` fallback lines are the
# pattern tools/audit_status_literals.py explicitly exempts.
try:
    from figure_gen_utils.solver_log import (        # noqa: F401
        STATUS_PROVED, STATUS_TIMEOUT, STATUS_NO_SOLUTION,
        STATUS_VERIFY_FAILED, STATUS_ERROR, STATUS_MATCHED, STATUS_FOUND)
except ImportError:                                   # standalone / cold
    STATUS_PROVED = "PROVED"                          # fallback
    STATUS_TIMEOUT = "TIMEOUT"                        # fallback
    STATUS_NO_SOLUTION = "NO_SOLUTION"                # fallback
    STATUS_VERIFY_FAILED = "VERIFY_FAILED"            # fallback
    STATUS_ERROR = "ERROR"                            # fallback
    STATUS_MATCHED = "MATCHED (prior authors)"        # fallback
    STATUS_FOUND = "FOUND (upper bound)"              # fallback

# Hex axial adjacency. IDENTICAL to tilings/polyhex.py, coloring_witness.py,
# verify_method1.py, verify_l1_l2.py. The adjacency relation is part of the
# PROBLEM STATEMENT, not an implementation choice, so a witness found here
# also passes the project's code/verify_method1.py.
HEX_DIRS = ((1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1))

_HERE = os.path.dirname(os.path.abspath(__file__))

NCOL = 9                       # number of colours for a(9)
NEED_PAIRS = NCOL * (NCOL - 1) // 2          # 36 colour pairs to cover
# A witness needs >= 36 DISTINCT bichromatic interior edges (one edge carries
# exactly one unordered colour-pair label), and bichromatic edges are a
# subset of all interior edges, so a witness SHAPE has >= 36 interior edges
# regardless of k. This is the single, k-independent edge floor.
EDGE_FLOOR = NEED_PAIRS                       # 36
MIN_PER_COLOUR = 2             # L2: each colour used >= ceil(8/6) = 2 times


def min_per_for(n):
    """L2 per-colour minimum for an n-colouring: each colour class needs
    >= ceil((n-1)/6) cells (<=6 edges/cell must reach n-1 other colours),
    and >= 1 regardless (the colour must appear). n=9 -> 2 (== the legacy
    MIN_PER_COLOUR constant, so default callers are unchanged); n=2..7 ->
    1; n=8 -> 2; n=10..13 -> 2; n=14 -> 3."""
    return max(1, -(-(n - 1) // 6))


def edge_floor_for(n):
    """A witness needs >= C(n,2) distinct bichromatic interior edges, so
    its shape has >= C(n,2) interior edges -- the k-independent edge floor
    for n colours (n=9 -> 36 == EDGE_FLOOR)."""
    return n * (n - 1) // 2


def first_feasible_k(n):
    """Smallest cell count k whose maximum interior edges I_max(k) can
    reach the C(n,2) edge floor (below this, no n-colour witness can
    exist -- a solver-free lower bound on a(n))."""
    need = edge_floor_for(n)
    k = 1
    while i_max(k) < need:
        k += 1
    return k


def _hex_neighbours(cell):
    q, r = cell
    return [(q + dq, r + dr) for dq, dr in HEX_DIRS]


def i_max(k):
    """Maximum interior edges of any k-cell polyhex (hex isoperimetric
    bound, the polyhex analogue of the polyomino max-adjacency formula):
    I_max(k) = 3k - ceil(sqrt(12k - 3)).  Sanity: k=1->0, k=2->1, k=7->12,
    k=18->39, k=19->42, k=20->44."""
    if k <= 0:
        return 0
    return 3 * k - math.ceil(math.sqrt(12 * k - 3))


# Canonical PROVED a(8)=16 witness (from research/solver-results.json, read
# 2026-05-16). Embedded so the verifier self-test and the g1 "extend the
# proven witness" generator need zero file lookups.
A8_CELLS = [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3),
            (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (4, 2)]
A8_COLORING = {
    (0, 0): 0, (0, 1): 1, (0, 2): 2, (0, 3): 3, (1, 0): 4, (1, 1): 5,
    (1, 2): 0, (1, 3): 6, (2, 0): 7, (2, 1): 6, (2, 2): 7, (2, 3): 1,
    (3, 0): 2, (3, 1): 4, (3, 2): 3, (4, 2): 5,
}

# A reference k-cell / 9-colour witness, embedded after a build sweep so a
# cold run can INSTANTLY emit a double-verified certificate floor; the run
# still re-derives it independently. None => not embedded (search cold).
KNOWN_WITNESS = None  # {(q, r): colour, ...}


# --------------------------------------------------------------------------
# Geometry helpers
# --------------------------------------------------------------------------

def interior_edge_pairs(cells):
    """List of adjacent-cell pairs both inside `cells` (each pair once)."""
    cs = set(cells)
    seen = set()
    out = []
    for c in cs:
        for nb in _hex_neighbours(c):
            if nb in cs:
                key = frozenset((c, nb))
                if key not in seen:
                    seen.add(key)
                    out.append((c, nb))
    return out


def interior_edge_count(cells):
    cs = set(cells)
    e = 0
    for c in cs:
        for nb in _hex_neighbours(c):
            if nb in cs and c < nb:
                e += 1
    return e


def is_connected_bfs(cells):
    cs = set(cells)
    if len(cs) <= 1:
        return True
    start = next(iter(cs))
    seen = {start}
    q = deque([start])
    while q:
        c = q.popleft()
        for nb in _hex_neighbours(c):
            if nb in cs and nb not in seen:
                seen.add(nb)
                q.append(nb)
    return seen == cs


def is_connected_uf(cells):
    """Independent connectivity check via union-find (disjoint from BFS)."""
    cs = list(set(cells))
    idx = {c: i for i, c in enumerate(cs)}
    parent = list(range(len(cs)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for c in cs:
        for nb in _hex_neighbours(c):
            if nb in idx:
                a, b = find(idx[c]), find(idx[nb])
                if a != b:
                    parent[a] = b
    roots = {find(i) for i in range(len(cs))}
    return len(cs) <= 1 or len(roots) == 1


# --- D6 canonical form (dedupe shapes up to rotation+reflection+translation)

def _r60(q, r):
    return (-r, q + r)


def _refl(q, r):
    return (r, q)


def _normalise(cell_set):
    mins_q = min(q for q, _ in cell_set)
    mins_r = min(r for _, r in cell_set)
    return tuple(sorted((q - mins_q, r - mins_r) for q, r in cell_set))


def d6_canonical(cell_set):
    best = None
    cur = list(cell_set)
    for _ in range(6):
        for variant in (cur, [_refl(q, r) for q, r in cur]):
            norm = _normalise(variant)
            if best is None or norm < best:
                best = norm
        cur = [_r60(q, r) for q, r in cur]
    return best


# --------------------------------------------------------------------------
# Shape generators
#
# Heuristic warm-start families (g1..g4) are CHEAP and find an easy witness
# fast if one exists; they are NOT complete. gen_complete_family IS the
# decisive complete enumeration -- the only one a >= k+1 conclusion may rest
# on.
# --------------------------------------------------------------------------

def _halo(cells, rings=2):
    cs = set(cells)
    frontier = set(cs)
    halo = set()
    for _ in range(rings):
        nxt = set()
        for c in frontier:
            for nb in _hex_neighbours(c):
                if nb not in cs and nb not in halo:
                    halo.add(nb)
                    nxt.add(nb)
        frontier = nxt
    return halo


def _hex_ball(radius):
    out = []
    for q in range(-radius, radius + 1):
        for r in range(-radius, radius + 1):
            if (abs(q) + abs(r) + abs(q + r)) // 2 <= radius:
                out.append((q, r))
    return out


def gen_g1_extend_a8(k):
    """Extend the PROVED a(8)=16 shape by k-16 cells (the extra colour mass)."""
    extra = k - len(A8_CELLS)
    if extra < 0:
        return
    base = list(A8_CELLS)
    halo = sorted(_halo(base, rings=max(2, extra)))
    seen = set()
    import itertools
    for add in itertools.combinations(halo, extra):
        shape = base + list(add)
        if len(set(shape)) != k:
            continue
        if not is_connected_bfs(shape):
            continue
        if interior_edge_count(shape) < EDGE_FLOOR:
            continue
        key = d6_canonical(set(shape))
        if key in seen:
            continue
        seen.add(key)
        yield ("g1", list(set(shape)))


def gen_g2_ball_minus(k):
    """Hex balls near size k, plus single-cell perturbations -- the
    roundest k-cell polyhexes."""
    seen = set()
    for radius in (2, 3):
        ball = _hex_ball(radius)
        if len(ball) < k:
            continue
        import itertools
        drop_n = len(ball) - k
        if drop_n > 4:
            # too many to drop exhaustively from a big ball; skip (g4/g5 cover)
            continue
        for drops in itertools.combinations(ball, drop_n):
            shape = [c for c in ball if c not in drops]
            if len(shape) != k or not is_connected_bfs(shape):
                continue
            if interior_edge_count(shape) < EDGE_FLOOR:
                continue
            key = d6_canonical(set(shape))
            if key not in seen:
                seen.add(key)
                yield ("g2", shape)


def gen_g3_compact_blocks(k):
    """Compact axial parallelograms summing to ~k cells, trimmed/padded."""
    seen = set()
    dims = [(a, b) for a in range(2, 8) for b in range(2, 10)
            if abs(a * b - k) <= 4]
    for a, b in dims:
        block = [(q, r) for q in range(a) for r in range(b)]
        if len(block) == k and is_connected_bfs(block):
            if interior_edge_count(block) >= EDGE_FLOOR:
                key = d6_canonical(set(block))
                if key not in seen:
                    seen.add(key)
                    yield ("g3", block)
        if len(block) > k:
            extra = len(block) - k
            border = [c for c in block
                      if sum(1 for nb in _hex_neighbours(c) if nb in set(block)) < 6]
            border.sort()
            for start in range(min(8, max(1, len(border) - extra))):
                shape = list(block)
                for c in border[start:start + extra]:
                    if c in shape:
                        shape.remove(c)
                if len(shape) != k or not is_connected_bfs(shape):
                    continue
                if interior_edge_count(shape) < EDGE_FLOOR:
                    continue
                key = d6_canonical(set(shape))
                if key not in seen:
                    seen.add(key)
                    yield ("g3", shape)


def gen_g4_ball_subsets(k):
    """k-cell connected subsets of a radius-2 hex ball (19 cells) and its
    1-ring halo -- the densest small polyhexes; broad but NOT complete."""
    import itertools
    ball = _hex_ball(2)                       # 19 cells
    halo = sorted(_halo(ball, rings=1))
    seen = set()
    pools = [list(ball)]
    for add in halo:
        pools.append(ball + [add])
    for a2 in itertools.combinations(halo, 2):
        pools.append(ball + list(a2))
    for pool in pools:
        drop_n = len(pool) - k
        if drop_n < 0 or drop_n > 4:
            continue
        for drops in itertools.combinations(pool, drop_n):
            shape = [c for c in pool if c not in drops]
            if len(shape) != k or not is_connected_bfs(shape):
                continue
            if interior_edge_count(shape) < EDGE_FLOOR:
                continue
            key = d6_canonical(set(shape))
            if key in seen:
                continue
            seen.add(key)
            yield ("g4", shape)


class IncompleteFamilyError(RuntimeError):
    """Raised when the decisive family cannot be CERTIFIED complete. The
    driver converts this to an honest 'UNDECIDED/partial' verdict and never
    claims a(9) >= k+1 from an uncertified enumeration."""


def _ts_print(msg):
    print(f"{time.strftime('%H:%M:%S')} {msg}", flush=True)


def _hex_ball_set(radius):
    s = set()
    for q in range(-radius, radius + 1):
        for r in range(-radius, radius + 1):
            if (abs(q) + abs(r) + abs(q + r)) // 2 <= radius:
                s.add((q, r))
    return s


def _span_sum(cells):
    """W_q + W_r + W_s, the summed axial extents (s = -q-r is the third
    cube coordinate). Monotone under cell addition: a superset's spans are
    >= a subset's, which is what makes the span prune sound."""
    qs = [q for q, _ in cells]
    rs = [r for _, r in cells]
    ss = [-q - r for q, r in cells]
    return ((max(qs) - min(qs)) + (max(rs) - min(rs))
            + (max(ss) - min(ss)))


def perimeter_span_lb(cells):
    """SOUND, tight lower bound on the boundary perimeter of ANY connected
    polyhex whose cells include `cells`:  P >= 2*(W_q+W_r+W_s) + 6.

    Proof sketch: connectivity (every hex step changes each of q, r, s by
    <= 1) makes every q-lane in [min q, max q] non-empty, likewise for r
    and s; the extreme cell of each lane exposes >= 2 boundary edges, and
    the edges charged to the q-, r-, s-lane families fall in the three
    DISJOINT hex edge-orientation classes, so the counts add:
    P >= 2(W_q+1) + 2(W_r+1) + 2(W_s+1) - 6 + 6 ... = 2*spansum + 6.
    Exact for hexagonal bounding regions (single cell P=6, domino P=10,
    flower P=18, radius-2 ball P=30 -- all = 2*spansum+6). The bound is
    asserted to hold for EVERY brute-enumerated polyhex (n<=10) in
    research/_verify_enum.py; if that guard ever fails the prune is unsound
    and must not be used."""
    return 2 * _span_sum(cells) + 6


def _redelmeier_pruned(k, edge_floor):
    """Textbook Redelmeier over ALL fixed k-polyhexes (each exactly once;
    Redelmeier 1981, Discrete Math 36:191-203; any-lattice generalisation
    by Mertens), yielding free shapes (D6-deduped) with >= edge_floor
    interior edges. NO bounding region -- completeness is BY CONSTRUCTION:
    a subtree is cut only when a SOUND bound proves no k-cell completion of
    the current partial can reach edge_floor:

      (1) span prune:  perimeter_span_lb(partial) > P_max  where
          P_max = 6k - 2*edge_floor.  Any completion H of the partial has
          spans >= the partial's (superset) so P(H) >= span LB > P_max,
          hence E(H) = (6k - P(H))/2 < edge_floor.  This bites EARLY
          (kills any partial that has spread out), which is what makes
          k=18 tractable.
      (2) edge prune:   min(I_max(k), e + 6*(k-m)) < edge_floor.

    Both are over-estimates of the best reachable, so cutting is sound;
    Redelmeier visits every fixed k-polyhex, so every qualifying free
    shape is still yielded.  Validated against OEIS A000228 and a disjoint
    brute method in research/_verify_enum.py."""
    imax_k = i_max(k)
    p_max = 6 * k - 2 * edge_floor
    start = (0, 0)
    poly = [start]
    pset = {start}
    seen = set()
    e_cur = [0]
    sys.setrecursionlimit(1_000_000)

    def rec(untried, untried_set, forb):
        m = len(poly)
        if m == k:
            if e_cur[0] >= edge_floor:
                key = d6_canonical(set(poly))
                if key not in seen:
                    seen.add(key)
                    yield list(poly)
            return
        if perimeter_span_lb(poly) > p_max:
            return
        if min(imax_k, e_cur[0] + 6 * (k - m)) < edge_floor:
            return
        untried = list(untried)
        untried_set = set(untried_set)
        local_forb = set()
        while untried:
            c = untried.pop()
            untried_set.discard(c)
            added = sum(1 for nb in _hex_neighbours(c) if nb in pset)
            poly.append(c)
            pset.add(c)
            e_cur[0] += added
            new = [d for d in _hex_neighbours(c)
                   if d not in pset and d not in forb
                   and d not in local_forb and d not in untried_set]
            yield from rec(untried + new,
                           untried_set | set(new),
                           forb | local_forb | {c})
            poly.pop()
            pset.discard(c)
            e_cur[0] -= added
            local_forb.add(c)

    init = list(_hex_neighbours(start))
    yield from rec(init, set(init), set())


def enumerate_complete_family(k, edge_floor=EDGE_FLOOR, log=None):
    """COMPLETE enumeration of every free k-cell polyhex with >= edge_floor
    interior edges, complete BY CONSTRUCTION via _redelmeier_pruned (sound
    span + edge prunes; no region, no saturation guess). Returns a sorted
    list of cell-lists. `certified_by` records the completeness argument."""
    if log is None:
        log = _ts_print
    t0 = time.time()
    shapes = sorted([sorted(s)
                     for s in _redelmeier_pruned(k, edge_floor)])
    enumerate_complete_family.certified_by = (
        f"sound-prune Redelmeier (span LB P>=2*spansum+6 + "
        f"min(I_max,e+6r)); P_max={6*k-2*edge_floor}; complete by "
        f"construction")
    enumerate_complete_family.certified_radius = None
    log(f"[enum] k={k} floor={edge_floor} -> {len(shapes)} free shapes "
        f"({time.time()-t0:.1f}s, complete-by-construction)")
    return shapes


enumerate_complete_family.certified_radius = None
enumerate_complete_family.certified_by = None


def enumerate_complete_family_v2(k, edge_floor=EDGE_FLOOR, log=None):
    """INDEPENDENT second enumerator (path 3) for the same family, by a
    DIFFERENT mechanism: canonical-set breadth-first growth.

    level[1] = {1-cell}; level[m] = every D6-canonical m-cell polyhex
    obtained by adding one halo cell to a surviving (m-1)-cell shape,
    DROPPING any partial the SOUND prune rules out (span LB > P_max, or
    min(I_max(k), e + 6*(k-m)) < edge_floor). Completeness: every connected
    polyhex has a non-cut cell whose removal stays connected, so each k-cell
    target is reachable by single-cell additions through connected
    subshapes; and for any such subshape the target itself is a k-superset
    with >= edge_floor edges, so the sound prune (which only cuts when NO
    k-superset can reach the floor) never discards it. Shares only the
    validated primitives (i_max, perimeter_span_lb, d6_canonical,
    interior_edge_count) with path 2 -- the growth LOGIC (canonical-dedup
    BFS) is disjoint from Redelmeier frontier-DFS. Agreement of the two on
    F_k is the project's two-independent-methods certificate for any
    a(9) >= k+1 claim."""
    if log is None:
        log = _ts_print
    t0 = time.time()
    imax_k = i_max(k)
    p_max = 6 * k - 2 * edge_floor

    def survives(cells, m):
        if perimeter_span_lb(cells) > p_max:
            return False
        e = interior_edge_count(cells)
        if min(imax_k, e + 6 * (k - m)) < edge_floor:
            return False
        return True

    level = {((0, 0),)}                         # canonical 1-cell
    for m in range(2, k + 1):
        nxt = {}
        for shape in level:
            cs = set(shape)
            halo = {nb for c in cs for nb in _hex_neighbours(c) if nb not in cs}
            for h in halo:
                cand = cs | {h}
                if not survives(cand, m):
                    continue
                key = d6_canonical(cand)
                if key not in nxt:
                    nxt[key] = sorted(cand)
        level = set(tuple(v) for v in nxt.values())
        if log and m % 4 == 0:
            log(f"[enum2] k={k} grew to size {m}: {len(level)} live "
                f"partials ({time.time()-t0:.1f}s)")
    out = sorted([sorted(s) for s in level
                  if interior_edge_count(set(s)) >= edge_floor])
    log(f"[enum2] k={k} floor={edge_floor} -> {len(out)} free shapes "
        f"({time.time()-t0:.1f}s, independent BFS method)")
    return out


def enumerate_complete_family_certified(k, edge_floor=EDGE_FLOOR, log=None,
                                        cross_check=True):
    """F_k via path 2 (Redelmeier, complete-by-construction). When
    cross_check, ALSO enumerate via path 3 (independent BFS) and require
    the D6-canonical SETS to be identical; on any mismatch raise
    IncompleteFamilyError so the driver never asserts a(9) >= k+1 on
    disagreeing enumerators (two-independent-methods rule)."""
    if log is None:
        log = _ts_print
    fam = enumerate_complete_family(k, edge_floor=edge_floor, log=log)
    if cross_check:
        fam2 = enumerate_complete_family_v2(k, edge_floor=edge_floor,
                                            log=log)
        s1 = frozenset(d6_canonical(set(s)) for s in fam)
        s2 = frozenset(d6_canonical(set(s)) for s in fam2)
        if s1 != s2:
            raise IncompleteFamilyError(
                f"F_{k} enumerator DISAGREEMENT: path2={len(s1)} "
                f"path3={len(s2)} sym_diff={len(s1 ^ s2)}; refusing to "
                f"treat the family as complete (a(9)>={k+1} would be "
                f"unsound). Investigate before any lower-bound claim.")
        log(f"[enum] k={k} TWO-METHOD AGREEMENT: path2==path3, "
            f"|F_{k}|={len(s1)} (certified complete)")
    return fam


def gen_complete_family(k, edge_floor=EDGE_FLOOR):
    """TRUE STREAMING view for the M1 driver: yields ("g5", shape) as path 2
    (span+edge-pruned Redelmeier) discovers each free shape, so the SAT
    colourer can try shapes immediately and SHORT-CIRCUIT on the first
    witness (the F_k members surface in the first seconds; the slow part is
    only the completeness exhaustion afterwards). Path 2 is complete by
    construction, so a full exhaustion of this generator with every shape
    UNSAT is itself sound; the driver additionally runs the path2==path3
    two-method cross-check (`enumerate_complete_family_certified`) before it
    actually asserts a(9) >= k+1 (see run_m1)."""
    for shape in _redelmeier_pruned(k, edge_floor):
        yield ("g5", shape)


def all_shapes(families, k):
    """Heuristic warm-start families FIRST (cheap), then the COMPLETE g5
    family (decisive). Globally D6-deduped so g5 never re-emits a g1..g4
    shape."""
    gens = {"g1": gen_g1_extend_a8, "g2": gen_g2_ball_minus,
            "g3": gen_g3_compact_blocks, "g4": gen_g4_ball_subsets,
            "g5": lambda kk: gen_complete_family(kk)}
    seen = set()
    for fam in families:
        for tag, shape in gens[fam](k):
            key = d6_canonical(set(shape))
            if key in seen:
                continue
            seen.add(key)
            yield (tag, shape)


# --------------------------------------------------------------------------
# M1 -- exact colourer (PySAT if available, else pure-Python backtracking)
#
# Colour model (k-independent): 9 colours, EACH used >= 2 times (L2
# necessity), all C(9,2)=36 pairs edge-adjacent. The shape fixes the total
# to k cells, so ">= 2 each" forces the multiset: k=18 -> nine 2s; k=19 ->
# one 3 + eight 2s; k=20 -> {one 4 / two 3s} + rest 2s; the solver picks.
# The 9 colours stay fully interchangeable (constraints symmetric in
# colour), so the lex-leader symmetry break is sound for the full S_9.
# --------------------------------------------------------------------------

def _bfs_order(cells):
    cs = set(cells)
    order = []
    seen = {cells[0]}
    dq = deque([cells[0]])
    while dq:
        c = dq.popleft()
        order.append(c)
        for nb in _hex_neighbours(c):
            if nb in cs and nb not in seen:
                seen.add(nb)
                dq.append(nb)
    for c in cells:
        if c not in seen:
            order.append(c)
    return order


def colour_shape_exact(cells, n=NCOL, node_budget=2_000_000, min_per=None):
    """Pure-Python exact backtracking colourer. Each colour used >= min_per
    (default min_per_for(n)), all C(n,2) pairs edge-adjacent. Returns
    dict cell->colour, None if no
    such colouring (definitive for this shape within node_budget), or
    "BUDGET" if the node budget was hit before exhausting the search (NOT a
    proof of UNSAT). Lex-leader colour symmetry break (sound for full S_n).
    """
    if min_per is None:
        min_per = min_per_for(n)
    cells = list(cells)
    order = _bfs_order(cells)
    cs = set(cells)
    pos = {c: i for i, c in enumerate(order)}
    adj_idx = [[pos[nb] for nb in _hex_neighbours(order[i]) if nb in cs]
               for i in range(len(order))]
    m = len(order)
    total_pairs = n * (n - 1) // 2
    max_per = m - min_per * (n - 1)            # max any one colour can take
    colour = [-1] * m
    count = [0] * n
    nodes = [0]
    hit_budget = [False]

    def covered_and_potential():
        cov = set()
        potential = 0
        for i in range(m):
            ci = colour[i]
            for j in adj_idx[i]:
                if j <= i:
                    continue
                cj = colour[j]
                if ci >= 0 and cj >= 0:
                    if ci != cj:
                        cov.add((ci, cj) if ci < cj else (cj, ci))
                else:
                    potential += 1
        return len(cov), potential

    def feasible_counts(i):
        # cells left to assign must be able to lift every colour to >= 2
        left = m - i
        deficit = sum(max(0, min_per - count[c]) for c in range(n))
        return deficit <= left

    def bt(i, max_used):
        nodes[0] += 1
        if nodes[0] > node_budget:
            hit_budget[0] = True
            return None
        if i == m:
            if any(count[c] < min_per for c in range(n)):
                return None
            cov, _ = covered_and_potential()
            return dict(zip(order, colour)) if cov == total_pairs else None
        if not feasible_counts(i):
            return None
        if i and (i & 7) == 0:
            cov, pot = covered_and_potential()
            if (total_pairs - cov) > pot:
                return None
        hi = min(max_used + 1, n - 1)
        for c in range(hi + 1):
            if count[c] >= max_per:
                continue
            colour[i] = c
            count[c] += 1
            res = bt(i + 1, max(max_used, c))
            if res is not None:
                return res
            count[c] -= 1
            colour[i] = -1
            if hit_budget[0]:
                return None
        return None

    res = bt(0, -1)
    if res is not None:
        return res
    return "BUDGET" if hit_budget[0] else None


def colour_shape_sat(cells, n=NCOL, min_per=None):
    """Frozen-shape SAT colourer via PySAT Cadical195. The cell set is FIXED
    (freezing the shape removes the cell-selection blow-up that defeats free
    CDCL). n colours, each used >= min_per (default min_per_for(n); n=9 ->
    2, identical to the validated path), all C(n,2) pairs at an edge.
    Returns dict cell->colour, None if UNSAT, "BUDGET" if inconclusive
    (conflict budget hit -- NOT a proof of UNSAT), or False if PySAT is
    unavailable (caller falls back to colour_shape_exact)."""
    try:
        from pysat.solvers import Cadical195
        from pysat.card import CardEnc, EncType
    except ImportError:
        return False
    if min_per is None:
        min_per = min_per_for(n)
    cells = _bfs_order(list(cells))
    cs = set(cells)
    m = len(cells)
    idx = {c: i for i, c in enumerate(cells)}
    edges = []
    for c in cells:
        for nb in _hex_neighbours(c):
            if nb in cs and idx[c] < idx[nb]:
                edges.append((idx[c], idx[nb]))
    nv = [0]

    def newv():
        nv[0] += 1
        return nv[0]

    V = [[newv() for _ in range(n)] for _ in range(m)]
    cl = []
    for i in range(m):
        cl.append([V[i][k] for k in range(n)])
        for a in range(n):
            for b in range(a + 1, n):
                cl.append([-V[i][a], -V[i][b]])
    # Colour-symmetry lex-leader: the n colour labels are fully
    # interchangeable (constraints symmetric in colour). Force colour c to
    # first appear only after colour c-1: cell 0 is colour 0; colour c at
    # cell i only if some j<i has colour c-1. Sound for the full S_n.
    for c in range(1, n):
        cl.append([-V[0][c]])
        for i in range(1, m):
            cl.append([-V[i][c]] + [V[j][c - 1] for j in range(i)])
    # Each colour used >= min_per AND <= max_per, the TIGHT per-k bound
    # max_per = m - min_per*(n-1) (the most any one colour can take while
    # the other n-1 still get >= min_per). n=9,k=18 -> [2,2] i.e. exactly
    # 2 each; n=9,k=19 -> [2,3] i.e. one colour 3, rest 2; etc. The
    # at-most is logically implied by ">=min_per each + fixed total m",
    # but stating it explicitly is load-bearing for SPEED: it restores
    # the strong unit propagation that makes each UNSAT proof ~0.3s
    # instead of ~25s (measured regression when at-most was omitted).
    # Both bounds keep the full S_n colour symmetry, so the lex-leader
    # break stays sound.
    max_per = m - min_per * (n - 1)
    for k in range(n):
        lits = [V[i][k] for i in range(m)]
        for _enc, _b in ((CardEnc.atleast, min_per),
                         (CardEnc.atmost, max_per)):
            c = _enc(lits, bound=_b, top_id=nv[0],
                     encoding=EncType.seqcounter)
            if c.clauses:
                nv[0] = max(nv[0],
                            max(abs(l) for cc in c.clauses for l in cc))
                cl.extend(c.clauses)
    # Each of the C(n,2) colour pairs must occur on >=1 interior edge.
    # If there are NO interior edges at all but at least one pair must be
    # covered, the instance is trivially UNSAT (an empty `aux` would be an
    # empty clause -> PySAT IndexError). Return the definitive UNSAT
    # directly rather than constructing a degenerate CNF.
    if not edges and n >= 2:
        return None
    for a in range(n):
        for b in range(a + 1, n):
            aux = []
            for (u, v) in edges:
                z = newv()
                cl.append([-z, V[u][a], V[u][b]])
                cl.append([-z, V[v][a], V[v][b]])
                cl.append([-z, -V[u][a], -V[v][a]])
                cl.append([-z, -V[u][b], -V[v][b]])
                aux.append(z)
            cl.append(aux)
    s = Cadical195(bootstrap_with=cl)
    try:
        s.conf_budget(2_000_000)
        res = s.solve_limited(expect_interrupt=True)
        if res is None:
            return "BUDGET"      # inconclusive: NOT a proof of UNSAT
        if not res:
            return None          # definitive UNSAT for this shape
        model = set(s.get_model())
    finally:
        s.delete()
    return {cells[i]: k for i in range(m) for k in range(n)
            if V[i][k] in model}


def run_m1(families, time_box_s, k, log):
    """Returns one of:
      ("WITNESS", {...})            a SAT colouring was found at this k
      ("COMPLETE_UNSAT", n_tested)  g5 family fully enumerated, every member
                                    definitively UNSAT, ZERO inconclusive
                                    -> rigorous proof a(9) >= k+1
      ("INCOMPLETE", info)          time-box / budget / inconclusive: no
                                    witness AND no completeness -> undecided
    """
    log(f"[M1] k={k} families={families} time_box={time_box_s:.0f}s")
    probe = colour_shape_sat(list(A8_CELLS), n=8)
    use_sat = probe is not False
    log(f"[M1] colourer = "
        f"{'PySAT-Cadical195' if use_sat else 'pure-Python exact-BT'}")
    have_complete = "g5" in families
    t0 = time.time()
    tried = 0
    budget_skips = 0
    g5_seen = 0
    last_fam = None
    shapes_iter = iter(all_shapes(families, k))
    while True:
        try:
            fam, shape = next(shapes_iter)
        except StopIteration:
            break
        except IncompleteFamilyError as e:
            log(f"[M1] g5 family NOT certifiable complete at k={k}: {e}")
            return ("INCOMPLETE", f"g5 uncertified: {e}")
        if time.time() - t0 > time_box_s:
            log(f"[M1] time-box hit after {tried} shapes "
                f"(last fam={last_fam})")
            return ("INCOMPLETE",
                    f"time-box after {tried} shapes, g5 not exhausted")
        tried += 1
        last_fam = fam
        if fam == "g5":
            g5_seen += 1
        if tried % 200 == 0:
            log(f"[M1] {tried} shapes ({g5_seen} from complete g5), "
                f"t={time.time()-t0:.0f}s, last fam={fam} "
                f"edges={interior_edge_count(shape)} skips={budget_skips}")
        if use_sat:
            col = colour_shape_sat(shape, n=NCOL)
            if col is False:
                use_sat = False
                col = colour_shape_exact(shape, n=NCOL, node_budget=400_000)
        else:
            col = colour_shape_exact(shape, n=NCOL, node_budget=400_000)
        if col == "BUDGET":
            budget_skips += 1
            continue
        if isinstance(col, dict) and col:
            engine = "PySAT-Cadical195" if use_sat else "pure-Python-exact-BT"
            log(f"[M1] SAT on {fam} shape #{tried} "
                f"(edges={interior_edge_count(shape)}) engine={engine} "
                f"t={time.time()-t0:.1f}s")
            return ("WITNESS",
                    {"method": f"M1-frozen-shape ({engine})", "family": fam,
                     "coloring": col, "shapes_tried": tried, "k": k})
        # col is None: this shape is definitively UNSAT -- continue.
    log(f"[M1] families exhausted at k={k}: {tried} shapes "
        f"({g5_seen} from complete g5), {budget_skips} inconclusive")
    if have_complete and budget_skips == 0:
        # Every member of the streamed complete family was definitively
        # UNSAT. Path 2 is complete by construction, but before asserting
        # a(9) >= k+1 we require the project's two-independent-methods
        # certificate: path2 (Redelmeier) and path3 (BFS) must enumerate
        # the IDENTICAL F_k. This is the slow full exhaustion, paid ONLY
        # here (the lower-bound branch), never on the fast witness path.
        try:
            log(f"[M1] all UNSAT; running path2==path3 completeness "
                f"certificate for a(9)>={k+1} ...")
            enumerate_complete_family_certified(
                k, edge_floor=EDGE_FLOOR, log=log, cross_check=True)
            return ("COMPLETE_UNSAT", tried)
        except IncompleteFamilyError as e:
            log(f"[M1] completeness certificate FAILED: {e}")
            return ("INCOMPLETE", f"dual-method cert failed: {e}")
    return ("INCOMPLETE",
            f"{tried} tested, {budget_skips} inconclusive, "
            f"complete-family{'' if have_complete else ' NOT'} requested")


# --------------------------------------------------------------------------
# M2 -- simulated annealing over (shape (+) colouring)  (corroboration only)
# --------------------------------------------------------------------------

def _distinct_pairs(cells, coloring):
    cs = set(cells)
    pr = set()
    for c in cs:
        a = coloring[c]
        for nb in _hex_neighbours(c):
            if nb in cs:
                b = coloring[nb]
                if a != b:
                    pr.add((a, b) if a < b else (b, a))
    return len(pr)


def _energy(cells, coloring, n=NCOL, min_per=None):
    if min_per is None:
        min_per = min_per_for(n)
    need = n * (n - 1) // 2
    cnt = {}
    for c in cells:
        cnt[coloring[c]] = cnt.get(coloring[c], 0) + 1
    # penalise any colour used fewer than min_per times, and any
    # colour entirely missing (all n colours must appear)
    deficit = sum(max(0, min_per - cnt.get(c, 0)) for c in range(n))
    missing = sum(1 for c in range(n) if cnt.get(c, 0) == 0)
    comp_pen = 0 if is_connected_bfs(cells) else 50
    return ((need - _distinct_pairs(cells, coloring))
            + 3 * deficit + 5 * missing + comp_pen)


def run_m2(time_box_s, k, log, seed=12345, n=NCOL):
    log(f"[M2] start anneal k={k} time_box={time_box_s:.0f}s seed={seed}")
    rng = random.Random(seed)
    t0 = time.time()
    best = None
    restart = 0
    seed_shapes = [s for _, s in all_shapes(["g4", "g2", "g1"], k)][:120]
    while time.time() - t0 < time_box_s:
        restart += 1
        if seed_shapes:
            cells = list(seed_shapes[rng.randrange(len(seed_shapes))])
        else:
            cells = [c for c in _hex_ball(3)][:k]
        rng.shuffle(cells)
        coloring = {c: (i // MIN_PER_COLOUR) % n for i, c in enumerate(cells)}
        T = 2.0
        e = _energy(cells, coloring, n)
        steps = 0
        while T > 0.01 and time.time() - t0 < time_box_s:
            steps += 1
            move = rng.random()
            old = None
            if move < 0.5:
                c = cells[rng.randrange(len(cells))]
                old = ("rc", c, coloring[c])
                coloring[c] = rng.randrange(n)
            elif move < 0.85:
                a = cells[rng.randrange(len(cells))]
                b = cells[rng.randrange(len(cells))]
                old = ("sw", a, b, coloring[a], coloring[b])
                coloring[a], coloring[b] = coloring[b], coloring[a]
            else:
                csset = set(cells)
                opts = [nb for c in cells for nb in _hex_neighbours(c)
                        if nb not in csset]
                if not opts:
                    continue
                bcells = [c for c in cells
                          if any(nb not in csset for nb in _hex_neighbours(c))]
                src = bcells[rng.randrange(len(bcells))]
                dst = opts[rng.randrange(len(opts))]
                old = ("sl", src, dst, coloring[src])
                idx = cells.index(src)
                cells[idx] = dst
                coloring[dst] = coloring.pop(src)
                if not is_connected_bfs(cells):
                    cells[idx] = src
                    coloring[src] = coloring.pop(dst)
                    continue
            ne = _energy(cells, coloring, n)
            if ne <= e or rng.random() < pow(2.718281828, (e - ne) / T):
                e = ne
            else:
                if old[0] == "rc":
                    coloring[old[1]] = old[2]
                elif old[0] == "sw":
                    coloring[old[1]], coloring[old[2]] = old[3], old[4]
                else:
                    idx = cells.index(old[2])
                    cells[idx] = old[1]
                    coloring[old[1]] = coloring.pop(old[2])
            T *= 0.9997
            if e == 0:
                col = {c: coloring[c] for c in cells}
                log(f"[M2] SAT restart={restart} steps={steps} "
                    f"t={time.time()-t0:.1f}s")
                return {"method": "M2-simulated-annealing",
                        "coloring": col, "restarts": restart, "k": k}
            if best is None or e < best:
                best = e
        if restart % 25 == 0:
            log(f"[M2] restart={restart} best_energy={best} "
                f"t={time.time()-t0:.0f}s")
    log(f"[M2] time-box hit, best_energy={best}")
    return None


# --------------------------------------------------------------------------
# Verifiers (two disjoint code paths). Both accept any k: 9 colours, each
# colour used >= 2 times, connected, all C(9,2)=36 pairs edge-adjacent.
# --------------------------------------------------------------------------

def verify_v1(coloring, n, min_per=None):
    """Orchestration-style: BFS connectivity + pair iteration."""
    if min_per is None:
        min_per = min_per_for(n)
    cells = list(coloring)
    cnt = {}
    for c in cells:
        cnt[coloring[c]] = cnt.get(coloring[c], 0) + 1
    if sorted(cnt) != list(range(n)):
        return False, f"V1: colours present = {sorted(cnt)}, want 0..{n-1}"
    if any(cnt[c] < min_per for c in range(n)):
        return False, f"V1: a colour used < {min_per}: {sorted(cnt.items())}"
    if not is_connected_bfs(cells):
        return False, "V1: not connected (BFS)"
    pairs = set()
    cset = set(cells)
    for c, col in coloring.items():
        for nb in _hex_neighbours(c):
            if nb in cset and coloring[nb] != col:
                a, b = col, coloring[nb]
                pairs.add((a, b) if a < b else (b, a))
    need = n * (n - 1) // 2
    if len(pairs) != need:
        return False, f"V1: {len(pairs)}/{need} pairs"
    return True, (f"V1 OK: {len(cells)} cells, connected, {need}/{need} "
                  f"pairs, colour counts {sorted(cnt.values())}")


def verify_v2(coloring, n, min_per=None):
    """From-scratch: union-find connectivity + independent edge scan +
    per-colour count check. Shares no logic with V1."""
    if min_per is None:
        min_per = min_per_for(n)
    cells = list(coloring)
    cnt = {}
    for c in cells:
        cnt[coloring[c]] = cnt.get(coloring[c], 0) + 1
    if sorted(cnt) != list(range(n)):
        return False, f"V2: colour set wrong {sorted(cnt.items())}"
    if any(v < min_per for v in cnt.values()):
        return False, f"V2: a colour used < {min_per} {sorted(cnt.items())}"
    if not is_connected_uf(cells):
        return False, "V2: not connected (union-find)"
    edge_pairs = set()
    for (a, b) in interior_edge_pairs(cells):
        ca, cb = coloring[a], coloring[b]
        if ca != cb:
            edge_pairs.add((ca, cb) if ca < cb else (cb, ca))
    expect = {(i, j) for i in range(n) for j in range(i + 1, n)}
    if edge_pairs != expect:
        miss = sorted(expect - edge_pairs)
        return False, f"V2: missing {miss[:6]}"
    return True, (f"V2 OK: {len(cells)} cells, UF-connected, all "
                  f"{len(expect)} pairs, counts {sorted(cnt.values())}")


def self_test(log):
    log("[self-test] verifying canonical a(8)=16 witness (8 colours, 28 pairs)")
    ok1, m1 = verify_v1(A8_COLORING, 8)
    ok2, m2 = verify_v2(A8_COLORING, 8)
    log(f"  V1: {m1}")
    log(f"  V2: {m2}")
    # Negative control: a deliberately broken witness MUST be rejected.
    bad = dict(A8_COLORING)
    bad[(4, 2)] = 0                       # collapse a colour -> count wrong
    nb1, _ = verify_v1(bad, 8)
    nb2, _ = verify_v2(bad, 8)
    if nb1 or nb2:
        log("[self-test] FAIL - a verifier ACCEPTED a broken witness; abort")
        return False
    # Enumerator sanity: I_max formula on known small values.
    if not (i_max(1) == 0 and i_max(2) == 1 and i_max(7) == 12
            and i_max(18) == 39 and i_max(19) == 42):
        log("[self-test] FAIL - I_max formula wrong; abort")
        return False
    if not (ok1 and ok2):
        log("[self-test] FAIL - verifiers reject a known-good witness; abort")
        return False
    log("[self-test] PASS - both verifiers sound (good accepted, bad "
        "rejected), I_max formula OK")
    return True


# --------------------------------------------------------------------------
# Output assembly
# --------------------------------------------------------------------------

def _bbox(cells):
    qs = [q for q, _ in cells]
    rs = [r for _, r in cells]
    return f"{max(qs)-min(qs)+1} x {max(rs)-min(rs)+1}"


def _ascii_art(coloring):
    cells = list(coloring)
    minq = min(q for q, _ in cells)
    minr = min(r for _, r in cells)
    maxq = max(q for q, _ in cells)
    maxr = max(r for _, r in cells)
    lines = []
    for q in range(minq, maxq + 1):
        row = " " * (q - minq)
        for r in range(minr, maxr + 1):
            row += (str(coloring[(q, r)]) if (q, r) in coloring else ".") + " "
        lines.append(row.rstrip())
    return "\n".join(lines)


def write_outputs(verdict, research_dir, log):
    """verdict: dict with keys
      status   : "PROVED" | "LOWER_BOUND" | "UNDECIDED"
      value    : int a(9) (PROVED only) else None
      lb       : proven lower bound on a(9)
      witness  : {(q,r):colour} (PROVED only)
      m2       : independent M2 witness if any
      methods  : list of method strings
      detail   : free-text status detail
    """
    status = verdict["status"]
    value = verdict.get("value")
    lb = verdict["lb"]
    witness = verdict.get("witness")
    m2 = verdict.get("m2")
    methods = verdict.get("methods", [])

    rec = {
        "9": {
            "n": 9,
            "value": value,
            "status": status,
            "analytical_lower_bound": 18,
            "proven_lower_bound": lb,
            "lower_bound_method": "analytic L2 = 9*ceil(8/6) = 18 "
                                  "(lower-bounds.md; re-derived by "
                                  "verify_l1_l2.py); raised by complete "
                                  "F_k all-UNSAT enumeration where stated",
            "bbox": _bbox(list(witness)) if witness else None,
            "cells": sorted([list(c) for c in witness]) if witness else None,
            "coloring": ({f"{q},{r}": c for (q, r), c in witness.items()}
                         if witness else None),
            "methods": methods,
            "verifiers": ["V1-bfs-pair-iter", "V2-unionfind-edge-scan"],
            "detail": verdict.get("detail", ""),
            "note": "Separate file; canonical solver-results.json untouched.",
        }
    }
    out_json = os.path.join(research_dir, "solver-n9-results.json")
    with open(out_json, "w", encoding="utf-8") as f:
        json.dump(rec, f, indent=2)
    log(f"[out] wrote {out_json}")

    cert = os.path.join(research_dir, "n9-certificate.md")
    with open(cert, "w", encoding="utf-8") as f:
        f.write("# a(9) certificate -- oeis-a396138\n\n")
        f.write("## Lower bound  a(9) >= 18  (analytic L2)\n\n")
        f.write("Colour i occupies c_i cells. Each cell has <= 6 edges, so "
                "edges incident to class C_i <= 6*c_i. Covering the n-1=8 "
                "other colours needs >= 8 such edges (distinct other "
                "colours), so 6*c_i >= 8 => c_i >= ceil(8/6) = 2. Sum over "
                "9 colours: a(9) >= 18.  (research/lower-bounds.md S L2; "
                "re-derived cold by research/verify_l1_l2.py.)\n\n")
        f.write("## Decisive-family lemma\n\n")
        f.write("A witness needs all C(9,2)=36 colour pairs at an edge. One "
                "interior edge carries exactly one unordered colour-pair "
                "label, so >= 36 DISTINCT bichromatic interior edges are "
                "required; bichromatic edges are a subset of all interior "
                "edges, hence ANY k-cell witness shape has >= 36 interior "
                "edges. F_k := { free k-cell polyhexes, >= 36 interior "
                "edges } is therefore the complete decisive family at each "
                "k. (research/n9_solve.py:gen_complete_family enumerates "
                "F_k completely by a Redelmeier search pruned only by the "
                "sound bound min(I_max(k), e + 6*(k-m)) >= 36.)\n\n")

        if status == STATUS_PROVED:
            f.write(f"## Upper bound  a(9) <= {value}  (explicit witness)\n\n")
            f.write(f"Found by: {', '.join(methods)}. "
                    f"F_18..F_{value-1} were each completely enumerated and "
                    f"every member definitively UNSAT (or, for k=18, the "
                    f"analytic L2 floor), so a(9) >= {value} as well.\n\n")
            f.write("```\n" + _ascii_art(witness) + "\n```\n\n")
            f.write("Colour table (cell -> colour):\n\n```\n")
            for (q, r), c in sorted(witness.items()):
                f.write(f"({q},{r}) -> {c}\n")
            f.write("```\n\n")
            ok1, msg1 = verify_v1(witness, NCOL)
            ok2, msg2 = verify_v2(witness, NCOL)
            f.write(f"- {msg1}\n- {msg2}\n\n")
            if m2:
                ok1b, _ = verify_v1(m2, NCOL)
                ok2b, _ = verify_v2(m2, NCOL)
                f.write(f"Independent M2 witness also verified: "
                        f"V1={ok1b} V2={ok2b}.\n\n")
            f.write(f"## Conclusion\n\n{lb} <= a(9) <= {value}  =>  "
                    f"**a(9) = {value}**. Upper bound by an explicit witness "
                    f"double-verified by two disjoint checkers; lower bound "
                    f"by an analytic counting proof plus complete-family "
                    f"all-UNSAT enumeration. No single engine is trusted.\n")
        elif status == "LOWER_BOUND":
            f.write(f"## Result: a(9) >= {lb}  (rigorous)\n\n")
            f.write(verdict.get("detail", "") + "\n\n")
            f.write(f"For every k in 18..{lb-1} the COMPLETE family F_k was "
                    f"enumerated (Redelmeier, sound-prune, D6-deduped -- "
                    f"complete by construction) and EVERY member was "
                    f"definitively UNSAT for the 9-colour / >=2-each / "
                    f"all-36-pairs CSP, with ZERO inconclusive (budget) "
                    f"skips. Hence no k-cell witness exists for "
                    f"k <= {lb-1}, i.e. **a(9) >= {lb}**. Each per-shape "
                    f"UNSAT is independently re-checkable (rerun the "
                    f"colourer on any shape's CNF). a(9) pin-down at "
                    f"k >= {lb} was not reached within the time budget.\n")
        else:
            f.write("## Result: UNDECIDED (honest partial)\n\n")
            f.write(verdict.get("detail", "") + "\n\n")
            f.write("No witness was found AND the complete family was NOT "
                    "exhausted with zero inconclusive skips at the current "
                    "k, so neither a(9)=k nor a(9)>=k+1 is claimed. The "
                    "analytic lower bound a(9) >= 18 still holds. Re-run "
                    "with a larger time budget to settle the term.\n")
    log(f"[out] wrote {cert}")
    return out_json, cert


# --------------------------------------------------------------------------
# CLI / schedule
# --------------------------------------------------------------------------

class _Timeout(Exception):
    pass


def _with_hard_wall(seconds, fn, *a, **k):
    """POSIX SIGALRM hard wall (the cold container is Linux). On platforms
    without SIGALRM (e.g. Windows dev box) falls back to running fn with no
    wall -- fn's own time-box checks still bound it."""
    if not hasattr(signal, "SIGALRM"):
        return fn(*a, **k)

    def _h(signum, frame):
        raise _Timeout()
    old = signal.signal(signal.SIGALRM, _h)
    signal.alarm(int(seconds))
    try:
        return fn(*a, **k)
    except _Timeout:
        return None
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old)


def main():
    p = argparse.ArgumentParser(description="Pure-Python a(9) solver")
    p.add_argument("--mode", default="all",
                   choices=["all", "self-test", "m1", "m2"])
    p.add_argument("--families", default="g1,g4,g2,g3,g5",
                   help="comma list; g5 is the COMPLETE decisive family. "
                        "Drop g5 for a witness-only quick pass.")
    p.add_argument("--budget-hours", type=float, default=8.0)
    p.add_argument("--k-max", type=int, default=22,
                   help="highest k to ascend to before reporting a partial")
    p.add_argument("--research-dir", default=os.path.join(_HERE))
    args = p.parse_args()

    research_dir = os.path.abspath(args.research_dir)
    os.makedirs(research_dir, exist_ok=True)
    log_path = os.path.join(research_dir, "n9-runbook-log.txt")
    log_f = open(log_path, "a", encoding="utf-8", buffering=1)

    def log(msg):
        line = f"{time.strftime('%H:%M:%S')} {msg}"
        print(line, flush=True)
        log_f.write(line + "\n")

    fams = [x.strip() for x in args.families.split(",") if x.strip()]
    log("=" * 64)
    log(f"a(9) pure-Python solve  mode={args.mode}  "
        f"budget={args.budget_hours}h  families={fams}  k_max={args.k_max}")
    log("Canonical research/solver-results.json will NOT be touched.")

    if not self_test(log):
        sys.exit(2)

    if KNOWN_WITNESS is not None:
        kw = {tuple(k_) if not isinstance(k_, tuple) else k_: v
              for k_, v in KNOWN_WITNESS.items()}
        ok1, mk1 = verify_v1(kw, NCOL)
        ok2, mk2 = verify_v2(kw, NCOL)
        log(f"[known-witness] V1 -> {mk1}")
        log(f"[known-witness] V2 -> {mk2}")
        if ok1 and ok2:
            log("[known-witness] FLOOR established (embedded double-verified "
                "witness + analytic L2). Run continues to re-derive it "
                "independently.")
        else:
            log("[known-witness] WARNING embedded witness failed a verifier "
                "- ignoring; searching from scratch.")

    if args.mode == "self-test":
        log("self-test only: done")
        log_f.close()
        return

    budget = args.budget_hours * 3600.0
    t_start = time.time()
    m1_witness = None
    m2_witness = None
    proven_lb = 18                                  # analytic L2 floor
    verdict = None

    # Ascent: k = 18, 19, ...  First k with a SAT member => a(9)=k.
    # Each k whose COMPLETE family is exhausted all-UNSAT (zero budget
    # skips) rigorously raises proven_lb to k+1.
    for k in range(18, args.k_max + 1):
        remaining = budget - (time.time() - t_start)
        if remaining < 60:
            log(f"[ascent] budget exhausted before k={k}")
            verdict = {"status": "UNDECIDED", "value": None, "lb": proven_lb,
                       "methods": [],
                       "detail": f"Budget hit before resolving k={k}. "
                                 f"Proven a(9) >= {proven_lb}."}
            break

        # M1 over this k. Reserve ~10% of the remaining budget for M2 at
        # k=18 corroboration only on the first iteration.
        if args.mode in ("all", "m1"):
            m1box = remaining * (0.85 if k == 18 and args.mode == "all"
                                 else 0.95)
            log(f"[ascent] k={k}: M1 box={m1box:.0f}s "
                f"(proven_lb={proven_lb}, t={time.time()-t_start:.0f}s)")
            kind, payload = _with_hard_wall(
                m1box, run_m1, fams, m1box, k, log) or ("INCOMPLETE",
                                                        "hard-wall hit")
        else:
            kind, payload = "INCOMPLETE", "m2-only mode"

        if kind == "WITNESS":
            m1_witness = payload
            ok1, _ = verify_v1(m1_witness["coloring"], NCOL)
            ok2, _ = verify_v2(m1_witness["coloring"], NCOL)
            log(f"[certify] M1 witness k={k} V1={ok1} V2={ok2}")
            if ok1 and ok2:
                verdict = {"status": STATUS_PROVED, "value": k, "lb": k,
                           "witness": m1_witness["coloring"],
                           "methods": [m1_witness["method"]],
                           "detail": f"a(9)={k} witness on family "
                                     f"{m1_witness['family']}."}
                break
            log("[certify] M1 witness REJECTED by a verifier - discarding, "
                "continuing search at this k via remaining methods")
            m1_witness = None
            verdict = {"status": "UNDECIDED", "value": None, "lb": proven_lb,
                       "methods": [],
                       "detail": f"k={k} produced a witness that FAILED "
                                 f"verification - serious; investigate."}
            break
        elif kind == "COMPLETE_UNSAT":
            proven_lb = k + 1
            log(f"[ascent] k={k}: COMPLETE family all-UNSAT "
                f"({payload} shapes, 0 inconclusive) -> a(9) >= {proven_lb}")
            verdict = {"status": "LOWER_BOUND", "value": None,
                       "lb": proven_lb, "methods": ["M1-complete-UNSAT"],
                       "detail": f"F_{k} complete ({payload} shapes), every "
                                 f"member definitively UNSAT, 0 inconclusive."}
            # keep ascending to try to pin the exact value
            continue
        else:  # INCOMPLETE
            log(f"[ascent] k={k}: INCOMPLETE ({payload}) - cannot prove "
                f"a(9)>={k+1}; stopping ascent with proven_lb={proven_lb}")
            verdict = {"status": ("LOWER_BOUND" if proven_lb > 18
                                  else "UNDECIDED"),
                       "value": None, "lb": proven_lb,
                       "methods": (["M1-complete-UNSAT"] if proven_lb > 18
                                   else []),
                       "detail": f"k={k} incomplete: {payload}. "
                                 f"Highest rigorously proven bound "
                                 f"a(9) >= {proven_lb}."}
            break
    else:
        log(f"[ascent] reached k_max={args.k_max} without a witness")
        verdict = {"status": ("LOWER_BOUND" if proven_lb > 18
                              else "UNDECIDED"),
                   "value": None, "lb": proven_lb,
                   "methods": (["M1-complete-UNSAT"] if proven_lb > 18
                               else []),
                   "detail": f"Ascended to k_max={args.k_max}; "
                             f"a(9) >= {proven_lb} proven, value not pinned."}

    # M2 independent corroboration (never load-bearing). Run at the k of
    # the M1 witness if there is one, else at k=18.
    if args.mode in ("all", "m2"):
        m2k = (verdict["value"] if verdict and verdict.get("value")
               else 18)
        remaining = budget - (time.time() - t_start)
        if remaining > 60:
            m2box = remaining * (0.9 if args.mode == "m2" else 1.0)
            m2res = _with_hard_wall(min(m2box, remaining - 30),
                                    run_m2, min(m2box, remaining - 30),
                                    m2k, log)
            if m2res:
                ok1, _ = verify_v1(m2res["coloring"], NCOL)
                ok2, _ = verify_v2(m2res["coloring"], NCOL)
                log(f"[certify] M2 witness k={m2k} V1={ok1} V2={ok2}")
                if ok1 and ok2:
                    m2_witness = m2res
                    if verdict and verdict["status"] == STATUS_PROVED:
                        verdict["methods"].append(m2res["method"])
                    elif not (verdict and verdict["status"] == "LOWER_BOUND"):
                        # M2 found a witness M1 missed (or M1 didn't run)
                        verdict = {"status": STATUS_PROVED, "value": m2k,
                                   "lb": m2k,
                                   "witness": m2res["coloring"],
                                   "methods": [m2res["method"]],
                                   "detail": f"a(9)={m2k} via M2 "
                                             f"(M1 did not converge)."}
                else:
                    log("[certify] M2 witness REJECTED by a verifier - "
                        "discarding")

    if verdict is None:
        verdict = {"status": "UNDECIDED", "value": None, "lb": proven_lb,
                   "methods": [], "detail": "no method produced a result"}
    if m2_witness:
        verdict["m2"] = m2_witness["coloring"]

    write_outputs(verdict, research_dir, log)
    s = verdict["status"]
    if s == STATUS_PROVED:
        log(f"[done] a(9)={verdict['value']} PROVED "
            f"(methods={verdict['methods']}, "
            f"verifiers V1+V2, analytic L2 floor)")
    elif s == "LOWER_BOUND":
        log(f"[done] a(9) >= {verdict['lb']} PROVEN (complete-family "
            f"all-UNSAT); exact value not pinned within budget")
    else:
        log(f"[done] UNDECIDED: a(9) >= {verdict['lb']} (analytic/partial); "
            f"{verdict.get('detail','')}")
    log_f.close()


if __name__ == "__main__":
    main()
