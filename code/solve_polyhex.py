"""
Polyhex Coloring -- minimum cells in a connected polyhex coloured with n
colours such that every unordered pair of distinct colours is edge-adjacent.

Single-formula SAT prover with ascending k-search from analytical lower
bounds. The first SAT k IS a(n), because every k below was proved UNSAT
by SAT (or by the analytical edge / per-colour-cell bounds before the
SAT solve was even built).

Glue: hex grid primitives are imported from sat_utils.tilings.polyhex;
solver selection from sat_utils.solver_select; per-term cooperative
timeout from sat_utils.timeouts.solve_with_timeout; CLI / banner /
incremental save / SolverLogger from sat_utils.solver_cli.

Usage:
    python solve_polyhex.py --n 1-7
    python solve_polyhex.py --n 1-10

License: CC-BY-4.0
"""

from __future__ import annotations

import math
import os
import sys
import time
from collections import deque

sys.stdout.reconfigure(line_buffering=True)

from pysat.card import CardEnc, EncType  # noqa: E402  (env-var setup needs EncType)


def _flag(name, default=True):
    """Read a boolean ablation toggle from the environment.

    Used by /solver-verify's heuristic ablation: setting e.g.
    POLYHEX_USE_REFL_LEX=0 disables that encoding block so the
    solver's answer can be compared with and without it.
    """
    v = os.environ.get(name)
    if v is None:
        return default
    return v.strip().lower() not in ("0", "false", "no", "off", "")


_USE_ANCHOR = _flag("POLYHEX_USE_ANCHOR")
_USE_REFL_LEX = _flag("POLYHEX_USE_REFL_LEX")
_USE_COLOR_SYM = _flag("POLYHEX_USE_COLOR_SYM")
_USE_COLOR_CARD = _flag("POLYHEX_USE_COLOR_CARD")
_USE_BFS = _flag("POLYHEX_USE_BFS")
_USE_DEGREE1 = _flag("POLYHEX_USE_DEGREE1")
_SOLVER_NAME = os.environ.get("POLYHEX_SOLVER_NAME", "cadical195").strip().lower()
_CARD_ENC_NAME = os.environ.get("POLYHEX_CARD_ENC", "seqcounter").strip().lower()
_PHASE_BIAS = os.environ.get("POLYHEX_PHASE_BIAS", "false").strip().lower()
_RESTART_INT = int(os.environ.get("POLYHEX_RESTART_INT", "3"))


_CARD_ENCODINGS = {
    "totalizer": EncType.totalizer,
    "seqcounter": EncType.seqcounter,
    "sortnetwrk": EncType.sortnetwrk,
    "cardnetwrk": EncType.cardnetwrk,
    "kmtotalizer": EncType.kmtotalizer,
    "ladder": EncType.ladder,
    "mtotalizer": EncType.mtotalizer,
    "pairwise": EncType.pairwise,
}


def _card_enc():
    return _CARD_ENCODINGS.get(_CARD_ENC_NAME, EncType.totalizer)

from sat_utils.solver_cli import (
    SolveResult,
    STATUS_PROVED,
    STATUS_TIMEOUT,
    run_solver_cli,
)
from sat_utils.solver_select import create_solver
from sat_utils.tilings.polyhex import hex_neighbours
from sat_utils.timeouts import solve_with_timeout
from sat_utils.bounds import i_max_hex, complete_coloring_lower_bound
from figure_gen_utils.solver_log import STATUS_TIMEOUT, STATUS_VERIFY_FAILED


PRIOR_VALUES = {
    1: 1, 2: 2, 3: 3, 4: 5, 5: 7, 6: 9, 7: 12,
    8: 16, 9: 18, 10: 21,
}


def _max_edges(k):
    """Hex isoperimetric upper bound on interior edges of a connected
    k-cell polyhex: 3k - ceil(sqrt(12k - 3)), 0 for k <= 1.

    Single source of truth: sat_utils.bounds.i_max_hex. Kept as a thin
    project-local name so internal call sites stay unchanged.
    """
    return i_max_hex(k)


def _analytical_lower_bound(n):
    """Smallest k not excluded by either analytical bound: the maximum
    of the L2 contact bound and the edge-isoperimetric feasibility floor.

    Single source of truth:
    sat_utils.bounds.complete_coloring_lower_bound with the polyhex cell
    degree (6) and the hex I_max.
    """
    return complete_coloring_lower_bound(n, 6, i_max_hex)


def _grid_size_for(k, n_pairs):
    """Tight square-grid bound large enough to host any feasible k-hex."""
    max_extent = (3 * k - 3 - n_pairs) // 2
    grid = max(max_extent + 1, 2)
    if grid * grid < k:
        grid = int(math.ceil(math.sqrt(k)))
    return grid


def _add_lex_leader(clauses, active, perm, G, new_var):
    """Lex-leader symmetry breaking: active <= active[perm]."""
    lex_eq = [new_var() for _ in range(G)]
    for i in range(G):
        j = perm[i]
        if i == 0:
            clauses.append([-active[0], active[j]])
            clauses.append([-lex_eq[0], -active[0], active[j]])
            clauses.append([-lex_eq[0], active[0], -active[j]])
            clauses.append([lex_eq[0], active[0], active[j]])
            clauses.append([lex_eq[0], -active[0], -active[j]])
        else:
            clauses.append([-lex_eq[i - 1], -active[i], active[j]])
            clauses.append([-lex_eq[i], lex_eq[i - 1]])
            clauses.append([-lex_eq[i], -active[i], active[j]])
            clauses.append([-lex_eq[i], active[i], -active[j]])
            clauses.append([lex_eq[i], -lex_eq[i - 1], active[i], active[j]])
            clauses.append([lex_eq[i], -lex_eq[i - 1], -active[i], -active[j]])


def _build_cnf(n, k, grid_size):
    """Construct the SAT formula asking: does any connected k-cell polyhex
    on a grid_size x grid_size axial board admit an n-colouring with all
    n*(n-1)/2 colour pairs edge-adjacent?

    Returns (all_clauses, total_vars, active, color, cells).
    """
    n_pairs = n * (n - 1) // 2
    cells = [(q, r) for q in range(grid_size) for r in range(grid_size)]
    cell_set = set(cells)
    cell_idx = {c: i for i, c in enumerate(cells)}
    G = len(cells)

    adj = {
        i: [cell_idx[nb] for nb in hex_neighbours(q, r) if nb in cell_set]
        for i, (q, r) in enumerate(cells)
    }
    edges = []
    for i, (q, r) in enumerate(cells):
        for nb in hex_neighbours(q, r):
            if nb in cell_set:
                j = cell_idx[nb]
                if i < j:
                    edges.append((i, j))

    var_count = [0]

    def new_var():
        var_count[0] += 1
        return var_count[0]

    active = [new_var() for _ in range(G)]
    color = [[new_var() for _ in range(n)] for _ in range(G)]
    clauses = []

    # 1. Colour assignment per active cell, mutually exclusive
    for i in range(G):
        clauses.append([-active[i]] + color[i])
        for c1 in range(n):
            for c2 in range(c1 + 1, n):
                clauses.append([-color[i][c1], -color[i][c2]])
        for c in range(n):
            clauses.append([active[i], -color[i][c]])

    # 2. Spatial anchoring (some active cell on column 0 and row 0)
    if _USE_ANCHOR:
        q0 = [i for i, (q, r) in enumerate(cells) if q == 0]
        clauses.append([active[i] for i in q0])
        r0 = [i for i, (q, r) in enumerate(cells) if r == 0]
        clauses.append([active[i] for i in r0])

    # 3. Degree-1 (every active cell has at least one active neighbour)
    if _USE_DEGREE1:
        for i in range(G):
            if adj[i]:
                clauses.append([-active[i]] + [active[j] for j in adj[i]])

    # 4. Lex-leader symmetry breaking under reflection (q,r) -> (r,q).
    # This is the only D_6 element that preserves the spatial anchors
    # (it maps {q=0 cells} <-> {r=0 cells}). The 180-rotation breaker
    # used in the archived (UNSAT-only) prover is unsafe in ascending
    # SAT search because it does not preserve the anchors -- pairs of
    # configurations could both be ruled out, hiding a real witness.
    if _USE_REFL_LEX:
        refl = [cell_idx.get((r, q), i) for i, (q, r) in enumerate(cells)]
        _add_lex_leader(clauses, active, refl, G, new_var)

    # 5. Colour symmetry breaking (direct value precedence)
    if _USE_COLOR_SYM:
        for c in range(1, n):
            clauses.append([-color[0][c]])
            for i in range(1, G):
                clauses.append([-color[i][c]] + [color[j][c - 1] for j in range(i)])

    # 6. Per-colour minimum cell count
    if _USE_COLOR_CARD:
        min_per_colour = max(1, -(-(n - 1) // 6))
        if min_per_colour == 1:
            for c in range(n):
                clauses.append([color[i][c] for i in range(G)])
        else:
            for c in range(n):
                color_c_vars = [color[i][c] for i in range(G)]
                top_v = var_count[0]
                card_cl = CardEnc.atleast(
                    color_c_vars, bound=min_per_colour,
                    top_id=top_v, encoding=_card_enc(),
                )
                if card_cl:
                    var_count[0] = max(max(abs(l) for l in cl) for cl in card_cl)
                    clauses.extend(card_cl)
    else:
        # Even when ablated, every colour must appear at least once.
        for c in range(n):
            clauses.append([color[i][c] for i in range(G)])

    # 7. Pair-coverage (Plaisted-Greenbaum, single aux per edge per pair)
    for c1 in range(n):
        for c2 in range(c1 + 1, n):
            pair_aux = []
            for i, j in edges:
                aux = new_var()
                clauses.append([-aux, color[i][c1], color[i][c2]])
                clauses.append([-aux, color[j][c1], color[j][c2]])
                clauses.append([-aux, -color[i][c1], -color[j][c1]])
                clauses.append([-aux, -color[i][c2], -color[j][c2]])
                pair_aux.append(aux)
            clauses.append(pair_aux)

    # 8. Connectivity (BFS reachability from the lex-min active cell)
    if _USE_BFS:
        max_steps = grid_size
        lo = [new_var() for _ in range(G)]
        for i in range(G):
            clauses.append([-lo[i], active[i]])
            for j in range(i):
                clauses.append([-lo[i], -active[j]])
            clauses.append([lo[i], -active[i]] + [active[j] for j in range(i)])
        for i in range(G):
            clauses.append([-lo[i], color[i][0]])
        reach = [[new_var() for _ in range(max_steps)] for _ in range(G)]
        for i in range(G):
            clauses.append([-lo[i], reach[i][0]])
            clauses.append([lo[i], -reach[i][0]])
        for t in range(1, max_steps):
            for i in range(G):
                nbs = adj[i]
                clauses.append([-reach[i][t - 1], reach[i][t]])
                for j in nbs:
                    clauses.append([-active[i], -reach[j][t - 1], reach[i][t]])
                clauses.append([-reach[i][t], reach[i][t - 1], active[i]])
                clauses.append(
                    [-reach[i][t], reach[i][t - 1]]
                    + [reach[j][t - 1] for j in nbs]
                )
        for i in range(G):
            clauses.append([-active[i], reach[i][max_steps - 1]])

    # 9. Cardinality: exactly k active cells
    top_v = var_count[0]
    card_cl = CardEnc.equals(
        active, k, top_id=top_v, encoding=_card_enc(),
    )
    if card_cl:
        top_v = max(max(abs(l) for l in cl) for cl in card_cl)
    all_clauses = clauses + list(card_cl)
    total_vars = max(var_count[0], top_v)
    return all_clauses, total_vars, active, color, cells


def _solve_at_k(n, k, per_term_timeout_s, verbose):
    """Build & solve at fixed (n, k). Returns (status, model_or_None, elapsed).

    status in {'SAT', 'UNSAT', 'TIMEOUT'}.
    """
    n_pairs = n * (n - 1) // 2
    grid_size = _grid_size_for(k, n_pairs)
    print(f"  k={k}: build (grid {grid_size}x{grid_size})...", flush=True)
    t0 = time.time()
    clauses, total_vars, active, color, cells = _build_cnf(n, k, grid_size)
    if verbose:
        print(f"  k={k}: {total_vars} vars, {len(clauses)} clauses", flush=True)

    solver = create_solver(clauses=clauses, name=_SOLVER_NAME)
    try:
        try:
            solver.configure({"restartint": _RESTART_INT})
        except Exception:
            pass
        try:
            if _PHASE_BIAS == "true":
                solver.set_phases([v for v in active])
            elif _PHASE_BIAS == "off":
                pass
            else:
                solver.set_phases([-v for v in active])
        except Exception:
            pass
        # Bug-B (known, 2026-05-15): the in-process PySAT/CaDiCaL
        # solve_limited() is a blocking C call that holds the GIL, so
        # sat_utils.timeouts._heartbeat_loop (a Python thread) is
        # starved and emits no live pulse until this k completes. The
        # rule-#5 fix (external streaming cadical, cf.
        # solve_polyiamond_ext.py) is a deferred daytime A/B task. Until
        # then, make the quiet period transparent: liveness is
        # verifiable via process CPU on PID below.
        print(
            f"  [liveness] k={k} solving in-process (PID {os.getpid()}); "
            f"no pulse until done -- confirm alive via climbing CPU, e.g. "
            f"powershell Get-Process -Id {os.getpid()}. "
            f"start={time.strftime('%H:%M:%S')}",
            flush=True,
        )
        result, elapsed, interrupted = solve_with_timeout(
            solver, per_term_timeout_s or 0,
        )
        wall = time.time() - t0
        if interrupted:
            print(f"  k={k}: TIMEOUT [{wall:.1f}s]", flush=True)
            return STATUS_TIMEOUT, None, wall
        if result is False:
            print(f"  k={k}: UNSAT [{wall:.1f}s]", flush=True)
            return "UNSAT", None, wall
        if result is True:
            model = set(solver.get_model())
            coloring = {}
            for i, cell in enumerate(cells):
                if active[i] in model:
                    for c in range(n):
                        if color[i][c] in model:
                            coloring[cell] = c
                            break
            print(f"  k={k}: SAT [{wall:.1f}s]", flush=True)
            return "SAT", coloring, wall
        print(f"  k={k}: INCONCLUSIVE [{wall:.1f}s]", flush=True)
        return STATUS_TIMEOUT, None, wall
    finally:
        solver.delete()


def _verify_witness(coloring, n):
    """Independent check: connected + every colour pair edge-adjacent."""
    if not coloring:
        return False, "empty coloring"
    cells = set(coloring.keys())
    start = next(iter(cells))
    seen = {start}
    queue = deque([start])
    while queue:
        c = queue.popleft()
        for nb in hex_neighbours(*c):
            if nb in cells and nb not in seen:
                seen.add(nb)
                queue.append(nb)
    if seen != cells:
        return False, "disconnected"
    pairs = set()
    for c, col in coloring.items():
        for nb in hex_neighbours(*c):
            if nb in coloring:
                other = coloring[nb]
                if col != other:
                    pairs.add((min(col, other), max(col, other)))
    expected = n * (n - 1) // 2
    if len(pairs) != expected:
        return False, f"{len(pairs)} colour pairs covered, expected {expected}"
    return True, "ok"


def solve_one(n, *, per_term_timeout_s, verbose):
    """Compute a(n) by ascending search from the analytical lower bound."""
    overall_t0 = time.time()
    lb = _analytical_lower_bound(n)
    print(f"  analytical LB = {lb}", flush=True)

    # n=1 trivial: a(1) = 1
    if n == 1:
        coloring = {(0, 0): 0}
        wall = time.time() - overall_t0
        return SolveResult(
            n=n, value=1, status=STATUS_PROVED, time_s=wall,
            bbox="1 x 1",
            extra={
                "cells": [list(c) for c in coloring],
                "coloring": {f"{q},{r}": col for (q, r), col in coloring.items()},
                "lower_bound_method": "trivial (n=1)",
            },
        )

    deadline = overall_t0 + per_term_timeout_s if per_term_timeout_s else None
    k = lb
    while True:
        if deadline is not None:
            remaining = deadline - time.time()
            if remaining <= 0:
                wall = time.time() - overall_t0
                return SolveResult(
                    n=n, value=None, status=STATUS_TIMEOUT, time_s=wall,
                    error=f"per-term timeout exceeded before SAT at k={k}",
                )
            this_budget = remaining
        else:
            this_budget = 0
        status, coloring, _ = _solve_at_k(n, k, this_budget, verbose)
        if status == STATUS_TIMEOUT:
            wall = time.time() - overall_t0
            return SolveResult(
                n=n, value=None, status=STATUS_TIMEOUT, time_s=wall,
                error=f"timeout at k={k}",
            )
        if status == "SAT":
            ok, why = _verify_witness(coloring, n)
            wall = time.time() - overall_t0
            if not ok:
                return SolveResult(
                    n=n, value=None, status=STATUS_VERIFY_FAILED,
                    time_s=wall, error=why,
                )
            qs = [q for q, _ in coloring]
            rs = [r for _, r in coloring]
            bbox = f"{max(qs) - min(qs) + 1} x {max(rs) - min(rs) + 1}"
            return SolveResult(
                n=n, value=k, status=STATUS_PROVED, time_s=wall,
                bbox=bbox,
                extra={
                    "cells": [list(c) for c in coloring],
                    "coloring": {
                        f"{q},{r}": col for (q, r), col in coloring.items()
                    },
                    "lower_bound_method": (
                        f"UNSAT chain k={lb}..{k - 1} (or analytical exclusion)"
                    ),
                    "analytical_lower_bound": lb,
                },
            )
        # UNSAT -> try the next k
        k += 1


if __name__ == "__main__":
    sys.exit(run_solver_cli(
        seq_id="NEW",
        description=(
            "Minimum connected polyhex with n-colouring covering every "
            "colour pair at an edge"
        ),
        method="Single-formula SAT, ascending k-search from analytical LB",
        software="solve_polyhex.py via sat_utils.solver_cli (CaDiCaL)",
        solve_fn=solve_one,
        default_n="1-5",
        prior_values=PRIOR_VALUES,
        script_path=__file__,
    ))
