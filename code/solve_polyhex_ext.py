"""External-cadical streaming polyhex solver (real timeout + pulse + LRAT).

Rule-#5 fix for Bug B. The in-process path (solve_polyhex.py) runs the
solve via PySAT's blocking C ``solve_limited()``, which holds the GIL.
That starves BOTH helper threads in ``sat_utils.timeouts``: the
heartbeat (no live pulse) AND the ``threading.Timer`` that is supposed
to call ``solver.interrupt()`` -- so ``--per-term-timeout`` never
fires. Evidence: an n=9 run with a 3 h per-term cap ran ~13 h on a
single k and never timed out (2026-05-15).

This solver shells out to a real cadical binary via
``sat_utils.drat_tools.solve_external_cadical_streaming``. The timeout
is an OS-level subprocess kill (not a GIL-starved Python timer), the
``-v`` lines are a real line-buffered pulse, and LRAT is emitted on the
same pass.

It reuses solve_polyhex's own ``_build_cnf`` / ``_analytical_lower_bound``
/ ``_grid_size_for`` / ``_verify_witness``, so for any (n, k) the CNF
and the accept/reject decision are by construction identical to the
in-process solver -- only the engine that decides SAT/UNSAT changes.
Output JSON shape matches solve_polyhex.py so verify_method1.py and
the OEIS pipeline consume it unchanged.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone

sys.stdout.reconfigure(line_buffering=True)

_HERE = os.path.dirname(os.path.abspath(__file__))
_PROJECT_DIR = os.path.dirname(_HERE)
_PAPER_DIR = os.path.dirname(_PROJECT_DIR)
if _PAPER_DIR not in sys.path:
    sys.path.insert(0, _PAPER_DIR)
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

# Reuse the in-process solver's constraint generation, analytical
# bounds, and independent witness verifier verbatim -- this is what
# makes the ext path's answers identical by construction.
from solve_polyhex import (  # noqa: E402
    _analytical_lower_bound,
    _build_cnf,
    _grid_size_for,
    _verify_witness,
)

from figure_gen_utils.pipeline_timeouts import SOLVER_ITERATE_TIMEOUT_S  # noqa: E402
from figure_gen_utils.solver_log import STATUS_TIMEOUT  # noqa: E402
from sat_utils.cnf_tools import export_cnf  # noqa: E402
from sat_utils.drat_tools import (  # noqa: E402
    check_lrat,
    solve_external_cadical_streaming,
)

STATUS_PROVED = "PROVED"


def _model_to_coloring(model_literals, n, active, color, cells):
    """cadical `v` literals -> {(q, r): colour}. Identical reconstruction
    to solve_polyhex._solve_at_k (range(n), active[i], color[i][c])."""
    model_set = set(model_literals)
    coloring = {}
    for i, cell in enumerate(cells):
        if active[i] in model_set:
            for c in range(n):
                if color[i][c] in model_set:
                    coloring[cell] = c
                    break
    return coloring


def _lrat_check(cnf_path, lrat_path):
    """Run lrat-check via the shared sat_utils.drat_tools.check_lrat
    (binary resolution, timeout, graceful-degrade handled there).
    Thin adapter preserving this project's (verified, info) contract."""
    if not os.path.exists(lrat_path) or os.path.getsize(lrat_path) == 0:
        return False, "lrat missing/empty"
    r = check_lrat(cnf_path, lrat_path)
    if r.get("verified"):
        return True, "VERIFIED"
    if r.get("error"):
        return False, str(r["error"])[:160]
    tail = (r.get("stdout_tail", "") + r.get("stderr_tail", ""))[-160:]
    return False, f"rc={r.get('exit_code')} {tail}"


def _solve_at_k(n, k, *, per_term_timeout_s, work_dir, emit_lrat):
    """Decide (n, k) via external streaming cadical. Real OS-level
    timeout. Returns a dict mirroring the in-process result shape."""
    n_pairs = n * (n - 1) // 2
    grid = _grid_size_for(k, n_pairs)
    print(f"  k={k}: build (grid {grid}x{grid})...", flush=True)
    clauses, total_vars, active, color, cells = _build_cnf(n, k, grid)
    print(f"  k={k}: {total_vars} vars, {len(clauses)} clauses", flush=True)

    cnf_path = os.path.normpath(os.path.join(work_dir, f"polyhex_n{n}_k{k}.cnf"))
    lrat_path = os.path.normpath(
        os.path.join(work_dir, f"polyhex_n{n}_k{k}.lrat")
    )
    for stale in (cnf_path, lrat_path):
        if os.path.exists(stale):
            try:
                os.remove(stale)
            except OSError:
                pass
    export_cnf(clauses, total_vars, cnf_path)

    t0 = time.time()
    res = solve_external_cadical_streaming(
        cnf_path,
        lrat_path=lrat_path if emit_lrat else None,
        timeout_seconds=per_term_timeout_s,
        verbose=True,
        pulse_label=f"n={n} k={k}" + (" lrat" if emit_lrat else ""),
    )
    elapsed = time.time() - t0

    if res.get("timed_out"):
        print(f"  k={k}: TIMEOUT [{elapsed:.1f}s] (OS-level cap fired)",
              flush=True)
        return {"status": STATUS_TIMEOUT, "elapsed_s": elapsed,
                "coloring": None, "bbox": None, "cnf_path": cnf_path,
                "lrat_path": None, "lrat_verified": None}

    sat = res.get("satisfiable")
    if sat is True:
        coloring = _model_to_coloring(
            res.get("model") or [], n, active, color, cells
        )
        ok, why = _verify_witness(coloring, n)
        if not ok:
            print(f"  k={k}: SAT but witness REJECTED ({why})", flush=True)
            return {"status": "SAT_INVALID", "elapsed_s": elapsed,
                    "coloring": None, "bbox": None, "cnf_path": cnf_path,
                    "lrat_path": None, "lrat_verified": None,
                    "error": f"witness rejected: {why}"}
        qs = [q for q, _ in coloring]
        rs = [r for _, r in coloring]
        bbox = f"{max(qs) - min(qs) + 1} x {max(rs) - min(rs) + 1}"
        print(f"  k={k}: SAT [{elapsed:.1f}s] bbox {bbox}", flush=True)
        return {"status": "SAT", "elapsed_s": elapsed, "coloring": coloring,
                "bbox": bbox, "cnf_path": cnf_path, "lrat_path": None,
                "lrat_verified": None}

    if sat is False:
        lrat_verified = None
        if emit_lrat:
            lrat_verified, info = _lrat_check(cnf_path, lrat_path)
            print(
                f"  k={k}: UNSAT [{elapsed:.1f}s] LRAT="
                f"{'VERIFIED' if lrat_verified else 'FAILED'}"
                + ("" if lrat_verified else f" ({info})"),
                flush=True,
            )
        else:
            print(f"  k={k}: UNSAT [{elapsed:.1f}s]", flush=True)
        return {"status": "UNSAT", "elapsed_s": elapsed, "coloring": None,
                "bbox": None, "cnf_path": cnf_path,
                "lrat_path": lrat_path if (emit_lrat and lrat_verified) else None,
                "lrat_verified": lrat_verified}

    print(f"  k={k}: INCONCLUSIVE [{elapsed:.1f}s] rc={res.get('exit_code')} "
          f"err={res.get('error')}", flush=True)
    return {"status": STATUS_TIMEOUT, "elapsed_s": elapsed, "coloring": None,
            "bbox": None, "cnf_path": cnf_path, "lrat_path": None,
            "lrat_verified": None, "error": res.get("error") or "inconclusive"}


def solve_one(n, *, per_term_timeout_s, work_dir, emit_lrat_for_lower_bound):
    """a(n) by ascending search from the analytical LB; optional LRAT
    cert for the UNSAT@(a(n)-1) lower-bound step."""
    print(f"[n={n} START]", flush=True)
    if n == 1:
        return {"n": 1, "value": 1, "status": STATUS_PROVED, "elapsed": 0.0,
                "bbox": "1 x 1", "cells": [[0, 0]], "coloring": {"0,0": 0},
                "lower_bound_method": "trivial (n=1)",
                "solver": "external cadical streaming"}

    lb = _analytical_lower_bound(n)
    print(f"  analytical LB = {lb}", flush=True)

    k = lb
    while True:
        res = _solve_at_k(n, k, per_term_timeout_s=per_term_timeout_s,
                          work_dir=work_dir, emit_lrat=False)
        st = res["status"]
        if st == "SAT":
            sat_at, sat_res = k, res
            break
        if st == "UNSAT":
            k += 1
            if k - lb > 25:
                return {"n": n, "value": None, "status": STATUS_TIMEOUT,
                        "elapsed": res["elapsed_s"],
                        "error": "ascending search exceeded LB+25"}
            continue
        return {"n": n, "value": None, "status": STATUS_TIMEOUT,
                "elapsed": res["elapsed_s"],
                "error": res.get("error", st)}

    lower_bound_method = (
        f"UNSAT chain k={lb}..{sat_at - 1}" if sat_at > lb
        else f"analytical LB = {lb} (k={lb} SAT; no UNSAT step)"
    )
    lrat_status, lrat_bytes = "skipped", 0
    if emit_lrat_for_lower_bound and sat_at > lb:
        lb_k = sat_at - 1
        print(f"  re-solving k={lb_k} with LRAT for the lower bound "
              f"(a(n) >= {sat_at} requires UNSAT@{lb_k}).", flush=True)
        lr = _solve_at_k(n, lb_k, per_term_timeout_s=per_term_timeout_s,
                         work_dir=work_dir, emit_lrat=True)
        if lr["status"] == "UNSAT" and lr["lrat_verified"] is True:
            lrat_status = "VERIFIED"
            lrat_bytes = (os.path.getsize(lr["lrat_path"])
                          if lr.get("lrat_path") else 0)
            lower_bound_method = f"UNSAT@{lb_k} (LRAT VERIFIED, {lrat_bytes}B)"
        elif lr["status"] == "UNSAT":
            lrat_status = "FAIL"
            lower_bound_method = f"UNSAT@{lb_k} (LRAT lrat-check FAILED)"
        else:
            lrat_status = "INCONCLUSIVE"
            lower_bound_method = f"UNSAT@{lb_k} re-solve -> {lr['status']}"
    elif emit_lrat_for_lower_bound and sat_at == lb:
        lrat_status = "n/a (analytic LB; no UNSAT step to certify)"

    coloring = sat_res["coloring"]
    cells_list = [[q, r] for (q, r) in sorted(coloring.keys())]
    coloring_serial = {f"{q},{r}": col for (q, r), col in coloring.items()}
    return {"n": n, "value": sat_at, "status": STATUS_PROVED,
            "elapsed": sat_res["elapsed_s"], "bbox": sat_res["bbox"],
            "cells": cells_list, "coloring": coloring_serial,
            "lower_bound_method": lower_bound_method,
            "analytical_lower_bound": lb, "lrat_status": lrat_status,
            "lrat_bytes": lrat_bytes,
            "solver": "external cadical streaming"}


def _parse_n_spec(spec):
    out = []
    for piece in spec.split(","):
        piece = piece.strip()
        if not piece:
            continue
        if "-" in piece:
            a, b = piece.split("-", 1)
            out.extend(range(int(a), int(b) + 1))
        else:
            out.append(int(piece))
    return out


def main():
    p = argparse.ArgumentParser(
        description="External-cadical polyhex solver (streaming + LRAT)."
    )
    p.add_argument("--n", default="1-7")
    p.add_argument("--per-term-timeout", type=int,
                   default=SOLVER_ITERATE_TIMEOUT_S)
    p.add_argument("--json", default=None)
    p.add_argument("--log", default=None)
    p.add_argument("--work-dir", default=None)
    p.add_argument("--no-lrat", action="store_true",
                   help="Skip the UNSAT@(a(n)-1) LRAT re-solve (sanity "
                        "/ A-B checks only).")
    args = p.parse_args()

    work_dir = args.work_dir or os.path.join(
        _PROJECT_DIR, "research", "ext-cadical")
    os.makedirs(work_dir, exist_ok=True)
    json_path = args.json or os.path.join(
        _PROJECT_DIR, "research", "solver-ext-results.json")
    log_path = args.log or os.path.join(
        _PROJECT_DIR, "research", "solver-ext-log.txt")

    log_f = open(log_path, "w", encoding="utf-8", buffering=1)

    class _Tee:
        def __init__(self, *s):
            self._s = s

        def write(self, x):
            for st in self._s:
                try:
                    st.write(x)
                    st.flush()
                except Exception:
                    pass

        def flush(self):
            for st in self._s:
                try:
                    st.flush()
                except Exception:
                    pass

    real = sys.stdout
    sys.stdout = _Tee(real, log_f)
    try:
        print("=" * 70, flush=True)
        print("OEIS NEW polyhex -- external cadical streaming", flush=True)
        print("=" * 70, flush=True)
        print(f"  Date: {datetime.now(timezone.utc).date().isoformat()}",
              flush=True)
        print(f"  Per-term timeout: {args.per_term_timeout}s (OS-level)",
              flush=True)
        print(f"  Range: {args.n}   Work dir: {work_dir}", flush=True)

        # Read-merge-write: never clobber an existing results file.
        results = {}
        if os.path.exists(json_path):
            try:
                with open(json_path, encoding="utf-8") as f:
                    results = json.load(f)
            except (OSError, json.JSONDecodeError):
                results = {}

        for n in _parse_n_spec(args.n):
            t0 = time.time()
            res = solve_one(
                n, per_term_timeout_s=args.per_term_timeout,
                work_dir=work_dir,
                emit_lrat_for_lower_bound=not args.no_lrat,
            )
            res["elapsed"] = res.get("elapsed", time.time() - t0)
            results[str(n)] = res
            with open(json_path, "w", encoding="utf-8") as f:
                json.dump(results, f, indent=2)
            tag = (STATUS_PROVED if res.get("status") == STATUS_PROVED
                   else "FAIL")
            print(f"[n={n} DONE  a({n})={res.get('value', '?')}  {tag}  "
                  f"{res.get('elapsed', 0):.1f}s]", flush=True)
        print(f"  Wrote: {json_path}", flush=True)
    finally:
        sys.stdout = real
        log_f.close()


if __name__ == "__main__":
    main()
