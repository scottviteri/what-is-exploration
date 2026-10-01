"""Opt-in cuOpt PDLP for bounded planning LPs, with checked CPU IPM fallback.

Run in /tmp/exploration-lp-gpu-venv. The caller serializes GPU jobs and sets
one-core affinity/thread limits. This adapter does not select environments.
"""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import time
from types import SimpleNamespace
import uuid

import numpy as np
from scipy import sparse

import scaling_core

HERE = Path(__file__).resolve().parent


def _save_json(path, value):
    path.write_text(json.dumps(value, indent=2, allow_nan=False)+'\n')


def _save_failed_witness(path, c, Ae, be, Au, bu, bounds, arrays):
    data = dict(cost=c, b_eq=be, b_ub=bu, bounds=bounds, **arrays)
    for key, matrix in [('A_eq', Ae), ('A_ub', Au)]:
        data.update({key+'_data':matrix.data, key+'_indices':matrix.indices,
                     key+'_indptr':matrix.indptr, key+'_shape':np.asarray(matrix.shape)})
    np.savez_compressed(path, **data)


def solve_arrays(c, Ae, be, Au, bu, bounds, time_limit=120):
    """Return SciPy-compatible solution and report; certify before returning.

    ``time_limit`` is the combined GPU-plus-fallback budget. PDLP itself receives
    at most 120 seconds. Only finite-box programs are attempted on the GPU.
    Failure artifacts remain available even if CPU fallback also fails.
    """
    started = time.perf_counter()
    if not np.isfinite(time_limit) or time_limit <= 0:
        raise ValueError('time_limit must be positive and finite')
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S')+'_'+uuid.uuid4().hex[:10]
    attempt_root = Path(os.environ.get('SCALING_GPU_ARTIFACT_ROOT',
                                        str(HERE/'gpu_results'/'adapter_attempts')))
    folder = attempt_root/stamp
    folder.mkdir(parents=True)
    c = np.asarray(c, dtype=np.float64); be = np.asarray(be, dtype=np.float64)
    bu = np.asarray(bu, dtype=np.float64)
    Ae = sparse.csr_matrix(Ae, dtype=np.float64); Au = sparse.csr_matrix(Au, dtype=np.float64)
    lo = np.asarray([-np.inf if a is None else a for a, b in bounds], dtype=np.float64)
    hi = np.asarray([np.inf if b is None else b for a, b in bounds], dtype=np.float64)
    box = np.column_stack([lo, hi]); arrays = {}
    attempt = dict(method='cuopt-pdlp', status='starting', artifact_dir=str(folder),
                   total_budget_seconds=float(time_limit), solver_tolerance=1e-9,
                   certificate_tolerance=scaling_core.TOL,
                   adapter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    stage = 'input-validation'
    try:
        if not all(np.all(np.isfinite(x)) for x in [c, be, bu, Ae.data, Au.data, lo, hi]):
            raise ValueError('GPU adapter requires finite data and finite box bounds')
        if Ae.shape != (len(be), len(c)) or Au.shape != (len(bu), len(c)) or len(lo) != len(c):
            raise ValueError('Inconsistent LP array dimensions')
        if np.any(lo > hi):
            raise ValueError('Inconsistent LP variable bounds')
        stage = 'import'; tick = time.perf_counter()
        from cuopt.linear_programming import DataModel, Solve
        from cuopt.linear_programming.solver_settings import SolverSettings, SolverMethod
        from cuopt.linear_programming.solver.solver_parameters import CUOPT_METHOD
        attempt['import_seconds'] = time.perf_counter()-tick
        attempt['cuopt_version'] = importlib.metadata.version('cuopt-cu12')
        stage = 'model-build'; tick = time.perf_counter()
        matrix = sparse.vstack([Ae, Au], format='csr')
        model = DataModel()
        model.set_csr_constraint_matrix(matrix.data, matrix.indices.astype(np.int32),
                                        matrix.indptr.astype(np.int32))
        model.set_constraint_bounds(np.r_[be, bu])
        model.set_row_types(np.array(['E']*len(be)+['L']*len(bu)))
        model.set_variable_lower_bounds(lo); model.set_variable_upper_bounds(hi)
        model.set_objective_coefficients(c); model.set_maximize(False)
        settings = SolverSettings()
        settings.set_parameter(CUOPT_METHOD, SolverMethod.PDLP)
        settings.set_parameter('num_cpu_threads', 1)
        settings.set_parameter('log_to_console', False)
        settings.set_parameter('log_file', str(folder/'cuopt.log'))
        settings.set_optimality_tolerance(1e-9)
        attempt['model_build_seconds'] = time.perf_counter()-tick
        remaining = time_limit-(time.perf_counter()-started)
        if remaining <= 0:
            raise TimeoutError('Combined time budget exhausted before GPU solve')
        gpu_limit = min(120., remaining)
        settings.set_parameter('time_limit', gpu_limit)
        settings.dump_parameters_to_file(str(folder/'settings.txt'), False)
        attempt['gpu_time_limit_seconds'] = gpu_limit
        stage = 'gpu-solve'; tick = time.perf_counter()
        fit = Solve(model, settings)
        attempt['solve_seconds'] = time.perf_counter()-tick
        attempt['solver_reported_seconds'] = float(fit.get_solve_time())
        attempt['termination_reason'] = str(fit.get_termination_reason())
        stage = 'certificate'; tick = time.perf_counter()
        x = np.asarray(fit.get_primal_solution(), dtype=float)
        row_dual = np.asarray(fit.get_dual_solution(), dtype=float)
        reported_rc = np.asarray(fit.get_reduced_cost(), dtype=float)
        arrays.update(solution=x, row_dual=row_dual, reported_reduced_cost=reported_rc)
        if x.shape != c.shape or row_dual.shape != (len(be)+len(bu),):
            raise ValueError('GPU returned invalid witness dimensions')
        if not np.all(np.isfinite(x)) or not np.all(np.isfinite(row_dual)):
            raise ValueError('GPU returned nonfinite primal/dual witness')
        # A complete box-bound dual can be recovered from row multipliers even
        # when the direct API reports a zero reduced-cost vector.
        y, z = row_dual[:len(be)], row_dual[len(be):]
        rc = c-Ae.T@y-Au.T@z
        attempt['reported_reduced_cost_disagreement'] = (float(np.max(np.abs(reported_rc-rc), initial=0))
                                                        if reported_rc.shape == rc.shape else None)
        if attempt['termination_reason'] != 'Optimal':
            raise RuntimeError('GPU termination was '+attempt['termination_reason'])
        sol = SimpleNamespace(x=x, fun=float(c@x), nit=int(fit.get_lp_stats()['nb_iterations']),
                              success=True, status=0, message='cuOpt PDLP: Optimal; certificate checked',
                              eqlin=SimpleNamespace(marginals=y), ineqlin=SimpleNamespace(marginals=z),
                              lower=SimpleNamespace(marginals=np.maximum(rc, 0)),
                              upper=SimpleNamespace(marginals=np.minimum(rc, 0)))
        checked = scaling_core.check_solution(c, Ae, be, Au, bu, lo, hi, sol)
        if not all(np.isfinite(v) for v in checked['residuals'].values()):
            raise ValueError('Nonfinite numerical certificate')
        attempt.update(status='accepted', certificate=checked.copy(),
                       verification_seconds=time.perf_counter()-tick)
        _save_json(folder/'attempt.json', attempt)
        checked.update(method='cuopt-pdlp', solve_seconds=attempt['solve_seconds'],
                       total_seconds=time.perf_counter()-started, gpu_attempt=attempt,
                       cpu_fallback=False, warnings=[])
        return sol, checked
    except Exception as exc:
        attempt.update(status='rejected', failed_stage=stage, error=repr(exc),
                       elapsed_seconds=time.perf_counter()-started)
        failure_file = folder/'rejected_witness.npz'
        _save_failed_witness(failure_file, c, Ae, be, Au, bu, box, arrays)
        attempt['rejected_witness_file'] = str(failure_file)
        _save_json(folder/'attempt.json', attempt)
    remaining = time_limit-(time.perf_counter()-started)
    if remaining <= 0:
        raise RuntimeError(f'GPU failed and combined budget expired; see {folder}/attempt.json')
    try:
        # The explicit method avoids the GPU dispatch in scaling_core.
        sol, checked = scaling_core.solve_arrays(c, Ae, be, Au, bu, bounds,
                                                 method='highs-ipm', time_limit=remaining)
        checked.update(gpu_attempt=attempt, cpu_fallback=True,
                       total_seconds=time.perf_counter()-started,
                       cpu_fallback_budget_seconds=remaining)
        _save_json(folder/'fallback.json', checked)
        return sol, checked
    except Exception as exc:
        _save_json(folder/'fallback_failure.json', dict(error=repr(exc),
                    remaining_budget_seconds=remaining, elapsed_seconds=time.perf_counter()-started))
        raise RuntimeError(f'GPU and CPU fallback failed; see {folder}') from exc
