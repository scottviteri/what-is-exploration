"""One isolated, bounded same-time deficiency solve; writes only its job folder."""
import os
for key in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[key] = '1'
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import argparse
import time
import traceback
import numpy as np
from common import BACKEND, CPU, CAP, TOL, read, require, unchanged, write

def replay(model, policy):
    T, Z = model['T'], model['Z']
    rows, saved, leaf = policy['rows'], policy['E'], policy['leaf']
    Q, _, S, _ = T.shape
    require(T.shape == (Q, 2, S, S) and Z.shape == (Q, 2, S, 2), 'Model shape')
    require(rows.shape == (21, 2) and saved.shape == (Q, 64) and leaf.shape == (64,), 'Policy shape')
    for array in (T, Z, rows, saved, leaf):
        require(np.isfinite(array).all() and np.min(array) >= 0, 'Invalid probability')
    for array in (T, Z, rows, saved):
        require(np.max(abs(array.sum(-1) - 1)) <= 1e-10, 'Nonstochastic array')
    E = np.zeros((Q, 64)); weights = np.zeros(64)
    for x in range(64):
        state = np.zeros((Q, S)); state[:, 0] = 1
        weight = 1.; prefix = 0
        for depth in range(3):
            digit = (x // 4 ** (2 - depth)) % 4
            a, o = divmod(digit, 2)
            weight *= rows[(4 ** depth - 1) // 3 + prefix, a]
            state = np.array([(state[q] @ T[q, a]) * Z[q, a, :, o] for q in range(Q)])
            prefix = 4 * prefix + digit
        weights[x] = weight; E[:, x] = weight * state.sum(1)
    require(max(np.max(abs(E - saved)), np.max(abs(weights - leaf))) <= 1e-10, 'Physical replay mismatch')
    return saved.copy()

def run(folder):
    started = time.perf_counter()
    request = read(folder / 'request.json')
    unchanged(request['input_sha256'])
    require(read(request['primary_execution'])['state'] == 'passed', 'Primary analysis has not passed')
    require(CPU in os.sched_getaffinity(0), 'CPU25 unavailable')
    os.sched_setaffinity(0, {CPU})
    with np.load(request['model_path'], allow_pickle=False) as model:
        with np.load(request['source_policy'], allow_pickle=False) as policy:
            E = replay(model, policy)
        with np.load(request['target_policy'], allow_pickle=False) as policy:
            F = replay(model, policy)
    # Solver import is deliberately after the primary-state and input guards.
    sys.path.insert(0, str(BACKEND))
    from certified_decoder import StableDecoder
    remaining = CAP - (time.perf_counter() - started)
    require(remaining > 0, 'Setup exhausted worker budget')
    decoder = StableDecoder(E, F.shape[1], time_limit=remaining)
    decoder.inner.time_limit = max(.001, CAP - (time.perf_counter() - started))
    report, witness = decoder.solve(F)
    keep = witness['source_indices']
    require(np.array_equal(keep, np.flatnonzero(np.max(E, axis=0) > 0)), 'Dropped nonzero source column')
    G = np.full((E.shape[1], F.shape[1]), 1 / F.shape[1])
    G[keep] = witness['decoder']
    alpha, b = witness['alpha'], witness['b']
    upper = float(np.max(np.abs(E @ G - F).sum(1) / 2))
    lower = float((F * b).sum() - np.max(E.T @ b, axis=1).sum())
    require(np.isfinite([lower, upper]).all() and lower <= upper + 1e-10 and upper - lower <= TOL,
            'Original-probability gap failed')
    unchanged(request['input_sha256'])
    with (folder / 'witness.npz').open('wb') as handle:
        np.savez_compressed(handle, E=E, F=F, G=G, alpha=alpha, b=b, lower=lower, upper=upper)
    write(folder / 'solve.json', dict(status='solved', lower=lower, upper=upper,
                                    seconds=time.perf_counter() - started, backend=report))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--job', type=Path, required=True)
    args = parser.parse_args(); folder = args.job.resolve()
    try:
        run(folder)
    except Exception as error:
        write(folder / 'failure.json', dict(error=repr(error), traceback=traceback.format_exc()))
        raise
