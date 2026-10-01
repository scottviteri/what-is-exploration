"""Prepared CPU bridge for later, separately authorized numerical validation.

Importing this module is solver-free. Dry runs never call load_backend. No CLI
launches solvers. The backend path is pinned and every imported project dependency
is checked. Solver-backed paths have NOT been run in this research pass.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
import hashlib
import importlib.util
import json
import math
import os
import sys
import time

from adaptive_weights import (Context, Cut, CutCache, MasterBound, Objective,
    PolicyIntervals, TargetBinding, canonical, digest, finite_certificate)

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
FROZEN = ROOT / 'Paper/research/target_selection_2026-09-23/decomposition_research'
PROJECT_MODULES = ('scaling_core', 'fast_decoder', 'certified_decoder')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def verify_lock():
    lock = json.loads((HERE/'DEPENDENCIES.json').read_text())
    if lock['schema'] != 'jw-frozen-backend-v1':
        raise ValueError('Unknown backend lock')
    for row in lock['files']:
        path = ROOT / row['path']
        if sha(path) != row['sha256']:
            raise ValueError('Frozen dependency changed: ' + row['path'])
    return lock


def load_backend(*, execution_authorized=False):
    if not execution_authorized:
        raise RuntimeError('Numerical execution is outside this research phase; use dry_run.py')
    verify_lock()
    occupied = [m for m in PROJECT_MODULES if m in sys.modules]
    if occupied:
        raise RuntimeError('Use a fresh dedicated process: dependency names occupied: ' + repr(occupied))
    if any(m in sys.modules for m in ('numpy', 'scipy', 'highspy')):
        raise RuntimeError('Set thread limits in a fresh process before numeric imports')
    for name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
        os.environ[name] = '1'
    sys.dont_write_bytecode = True
    name = '_jw_frozen_decomposition_' + sha(FROZEN/'experiment.py')[:16]
    spec = importlib.util.spec_from_file_location(name, FROZEN/'experiment.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    for name in PROJECT_MODULES:
        loaded = sys.modules.get(name)
        expected = (FROZEN/'deps'/(name + '.py')).resolve()
        if loaded is None or Path(loaded.__file__).resolve() != expected:
            raise RuntimeError('Project dependency escaped frozen directory: ' + name)
    verify_lock()
    module.core.OPTIONS = module.core.OPTIONS | {'threads': 1}
    return module


def array_hash(array):
    """Representation identity; callers do not get to relabel changed geometry."""
    h = hashlib.sha256()
    h.update(str(array.dtype).encode()); h.update(repr(tuple(array.shape)).encode())
    h.update(array.tobytes(order='C'))
    return h.hexdigest()


def context_for(g, model_sha256, world_labels):
    geometry = {'raw': array_hash(g.raw), 'leaf_index': array_hash(g.leaf_index),
        'flow_data': array_hash(g.flow.data), 'flow_indices': array_hash(g.flow.indices),
        'flow_indptr': array_hash(g.flow.indptr), 'flow_shape': g.flow.shape,
        'flow_rhs': array_hash(g.flow_rhs), 'decisions': g.decisions,
        'layers': g.layers}
    return Context(model_sha256, digest(geometry), digest(world_labels),
                   len(g.layers)-1, g.flow.shape[1])


def target_binding(target_id, kernel, record='full-action-observation-history-v1'):
    return TargetBinding(target_id, array_hash(kernel), record)


def numeric_q(x):
    """Exact identity of a finite binary float, not an exact mathematical certificate."""
    x = float(x)
    if not math.isfinite(x):
        raise ValueError('Nonfinite numerical evidence')
    return F.from_float(x)


def prepare_master(cache, objective):
    """Pure manifest of cut reuse and current costs; no previous aggregate bound."""
    retained = cache.for_objective(objective)
    return {'schema': 'jw-retained-master-v1', 'context_id': objective.context_id,
        'objective_id': objective.identity, 'costs': [str(w) for w in objective.weights],
        'target_bindings': canonical(objective.targets),
        'reused_cut_count': len(retained),
        'cuts': [dict(target=i, **canonical(c)) for i, c in retained],
        'required_fresh': ['master-dual-bound', 'replayed-policy-target-intervals'],
        'inherited_aggregate_lower': None, 'inherited_aggregate_upper': None,
        'execution_enabled': False}


def solve_reweighted(backend, g, targets, objective, cache, *, model_sha256,
                     world_labels, execution_authorized=False, seconds=40.,
                     max_iterations=200, gap=1e-6, witness_store=None):
    """Future numerical path: retain target cuts but reset all aggregate bounds.

    `targets` are aligned frozen-backend dictionaries containing actual kernels.
    This adapter implements finite weighted objectives and their rich-background
    truncations. Direct minimax remains available in the unmodified frozen
    prototype; the robust background epigraph and reward-face constraints are
    intentionally NOT implemented here. Returned bounds are numerical and require
    the independent full audit described in PROTOCOL.md before scientific use.
    """
    if not execution_authorized:
        raise RuntimeError('Execution disabled for the current research assignment')
    verify_lock()
    context = context_for(g, model_sha256, world_labels)
    if context != cache.context or context.identity != objective.context_id:
        raise ValueError('Backend geometry does not match cache/objective')
    if len(targets) != len(objective.targets):
        raise ValueError('Target count mismatch')
    for source, binding in zip(targets, objective.targets):
        if array_hash(source['kernel']) != binding.kernel_sha256:
            raise ValueError('Target kernel changed or target order is stale')
    if not math.isfinite(seconds) or not 0 < seconds or max_iterations < 1 or not 0 < gap < 1:
        raise ValueError('Explicit positive resource and gap limits required')
    if witness_store is None:
        witness_store = {}
    started = time.perf_counter(); deadline = started + seconds
    np = backend.np
    # The exact intended costs and the floats actually sent to the LP differ.
    # Account for that difference in both lower and upper bounds.
    numeric_weights = tuple(numeric_q(float(w)) for w in objective.weights)
    cost_shift = sum((min(F(0), exact-numerical) for exact, numerical in
                      zip(objective.weights, numeric_weights)), F(0))
    numeric_targets = [dict(t, weight=float(w)) for t, w in zip(targets, objective.weights)]
    lower = F(0); best = None; upper = None; iterations = []; evidence = []
    status = 'incomplete_iteration_cap'
    for iteration in range(max_iterations):
        if time.perf_counter() >= deadline:
            status = 'incomplete_time_cap'; break
        retained = cache.for_objective(objective)
        # Imported caches are not trusted merely because their identity strings
        # match. Reconstruct each cut from its saved dual on current full geometry.
        for index, cut in retained:
            witness = witness_store.get(cut.witness_sha256)
            if witness is None or digest(witness) != cut.witness_sha256:
                raise ValueError('Cached cut lacks its original, matching dual witness')
            intercept, slope, _ = backend.make_cut(g, numeric_targets[index]['kernel'], witness)
            if numeric_q(intercept) != cut.intercept or tuple(numeric_q(x) for x in slope) != cut.slope:
                raise ValueError('Cached cut does not reconstruct under the frozen backend')
        cuts = [dict(target=i, intercept=float(c.intercept),
                     slope=np.array([float(s) for s in c.slope])) for i, c in retained]
        # This path accepts only cuts emitted as original binary-float coefficients
        # by this bridge; rounding arbitrary exact coefficients needs another audit.
        if any(numeric_q(float(c.intercept)) != c.intercept or
               any(numeric_q(float(s)) != s for s in c.slope) for _, c in retained):
            raise ValueError('Non-binary-exact cached cut requires outward rounding support')
        try:
            E, rows, leaf, deficits, report, arrays = backend.master(g, numeric_targets,
                'native_weighted', cuts, max(.01, min(10., deadline-time.perf_counter())))
            master_ready = time.perf_counter()
            if master_ready > deadline:
                raise TimeoutError('Master certificate arrived after the declared budget')
            lower = max(lower, numeric_q(report['dual']) + cost_shift)
            # Preserve a newly used lower-bound witness even if the subsequent
            # target oracle times out. This record belongs to the current objective.
            evidence_record = {'master_arrays': arrays, 'cut_prefix': cuts,
                               'E': E, 'rows': rows, 'oracle': None}
            evidence.append(evidence_record)
            evaluated = backend.oracle(g, E, rows, numeric_targets, deadline)
            evidence_record['oracle'] = evaluated
            oracle_ready = time.perf_counter()
            evidence_record['available_seconds'] = oracle_ready-started
            if oracle_ready > deadline:
                raise TimeoutError('Decoder evidence arrived after the declared budget; endpoint rejected')
            policy = PolicyIntervals(context.identity, array_hash(rows), tuple(
                (binding.identity,
                 max(F(0), min(F(1), numeric_q(evaluated['lower'][i])-numeric_q(backend.TOL))),
                 max(F(0), min(F(1), numeric_q(evaluated['upper'][i])+numeric_q(backend.TOL))))
                for i, binding in enumerate(objective.targets)),
                'frozen floating decoder witnesses; TOL padding; requires independent audit')
            selected_upper = policy.aggregate(objective)[1]
            if upper is None or selected_upper < upper:
                upper = selected_upper
                best = dict(policy=policy, E=E, rows=rows, leaf=leaf, evaluated=evaluated)
            # Retain all new target cuts, including those from this final iteration.
            count_before = len(cache._cuts)
            for c in evaluated['cuts']:
                binding = objective.targets[c['target']]
                witness = {'alpha': c['alpha'].tolist(), 'b': c['b'].tolist()}
                witness_store[digest(witness)] = witness
                cache.add(binding, Cut(context.identity, binding.identity,
                    numeric_q(c['intercept']), tuple(numeric_q(x) for x in c['slope']),
                    digest(witness), 'frozen floating dual; unvalidated new bridge'))
            record = {'iteration': iteration, 'objective_id': objective.identity,
                'lower': str(lower), 'upper': str(upper), 'selected_gap': str(upper-lower),
                'evidence_available_seconds': oracle_ready-started,
                'master_available_seconds': master_ready-started,
                'master': report, 'cuts_before': count_before, 'cuts_after': len(cache._cuts)}
            iterations.append(record)
            # Save each master certificate and decoder witness, including raw arrays.
            # Future caller MUST export these; a digest alone is not a proof.
            evidence_record['oracle'] = evaluated
            if lower > upper:
                status = 'failed_bound_order'; break
            if float(upper-lower) <= gap:
                status = 'converged_numerically'; break
            if len(cache._cuts) == count_before:
                status = 'incomplete_no_new_cuts'; break
        except Exception as exc:
            status = 'incomplete_time_cap' if isinstance(exc, TimeoutError) else 'failed'
            iterations.append({'error': repr(exc), 'objective_id': objective.identity})
            break
    certificate = None
    if best is not None and upper is not None and lower > upper:
        status = 'failed_bound_order'
    if best is not None and status != 'failed_bound_order':
        certificate = finite_certificate(objective, best['policy'], MasterBound(
            context.identity, objective.identity, lower,
            'fresh floating master dual plus exact cost-rounding correction; audit pending'))
    return {'status': status, 'objective': objective.manifest(), 'certificate': certificate,
        'best': best, 'iterations': iterations, 'evidence_to_export': evidence,
        'cache': cache.manifest(), 'witness_store': witness_store, 'seconds': time.perf_counter()-started,
        'budget_scope': 'backend soft cap; late evidence rejected; future harness must enforce hard process cap',
        'validation_status': 'new bridge not solver-validated'}
