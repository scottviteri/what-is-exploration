#!/usr/bin/env python3
"""Shared-decoder diagnostic on saved native-optimal collectors only.

This minimizes over ONE decoder simultaneously for the selected collectors.
It is not their worst policy-specific deficiency and not a bound for the full
native-optimal face. Selection uses audited floating point deficiencies.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import sys
import time

import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location('sharp_search_shared_diagnostic', HERE/'search.py')
SEARCH = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = SEARCH
SPEC.loader.exec_module(SEARCH)
BASE = SEARCH.BASE


def run():
    start = time.monotonic()
    folder = HERE.parent/'results_h4'
    index = folder/'results.json'
    parent = json.loads(index.read_text())
    weights = dict(zip(('L','R','tagged','LR','LLL','RRR'),(.2,.2,.1,.1,.1,.1)))
    selected, sources = [], []
    for row in parent['optima'] + parent['rows']:
        if row['noise'] != [.1,.1]:
            continue
        native = sum(weights[k]*row['target_deficiencies'][k] for k in weights)
        if native > .0072 + 1e-10:
            continue
        path = folder/row['policy_path']
        with np.load(path) as artifact:
            E = artifact['source_kernel'].copy()
        # Retain every numerically different source; no approximate merging.
        matching = next((i for i, old in enumerate(sources) if np.array_equal(E,old)), None)
        if matching is None:
            matching = len(sources)
            sources.append(E)
        selected.append({'id':row['id'], 'native_weighted_cost':native,
                         'source_number':matching, 'path':str(path.relative_to(HERE.parent)),
                         'sha256':SEARCH.digest(path),
                         'saved_adaptive_deficiency':row['target_deficiencies']['adaptive_L']})
    E = np.asarray(sources)
    keep = np.flatnonzero(E.sum(axis=(0,1)) > 0)
    target = next(t for t in BASE.target_library((.1,.1)) if t['name']=='adaptive_L')
    groups_by_key = {}
    for y,h in enumerate(target['signals']):
        key = (h[0][1], h[1][1]+h[2][1])
        groups_by_key.setdefault(key,[]).append(y)
    groups = list(groups_by_key.values())
    T = np.stack([target['kernel'][:,g].sum(axis=1) for g in groups],axis=1)
    for g in groups:
        assert np.max(np.abs(target['kernel'][:,g]-target['kernel'][:,g[0],None])) < 1e-15
    lp = BASE.LP()
    error = lp.var(1.)
    G = np.asarray([[lp.var() for _ in groups] for _ in keep])
    for row in G:
        lp.row({i:1 for i in row},1,True)
    for source in E:
        for theta in range(4):
            absolute = []
            for y in range(len(groups)):
                e = lp.var(); absolute.append(e)
                terms = {G[j,y]:source[theta,h] for j,h in enumerate(keep) if source[theta,h]}
                lp.row(terms | {e:-1},T[theta,y])
                lp.row({i:-v for i,v in terms.items()} | {e:-1},-T[theta,y])
            lp.row({i:.5 for i in absolute} | {error:-1},0)
    ae,au = lp.matrix(lp.eq),lp.matrix(lp.ub)
    be,bu = (np.asarray([b for _,b in rows]) for rows in (lp.eq,lp.ub))
    solve_start = time.monotonic()
    sol = linprog(lp.cost,A_eq=ae,b_eq=be,A_ub=au,b_ub=bu,bounds=lp.bounds,
                  method=SEARCH.METHOD,options=SEARCH.OPTIONS)
    assert sol.success, sol.message
    lo,hi = np.asarray(lp.bounds).T
    dual = float(be@sol.eqlin.marginals+bu@sol.ineqlin.marginals+
                 lo@sol.lower.marginals+hi@sol.upper.marginals)
    residuals = {'equality':float(np.max(abs(ae@sol.x-be),initial=0)),
                 'inequality':float(np.max(au@sol.x-bu,initial=0)),
                 'bounds':float(np.max(np.maximum(lo-sol.x,sol.x-hi),initial=0)),
                 'stationarity':float(np.max(abs(np.asarray(lp.cost)-ae.T@sol.eqlin.marginals-
                                          au.T@sol.ineqlin.marginals-sol.lower.marginals-sol.upper.marginals),initial=0)),
                 'duality_gap':abs(float(sol.fun)-dual)}
    assert max(residuals.values()) < 1e-8
    decoder = sol.x[G]
    errors = np.sum(abs(E[:,:,keep]@decoder-T),axis=2)/2
    assert abs(errors.max()-sol.fun)<1e-8
    arrays = BASE.certificate_arrays(lp,sol,ae,au,be,bu)
    arrays.update(source_kernels=E,source_indices=keep,target_kernel=T,
                  full_target_kernel=target['kernel'],decoder=decoder,decoder_indices=G,
                  source_world_errors=errors)
    out = HERE/'shared_decoder_diagnostic.npz'
    np.savez_compressed(out,**arrays)
    report = {'status':'completed_float64_diagnostic','scope':
              'One common decoder on selected saved collectors; not worst policy-specific deficiency and not a full-face bound.',
              'source_sha256':SEARCH.digest(__file__),'search_sha256':SEARCH.digest(HERE/'search.py'),
              'parent_compute_sha256':SEARCH.digest(HERE.parent/'compute.py'),
              'parent_results_sha256':SEARCH.digest(index),'H':4,'noise':[.1,.1],
              'native_cost_selection_bound':.0072,'selection_tolerance':1e-10,
              'selected_collectors':selected,'distinct_exact_source_arrays':len(sources),
              'active_union_histories':len(keep),'target_compression_groups':groups,
              'compressed_output_keys':list(groups_by_key),'common_decoder_error':float(sol.fun),
              'common_decoder_dual_lower':dual,'largest_saved_policy_specific_error':
              max(r['saved_adaptive_deficiency'] for r in selected),
              'source_world_errors':errors.tolist(),'residuals':residuals,
              'variables':len(lp.cost),'equalities':len(lp.eq),'inequalities':len(lp.ub),
              'solver_seconds':time.monotonic()-solve_start,'run_seconds':time.monotonic()-start,
              'certificate_path':out.name,'certificate_sha256':SEARCH.digest(out)}
    SEARCH.write_json(HERE/'shared_decoder_diagnostic.json',report)
    print(json.dumps({k:report[k] for k in ('common_decoder_error','common_decoder_dual_lower',
          'largest_saved_policy_specific_error','distinct_exact_source_arrays','active_union_histories',
          'residuals','run_seconds')},indent=2))


if __name__ == '__main__':
    run()
