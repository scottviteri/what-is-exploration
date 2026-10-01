"""Independent policy/witness replay. Imports NumPy, never a numerical solver."""
import os
for key in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[key] = '1'
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import argparse
import math
import csv
import json
from functools import lru_cache
import numpy as np
from common import HERE, STUDY, TOL, MARGIN, design, pair_classification, read, require, sha, unchanged, write, now
sys.path.insert(0, str(STUDY))
from checked_summary import checked_summary, csv_scalar

def physical_replay(model, policy):
    T, Z = model['T'], model['Z']
    Q, actions, S, next_states = T.shape
    require(Q > 0 and S > 0 and actions == 2 and next_states == S and Z.shape == (Q, 2, S, 2), 'Model dimensions')
    E, rows, leaf = policy['E'], policy['rows'], policy['leaf']
    require(E.shape == (Q, 64) and rows.shape == (21, 2) and leaf.shape == (64,), 'Policy dimensions')
    for name, array in [('T', T), ('Z', Z), ('rows', rows), ('leaf', leaf), ('E', E)]:
        require(np.isfinite(array).all() and np.min(array) >= 0, 'Invalid ' + name)
    for array in (T, Z, rows, E):
        require(np.max(np.abs(array.sum(-1) - 1)) <= 1e-10, 'Probability normalization')
    initial = np.zeros((Q, S)); initial[:, 0] = 1
    nodes = [(initial, 1.)]; index = 0
    for _ in range(3):
        children = []
        for state, weight in nodes:
            choice = rows[index]; index += 1
            for action in range(2):
                predicted = np.einsum('qi,qij->qj', state, T[:, action])
                for obs in range(2):
                    children.append((predicted * Z[:, action, :, obs], weight * choice[action]))
        nodes = children
    actual = np.stack([state.sum(1) * weight for state, weight in nodes], axis=1)
    weights = np.asarray([weight for _, weight in nodes])
    residual = max(float(np.max(np.abs(actual - E))), float(np.max(np.abs(weights - leaf))))
    require(residual <= 1e-10, 'Independent physical-policy replay failed')
    return E.copy(), residual

def replay_witness(E, F, G, alpha, b, saved_lower, saved_upper):
    require(E.ndim == F.ndim == 2 and E.shape[0] == F.shape[0], 'World alignment')
    Q, X = E.shape; Y = F.shape[1]
    require(min(Q, X, Y) > 0 and G.shape == (X, Y) and alpha.shape == (Q,) and b.shape == (Q, Y), 'Witness dimensions')
    require(all(np.isfinite(a).all() for a in (E, F, G, alpha, b)), 'Nonfinite witness')
    require(all(math.isfinite(float(v)) for v in (saved_lower, saved_upper)), 'Nonfinite saved bounds')
    require(min(float(E.min()), float(F.min())) >= 0 and
            max(float(np.max(abs(E.sum(1) - 1))), float(np.max(abs(F.sum(1) - 1)))) <= 1e-10,
            'Experiment probabilities')
    feasibility = max(float(np.max(abs(G.sum(1) - 1))), float(max(0., -G.min())),
                      abs(float(alpha.sum()) - 1), float(max(0., -alpha.min())),
                      float(max(0., -b.min())), float(np.maximum(b - alpha[:, None], 0).max()))
    require(feasibility <= 1e-12, 'Infeasible decoder or dual')
    # Scalar math.fsum reductions are independent of the producer's BLAS reductions.
    upper = max(math.fsum(abs(math.fsum(float(E[q, x]) * float(G[x, y]) for x in range(X))
                               - float(F[q, y])) for y in range(Y)) / 2 for q in range(Q))
    lower = math.fsum(float(F[q, y]) * float(b[q, y]) for q in range(Q) for y in range(Y)) - \
        math.fsum(max(math.fsum(float(E[q, x]) * float(b[q, y]) for q in range(Q))
                      for y in range(Y)) for x in range(X))
    disagreement = max(abs(lower - float(saved_lower)), abs(upper - float(saved_upper)))
    require(disagreement <= 1e-12, 'Saved witness values disagree')
    require(lower <= upper + 1e-10 and upper - lower <= TOL, 'Unclosed numerical bracket')
    return dict(lower=lower, upper=upper, gap=upper-lower, feasibility=feasibility,
                replay_disagreement=disagreement)

@lru_cache(maxsize=1)
def context():
    primary, bindings = checked_summary(STUDY / 'summary/summary.json')
    plan_path = HERE / 'PLAN.json'; plan = read(plan_path)
    require(len(plan['models']) == len(set(plan['models'])) == 12, 'Wrong model count')
    require(plan['jobs'] == design(plan['models']), 'Frozen grid differs from complete design')
    unchanged(plan['source_sha256']); unchanged(plan['design_input_sha256'])
    inventory = read(STUDY / 'MODELS.json')
    return dict(primary=primary, index={(r['model'],r['method'],r['budget_seconds']):r for r in primary['endpoints']},
                models={m['id']:m for m in inventory['models']}, jobs={j['job_id']:j for j in plan['jobs']},
                bindings={**bindings, str(plan_path):sha(plan_path), **plan['source_sha256'], **plan['design_input_sha256']})

def check_request(request, job_id, ctx):
    expected = ctx['jobs'][job_id]
    require(all(request.get(k) == v for k,v in expected.items()), 'Request job/direction mismatch')
    model = ctx['models'][expected['model']]
    model_path = Path(model['path']); model_path = (model_path if model_path.is_absolute() else STUDY/model_path).resolve()
    native = ctx['index'][expected['model'],expected['method'],40]
    baseline = ctx['index'][expected['model'],expected['baseline'],40]
    for row in (native,baseline):
        require(row.get('planning_check_status') == 'passed' and row.get('available_seconds') is not None and row['available_seconds'] <= 40, 'Ineligible saved policy')
    source,target = (native,baseline) if expected['direction']=='native_to_baseline' else (baseline,native)
    expected_paths = {'model_path':model_path,'source_policy':Path(source['policy_path']).resolve(),
                      'target_policy':Path(target['policy_path']).resolve(), 'primary_execution':STUDY/'ANALYSIS_EXECUTION.json'}
    frozen = ctx['primary']['metadata']['input_sha256']
    for name,path in expected_paths.items():
        require(request.get(name) == str(path) and str(path) in request['input_sha256'], 'Unbound or misdirected '+name)
        expected_hash = sha(path) if name=='primary_execution' else frozen.get(str(path))
        require(expected_hash is not None and request['input_sha256'][str(path)]==expected_hash, 'Primary/request binding mismatch')
    require(request['input_sha256'][str(model_path)]==model['sha256'], 'Wrong model inventory binding')
    for path,digest in ctx['bindings'].items():
        require(request['input_sha256'].get(path)==digest, 'Request omitted checked context')

def primary_pair(pair, ctx):
    a=ctx['index'][pair['model'],pair['method'],40]; b=ctx['index'][pair['model'],pair['baseline'],40]
    if not (a['comparison_eligible'] and b['comparison_eligible']):
        return 'unavailable',None,None
    lo=a['audit_lower']-b['audit_upper'];hi=a['audit_upper']-b['audit_lower']
    result='native_win' if hi < -MARGIN else 'native_loss' if lo > MARGIN else 'unresolved'
    return result,lo,hi

def check_csv(path, records):
    with path.open(newline='') as stream:
        reader=csv.DictReader(stream);saved=list(reader);headers=reader.fieldnames
    require(headers is not None and len(headers)==len(set(headers)), 'CSV column mismatch')
    require(set(headers)==set().union(*(set(r) for r in records)), 'CSV/JSON columns differ')
    require(saved==[{k:csv_scalar(r.get(k)) for k in headers} for r in records], 'CSV/JSON rows differ')

def check_job(folder):
    folder = Path(folder); request_path = folder / 'request.json'
    request_hash = sha(request_path); request = read(request_path)
    check_request(request, folder.name, context())
    unchanged(request['input_sha256'])
    require(read(request['primary_execution'])['state'] == 'passed', 'Primary analysis not passed')
    with np.load(request['model_path'], allow_pickle=False) as model:
        with np.load(request['source_policy'], allow_pickle=False) as policy:
            E, source_residual = physical_replay(model, policy)
        with np.load(request['target_policy'], allow_pickle=False) as policy:
            F, target_residual = physical_replay(model, policy)
    witness_path = folder / 'witness.npz'; witness_hash = sha(witness_path)
    with np.load(witness_path, allow_pickle=False) as w:
        require(np.array_equal(E, w['E']) and np.array_equal(F, w['F']), 'Saved experiments differ from bound policies')
        checked = replay_witness(E, F, w['G'], w['alpha'], w['b'], w['lower'], w['upper'])
    unchanged(request['input_sha256'])
    require(sha(request_path) == request_hash and sha(witness_path) == witness_hash, 'Job evidence changed while checking')
    return dict(status='validated', **checked, source_replay_residual=source_residual,
                target_replay_residual=target_residual, request_sha256=request_hash,
                witness_sha256=witness_hash)

def check_pair(pair, forward, reverse, ctx):
    require(pair['classification'] == pair_classification(forward, reverse), 'Pair classification mismatch')
    require(all(pair[k] == forward[k] == reverse[k] for k in ('model', 'method', 'baseline')), 'Pair identity mismatch')
    require(pair['forward_job']==forward['job_id'] and pair['reverse_job']==reverse['job_id'] and pair['budget_seconds']==40, 'Paired direction IDs')
    for prefix,direction in [('forward',forward),('reverse',reverse)]:
        for field in ('lower','upper'):
            require(pair[prefix+'_'+field]==direction.get(field), 'Pair interval binding')
    classification,lo,hi=primary_pair(pair,ctx)
    require((pair['native_audit_classification'],pair['native_audit_difference_lower'],pair['native_audit_difference_upper'])==(classification,lo,hi), 'Scalar audit join mismatch')

def check_results(folder):
    folder = Path(folder); summary_path = folder / 'SUMMARY.json'
    summary_hash = sha(summary_path); summary = read(summary_path)
    unchanged(summary['input_sha256']); plan = read(HERE / 'PLAN.json'); ctx=context()
    require(plan['jobs'] == design(plan['models']), 'Plan coverage mismatch')
    for path,digest in ctx['bindings'].items():
        require(summary['input_sha256'].get(path)==digest, 'Summary omitted checked context')
    expected = plan['jobs']; rows = summary['directions']; pairs = summary['pairs']
    require(len(rows) == 288 and len(pairs) == 144, 'Incomplete requested coverage')
    require([{k: r[k] for k in e} for r, e in zip(rows, expected)] == expected, 'Direction queue identity/order mismatch')
    validated = 0; failures = []
    for row in rows:
        if row['status'] == 'validated':
            try:
                checked = check_job(folder / 'jobs' / row['job_id'])
                for key in ('lower', 'upper', 'gap', 'feasibility'):
                    require(abs(checked[key] - row[key]) <= 1e-12, 'Summary/checker mismatch: ' + key)
                for key in ('request_sha256', 'witness_sha256'):
                    require(checked[key] == row[key], 'Job evidence identity changed')
                validated += 1
            except Exception as error:
                failures.append(dict(job_id=row['job_id'], error=repr(error)))
    for i, pair in enumerate(pairs):
        forward, reverse = rows[2*i:2*i+2]
        check_pair(pair,forward,reverse,ctx)
    check_csv(folder/'DIRECTIONS.csv',rows);check_csv(folder/'PAIRS.csv',pairs)
    unchanged(summary['input_sha256']); require(sha(summary_path) == summary_hash, 'Summary changed during check')
    return dict(status='passed' if not failures else 'failed', checked_utc=now(),
                requested_directions=288, requested_pairs=144, validated_directions=validated,
                unavailable_or_failed_directions=288-validated, errors=failures,
                summary_sha256=summary_hash, checker_sha256=sha(__file__),
                scope='Independent solver-free physical-policy, original-probability witness and fixed-coverage replay; floating-point evidence only')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--results', type=Path, required=True)
    args = parser.parse_args()
    report = check_results(args.results)
    write(args.results / 'CHECKS.json', report)
    print(report)
    raise SystemExit(0 if report['status'] == 'passed' else 1)
