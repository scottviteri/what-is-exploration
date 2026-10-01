#!/usr/bin/env python3
"""Exact finite-tree dynamic programming for fixed full-history rewards.

The recurrence is exact algebraically. Float64 results and LP comparisons are
numerical checks, not rational/interval certificates. This module never evaluates
native deficiency or claims to solve a hardest-target search problem.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import time

import numpy as np

HERE = Path(__file__).resolve().parent
ARCHIVE = HERE.parent/'native_objective_benchmark_2026-09-15/results'
OBJECTIVES = ('information', 'brier', 'surprisal', 'first_visit')
TOL = 2e-7


def history_levels(horizon, actions=(0, 1), observations=(0, 1)):
    if horizon < 0 or not actions or not observations:
        raise ValueError('Nonnegative horizon and nonempty finite alphabets required')
    levels = [[()]]
    for _ in range(horizon):
        levels.append([h + ((a, o),) for h in levels[-1]
                       for a in actions for o in observations])
    return levels


def controlled_masses(levels, transitions, emissions, initial=None):
    """Known candidate models; transition then emission, arbitrary world count."""
    transitions, emissions = np.asarray(transitions), np.asarray(emissions)
    worlds, actions, states, _ = transitions.shape
    if initial is None:
        initial = np.zeros((worlds, states)); initial[:, 0] = 1
    initial = np.asarray(initial)
    flow = {(): initial}
    for layer in levels[:-1]:
        for h in layer:
            for a in range(actions):
                pred = np.einsum('ws,wst->wt', flow[h], transitions[:, a])
                for o in range(emissions.shape[-1]):
                    flow[h + ((a, o),)] = pred * emissions[:, a, :, o]
    return {h: f.sum(axis=1) for h, f in flow.items()}


def _inputs(levels, masses, prior=None):
    if not levels or levels[0] != [()]:
        raise ValueError('The first level must contain only the empty history')
    worlds = len(np.asarray(masses[()]))
    if worlds == 0:
        raise ValueError('Nonempty world class required')
    mu = np.full(worlds, 1/worlds) if prior is None else np.asarray(prior, dtype=float)
    if mu.shape != (worlds,) or np.any(mu < 0) or not np.isfinite(mu).all() or abs(mu.sum()-1) > 1e-12:
        raise ValueError('Prior must be a finite probability vector')
    actions = sorted({a for h in levels[1] for a, _ in h}) if len(levels) > 1 else []
    observations = sorted({o for h in levels[1] for _, o in h}) if len(levels) > 1 else []
    if len(levels) > 1 and (not actions or not observations):
        raise ValueError('Nonempty alphabets required at positive horizons')
    if np.max(abs(np.asarray(masses[()])-1)) > 1e-12:
        raise ValueError('Root masses must equal one in every world')
    for depth, layer in enumerate(levels):
        if len(set(layer)) != len(layer) or any(len(h) != depth for h in layer):
            raise ValueError('History levels have duplicates or wrong lengths')
        for h in layer:
            p = np.asarray(masses[h])
            if p.shape != (worlds,) or np.any(p < 0) or not np.isfinite(p).all():
                raise ValueError('Invalid controlled masses')
        if depth < len(levels)-1:
            expected = {h + ((a, o),) for h in layer for a in actions for o in observations}
            if set(levels[depth+1]) != expected:
                raise ValueError('Complete rectangular finite history tree required')
            for h in layer:
                for a in actions:
                    child_sum = sum(np.asarray(masses[h + ((a, o),)]) for o in observations)
                    if np.max(abs(child_sum-np.asarray(masses[h]))) > 1e-10:
                        raise ValueError('Controlled masses violate action-fiber normalization')
    return mu, actions, observations


def terminal_scores(levels, masses, prior=None):
    """Four fixed conditional leaf rewards, aligned exactly with levels[-1].

Information and predictive surprisal use base-two logarithms. Brier is the
category-summed terminal posterior potential gain. First visit counts distinct
observation symbols, with no initial symbol. Null-prior-mass leaves score zero.
    """
    mu, _, _ = _inputs(levels, masses, prior)
    p = np.stack([masses[h] for h in levels[-1]], axis=1)
    m = mu @ p
    post = np.divide(mu[:, None]*p, m[None, :], out=np.zeros_like(p, dtype=float), where=m[None, :] > 0)
    logpost = np.zeros_like(post)
    np.log2(post, out=logpost, where=post > 0)
    positive = mu > 0
    initial_entropy = -float(mu[positive] @ np.log2(mu[positive]))
    surprise = np.zeros_like(m)
    np.log2(m, out=surprise, where=m > 0)
    answer = dict(information=initial_entropy + (post*logpost).sum(axis=0),
                  brier=(post*post).sum(axis=0)-mu@mu,
                  surprisal=-surprise,
                  first_visit=np.asarray([len({o for _, o in h}) for h in levels[-1]], dtype=float))
    for reward in answer.values():
        reward[m == 0] = 0.
    return answer


def plan_terminal_rewards(levels, masses, scores, prior=None, *, tie_tolerance=0., tie_break='uniform'):
    """Globally maximize a fixed leaf reward over full-history policies.

Return rows in flattened levels[:-1] order, weights in flattened levels order,
terminal source law E, attained and optimal expected reward, explicit action/tie
arrays, and Bellman/replay checks. tie_tolerance=0 chooses exact floating-point
maximizers; positive tolerance may lose reward, reported in objective_gap.
    """
    started = time.perf_counter()
    mu, actions, observations = _inputs(levels, masses, prior)
    score = np.asarray(scores, dtype=float)
    if score.shape != (len(levels[-1]),) or not np.isfinite(score).all():
        raise ValueError('One finite conditional score per terminal history required')
    if not np.isfinite(tie_tolerance) or tie_tolerance < 0 or tie_break not in ['uniform', 'first']:
        raise ValueError('Invalid tie handling')
    coefficients = np.asarray([mu @ masses[h] for h in levels[-1]]) * score
    values = dict(zip(levels[-1], coefficients))
    q = {}; masks = {}; pi = {}
    for layer in reversed(levels[:-1]):
        for h in layer:
            q[h] = np.asarray([sum(values[h + ((a, o),)] for o in observations) for a in actions])
            values[h] = float(q[h].max())
            masks[h] = values[h]-q[h] <= tie_tolerance
            pi[h] = masks[h].astype(float)
            if tie_break == 'first':
                pi[h][:] = 0.; pi[h][int(np.flatnonzero(masks[h])[0])] = 1.
            else:
                pi[h] /= pi[h].sum()
    weights = {(): 1.}
    for layer in levels[:-1]:
        for h in layer:
            for i, a in enumerate(actions):
                for o in observations:
                    weights[h + ((a, o),)] = weights[h] * pi[h][i]
    terminal_weights = np.asarray([weights[h] for h in levels[-1]])
    source = np.stack([np.asarray(masses[h])*weights[h] for h in levels[-1]], axis=1)
    attained = float(terminal_weights @ coefficients)
    optimum = float(values[()])
    prefix = [h for layer in levels[:-1] for h in layer]
    histories = [h for layer in levels for h in layer]
    local_gap = sum(weights[h] * (values[h]-float(pi[h]@q[h])) for h in prefix)
    checks = dict(
        bellman_max_residual=max([abs(values[h]-q[h].max()) for h in prefix], default=0.),
        source_stochastic_residual=float(np.max(abs(source.sum(axis=1)-1))),
        expected_reward_replay_residual=abs(float((mu@source)@score)-attained),
        local_global_gap_residual=abs((optimum-attained)-local_gap),
        objective_gap=max(0., optimum-attained),
        negative_objective_gap=max(0., attained-optimum),
        action_row_sum_residual=max([abs(pi[h].sum()-1) for h in prefix], default=0.),
    )
    return dict(rows=np.asarray([pi[h] for h in prefix]).reshape(len(prefix), len(actions)),
                weights=np.asarray([weights[h] for h in histories]), E=source,
                action_values=np.asarray([q[h] for h in prefix]).reshape(len(prefix), len(actions)),
                tie_mask=np.asarray([masks[h] for h in prefix], dtype=bool).reshape(len(prefix), len(actions)),
                values=np.asarray([values[h] for h in histories]), coefficients=coefficients,
                objective=attained, optimal_objective=optimum, checks=checks,
                tie_tolerance=tie_tolerance, tie_break=tie_break,
                numerical_tied_histories=int(sum(mask.sum() > 1 for mask in masks.values())),
                seconds=time.perf_counter()-started)


def _reference_lp(levels, masses, scores, prior=None):
    """Independent realization-weight LP, only for bounded validation."""
    from scipy.optimize import linprog
    from scipy.sparse import coo_matrix
    mu, actions, observations = _inputs(levels, masses, prior)
    histories = [h for layer in levels for h in layer]
    index = {h: i for i, h in enumerate(histories)}
    cost = np.zeros(len(histories))
    cost[[index[h] for h in levels[-1]]] = -np.asarray([mu@masses[h] for h in levels[-1]]) * scores
    rr, cc, vv, rhs = [], [], [], []
    def row(items, value):
        j = len(rhs); rhs.append(value)
        for key, coefficient in items.items():
            rr.append(j); cc.append(index[key]); vv.append(coefficient)
    row({(): 1.}, 1.)
    for layer in levels[:-1]:
        for h in layer:
            row({h: -1.} | {h + ((a, observations[0]),): 1. for a in actions}, 0.)
            for a in actions:
                for o in observations[1:]:
                    row({h + ((a, o),): 1., h + ((a, observations[0]),): -1.}, 0.)
    eq = coo_matrix((vv, (rr, cc)), shape=(len(rhs), len(histories))).tocsr()
    started = time.perf_counter()
    sol = linprog(cost, A_eq=eq, b_eq=rhs, bounds=(0, 1), method='highs',
                  options={'primal_feasibility_tolerance':1e-9, 'dual_feasibility_tolerance':1e-9,
                           'time_limit':120.})
    seconds = time.perf_counter()-started
    if not sol.success:
        raise RuntimeError(sol.message)
    rhs = np.asarray(rhs)
    dual = float(rhs@sol.eqlin.marginals + sol.upper.marginals.sum())
    checks = dict(lp_primal_residual=float(np.max(abs(eq@sol.x-rhs))),
                  lp_bound_violation=float(max(0., -sol.x.min(), sol.x.max()-1)),
                  lp_dual_gap=abs(float(sol.fun)-dual),
                  lp_stationarity=float(np.max(abs(cost-eq.T@sol.eqlin.marginals-sol.lower.marginals-sol.upper.marginals))),
                  lp_lower_dual_sign=float(max(0., -sol.lower.marginals.min())),
                  lp_upper_dual_sign=float(max(0., sol.upper.marginals.max())))
    certificate = dict(cost=cost, solution=sol.x, b_eq=rhs, eq_dual=sol.eqlin.marginals,
                       lower_dual=sol.lower.marginals, upper_dual=sol.upper.marginals,
                       A_eq_data=eq.data, A_eq_indices=eq.indices,
                       A_eq_indptr=eq.indptr, A_eq_shape=eq.shape)
    return dict(objective=-float(sol.fun), seconds=seconds, checks=checks, certificate=certificate)


def _digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def validate(output):
    import scipy
    os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})
    started = time.perf_counter()
    output.mkdir(parents=True, exist_ok=True)
    results, policies, certificates, failures, input_hashes = [], {}, {}, [], {}
    cases = sorted(p for p in ARCHIVE.iterdir() if (p/'model.npz').exists())
    assert len(cases) == 10
    def run(case, horizon, masses, levels, prior, archive=None):
        scores = terminal_scores(levels, masses, prior)
        for objective in OBJECTIVES:
            key = f'{case}__h{horizon}__{objective}'
            try:
                result = plan_terminal_rewards(levels, masses, scores[objective], prior)
                checks = dict(result['checks'])
                row = dict(case=case, horizon=horizon, objective=objective,
                           worlds=len(masses[()]), histories=sum(map(len,levels)),
                           optimal_reward=result['optimal_objective'], attained_reward=result['objective'],
                           dp_seconds=result['seconds'], numerical_tied_histories=result['numerical_tied_histories'],
                           tie_tolerance=result['tie_tolerance'], tie_break=result['tie_break'])
                if archive is not None:
                    archived = next(r for r in archive['optima'] if r['objective'] == objective)
                    ref = -archived['cost']
                    checks['archive_lp_reward_difference'] = abs(result['objective']-ref)
                    row.update(reference='archived_h3_lp', reference_reward=ref,
                               archived_solver_seconds=archived['solver_seconds'])
                else:
                    lp = _reference_lp(levels, masses, scores[objective], prior)
                    checks.update(lp['checks'])
                    checks['fresh_lp_reward_difference'] = abs(result['objective']-lp['objective'])
                    row.update(reference='fresh_independent_lp', reference_reward=lp['objective'], lp_seconds=lp['seconds'])
                    certificates.update({key+'__'+k:v for k,v in lp['certificate'].items()})
                for check, value in checks.items():
                    assert np.isfinite(value) and value <= TOL, (key,check,value)
                row['checks'] = checks; row['status'] = 'passed'; results.append(row)
                for name in ['rows','weights','E','action_values','tie_mask','values','coefficients']:
                    policies[key+'__'+name] = result[name]
            except Exception as exc:
                failures.append(dict(case=case, horizon=horizon, objective=objective, error=repr(exc)))
    for folder in cases:
        model_path = folder/'model.npz'; meta_path = folder/'results.json'
        input_hashes[str(model_path)] = _digest(model_path); input_hashes[str(meta_path)] = _digest(meta_path)
        model = np.load(model_path)
        levels = history_levels(3); masses = controlled_masses(levels,model['T'],model['Z'])
        archive = json.loads(meta_path.read_text())
        run(folder.name,3,masses,levels,None,archive)
    for case in ['sensors_0.1_0.3','hmm_91501_0.2']:
        model = np.load(ARCHIVE/case/'model.npz')
        for horizon in [4,5]:
            levels=history_levels(horizon); masses=controlled_masses(levels,model['T'],model['Z'])
            run(case,horizon,masses,levels,None)
    # General-interface controls include a singleton class, nonuniform priors,
    # zero-prior worlds, and an alphabet other than the benchmark's binary one.
    rng = np.random.default_rng(20260923)
    for worlds, actions, observations, horizon in [(1,2,2,3),(2,2,2,3),(7,2,2,3),(3,3,3,2)]:
        trans=np.ones((worlds,actions,1,1))
        emission=rng.dirichlet(np.ones(observations),size=(worlds,actions,1))
        levels=history_levels(horizon,range(actions),range(observations))
        masses=controlled_masses(levels,trans,emission)
        prior=np.arange(1,worlds+1,dtype=float); prior/=prior.sum()
        if worlds==7:
            prior[0]=0;prior/=prior.sum()
        run(f'generic_w{worlds}_a{actions}_o{observations}',horizon,masses,levels,prior)
    # Positive tie tolerances are explicitly approximate, with the global loss
    # reconstructed from the weighted local Bellman action deficits.
    levels=history_levels(1)
    masses={():np.ones(1)}
    for a in range(2):
        for o in range(2):masses[((a,o),)]=np.array([.5])
    approximate=plan_terminal_rewards(levels,masses,np.array([0.,0.,1e-4,1e-4]),tie_tolerance=2e-4)
    assert abs(approximate['checks']['objective_gap']-5e-5)<1e-12
    assert approximate['checks']['local_global_gap_residual']<1e-12
    np.savez_compressed(output/'objective_dp_policies.npz',**policies)
    np.savez_compressed(output/'objective_dp_lp_certificates.npz',**certificates)
    report=dict(status='passed' if not failures else 'failed', scope='Float64 DP Bellman checks and finite LP comparisons; not interval or Lean proofs.',
                source_sha256=_digest(__file__), input_sha256=input_hashes,
                python=platform.python_version(),numpy=np.__version__,scipy=scipy.__version__,
                validation_tolerance=TOL,seed=20260923,cpu_affinity=sorted(os.sched_getaffinity(0)),results=results,failures=failures,
                approximate_tie_control=approximate['checks'],seconds=time.perf_counter()-started)
    (output/'objective_dp_results.json').write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
    print(json.dumps(dict(status=report['status'],rows=len(results),failures=failures,seconds=report['seconds']),indent=2))
    if failures: raise SystemExit(1)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--validate',action='store_true')
    parser.add_argument('--output',type=Path,default=HERE)
    args=parser.parse_args()
    if args.validate: validate(args.output)
    else: parser.print_help()


if __name__=='__main__': main()
