#!/usr/bin/env python3
"""Frozen finite objective-selection benchmark; no learner or infinite claim."""
import argparse
import copy
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
import time

import numpy as np

HERE = Path(__file__).resolve().parent
CORE_PATH = HERE.parent / 'noisy_diagnostic_transfer_2026-09-13/compute.py'
spec = importlib.util.spec_from_file_location('native_benchmark_core', CORE_PATH)
core = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = core
spec.loader.exec_module(core)
LP = core.LP
H = 3
PAD = 1e-8
FRACTIONS = [0., .01, .05]
OBJECTIVES = ['native_weighted', 'native_minimax', 'information', 'brier',
              'surprisal', 'first_visit']
WORLDS = np.array(list(itertools.product(range(2), repeat=2)))
LABELS = np.array([[0, 0, 1, 1], [0, 1, 0, 1], [0, 1, 1, 0],
                   [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
PURPOSES = ['mean_seven', 'U', 'V', 'parity']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, allow_nan=False) + '\n')


def environments():
    result = []
    def add(name, family, errors, states):
        T = np.zeros((4, 2, states, states))
        Z = np.zeros((4, 2, states, 2))
        for w, (u, v) in enumerate(WORLDS):
            for a in range(2):
                for s in range(states):
                    dest = (0 if family == 'sensors' else
                            (min(s+1, 2) if a == 0 else 0) if family == 'delayed' else
                            a+1 if s == 0 else s)
                    T[w, a, s, dest] = 1
                    bit = (u, v)[a] if family != 'irreversible' else (u if s == 1 else v)
                    err = errors[a] if family != 'irreversible' else errors[0 if s == 1 else 1]
                    if family == 'delayed' and a == 0 and s < 2:
                        Z[w, a, s] = [.5, .5]
                    else:
                        Z[w, a, s, bit] = 1-err
                        Z[w, a, s, 1-bit] = err
        result.append(dict(name=name, family=family, T=T, Z=Z))
    for errors in [(.1, .1), (.1, .3), (.25, .25)]:
        add('sensors_' + '_'.join(map(str, errors)), 'sensors', errors, 1)
    for errors in [(.1, .1), (.25, .1)]:
        add('delayed_' + '_'.join(map(str, errors)), 'delayed', errors, 3)
    for errors in [(.1, .1), (.1, .3)]:
        add('irreversible_' + '_'.join(map(str, errors)), 'irreversible', errors, 3)
    for seed, concentration in [(91501, .2), (91502, 1.), (91503, 5.)]:
        rng = np.random.default_rng(seed)
        T = rng.dirichlet(np.full(3, concentration), size=(4, 2, 3))
        Z = rng.dirichlet(np.full(2, concentration), size=(4, 2, 3))
        result.append(dict(name=f'hmm_{seed}_{concentration}', family='hmm', T=T, Z=Z))
    return result


def levels(H):
    result = [[()]]
    for _ in range(H):
        result.append([h+((a, o),) for h in result[-1] for a in range(2) for o in range(2)])
    return result


def masses(T, Z, lev):
    first = np.zeros((4, T.shape[-1])); first[:, 0] = 1
    f = {(): first}
    for layer in lev[:-1]:
        for h in layer:
            for a in range(2):
                pred = np.einsum('ws,wst->wt', f[h], T[:, a])
                for o in range(2):
                    f[h+((a, o),)] = pred * Z[:, a, :, o]
    return {h: v.sum(axis=1) for h, v in f.items()}


def target_library(T, Z):
    targets = []
    for length in [1, 2, 3]:
        lev = levels(length); p = masses(T, Z, lev)
        for word in itertools.product(range(2), repeat=length):
            keep = [h for h in lev[-1] if tuple(a for a, _ in h) == word]
            targets.append(dict(name=''.join('LR'[a] for a in word),
                                weight=.1 if length == 1 else .05,
                                kernel=np.array([p[h] for h in keep]).T,
                                signals=keep))
    for length in [1, 3]:
        lev = levels(length); p = masses(T, Z, lev)
        keep = [h for h in lev[-1] if len(set(a for a, _ in h)) == 1]
        targets.append(dict(name=f'tagged_{length}', weight=.05,
                            kernel=.5*np.array([p[h] for h in keep]).T,
                            signals=keep))
    assert len(targets) == 16 and abs(sum(t['weight'] for t in targets)-.9) < 1e-12
    for t in targets:
        assert np.max(abs(t['kernel'].sum(axis=1)-1)) < 1e-12
    return targets


def pure_weights(lev):
    result = []
    for choices in itertools.product(range(2), repeat=2**H-1):
        weights = []
        for h in lev[-1]:
            code = 0; possible = True
            for depth, (a, o) in enumerate(h):
                if a != choices[2**depth-1+code]:
                    possible = False; break
                code = 2*code+o
            weights.append(float(possible))
        result.append(weights)
    return np.array(result)


def reward_coefficients(lev, p):
    result = {k: [] for k in OBJECTIVES[2:]}
    for h in lev[-1]:
        m = p[h].mean(); post = p[h]/p[h].sum()
        ent = -sum(x*np.log2(x) for x in post if x > 0)
        result['information'].append(m*(2-ent))
        result['brier'].append(m*(float(post@post)-.25))
        result['surprisal'].append(-m*np.log2(m))
        result['first_visit'].append(m*len(set(o for _, o in h)))
    return {k: np.array(v) for k, v in result.items()}


def decision_values(E):
    return np.array([sum(max(E[label == b, x].sum()/4 for b in [0, 1])
                         for x in range(E.shape[1])) for label in LABELS])


def program(lev, p, targets, objective, rewards):
    lp = LP()
    w = {h: lp.var() for layer in lev for h in layer}
    x = {}
    lp.row({w[()]: 1}, 1, True)
    for layer in lev[:-1]:
        for h in layer:
            row = {w[h]: -1}
            for a in range(2):
                x[h, a] = lp.var(); row[x[h, a]] = 1
                for o in range(2):
                    lp.row({w[h+((a, o),)]: 1, x[h, a]: -1}, 0, True)
            lp.row(row, 0, True)
    allocations = []; deficits = []
    if objective.startswith('native'):
        mm = lp.var(1.) if objective == 'native_minimax' else None
        for target in targets:
            Q = target['kernel']; Y = Q.shape[1]
            d = lp.var(target['weight'] if mm is None else 0.); deficits.append(d)
            if mm is not None:
                lp.row({d: 1, mm: -1}, 0)
            z = np.array([[lp.var() for _ in range(Y)] for h in lev[-1]])
            allocations.append(z)
            for j, h in enumerate(lev[-1]):
                lp.row({int(i): 1 for i in z[j]} | {w[h]: -1}, 0, True)
            for theta in range(4):
                errors = []
                for y in range(Y):
                    e = lp.var(); errors.append(e)
                    row = {int(z[j, y]): p[h][theta] for j, h in enumerate(lev[-1])}
                    lp.row(row | {e: -1}, Q[theta, y])
                    lp.row({i: -v for i, v in row.items()} | {e: -1}, -Q[theta, y])
                lp.row({i: .5 for i in errors} | {d: -1}, 0)
    else:
        for h, c in zip(lev[-1], rewards[objective]):
            lp.cost[w[h]] = -float(c)
    return lp, w, x, allocations, deficits


def replay(lev, p, x, sol):
    weights = {(): 1.}; rows = []
    for layer in lev[:-1]:
        for h in layer:
            a = np.maximum([sol.x[x[h, i]] for i in range(2)], 0)
            a = a/a.sum() if a.sum() > 1e-13 else np.array([.5, .5])
            rows.append(a)
            for i in range(2):
                for o in range(2):
                    weights[h+((i, o),)] = weights[h]*a[i]
    E = np.array([weights[h]*p[h] for h in lev[-1]]).T
    assert np.max(abs(E.sum(axis=1)-1)) < 1e-9
    return E, np.array(rows), np.array([weights[h] for layer in lev for h in layer])


def add_evaluation(lp, w, lev, p, purpose):
    selected = range(7) if purpose == 'mean_seven' else [PURPOSES.index(purpose)-1]
    for k in selected:
        for h in lev[-1]:
            v = lp.var(1/len(selected))
            for b in [0, 1]:
                c = float(p[h][LABELS[k] == b].sum()/4)
                lp.row({w[h]: c, v: -1}, 0)


def run_case(case, out):
    folder = out/case['name']; folder.mkdir(parents=True, exist_ok=True)
    result_path = folder/'results.json'
    if result_path.exists():
        saved = json.loads(result_path.read_text())
        if saved.get('status') == 'complete':
            assert saved['code_sha256'] == digest(__file__), 'Refusing stale resume'
            return saved
    start = time.monotonic()
    T, Z = case['T'], case['Z']; lev = levels(H); p = masses(T, Z, lev)
    targets = target_library(T, Z); rewards = reward_coefficients(lev, p)
    raw = np.array([p[h] for h in lev[-1]]).T
    pure = pure_weights(lev)
    meta = dict(name=case['name'], family=case['family'], H=H, status='running',
                code_sha256=digest(__file__), core_sha256=digest(CORE_PATH),
                protocol_sha256=digest(HERE/'PROTOCOL.md'), optima=[], endpoints=[], failures=[])
    arrays = {'T': T, 'Z': Z, 'source_controlled_masses': raw, 'labels': LABELS}
    arrays.update({f'target_{j}': t['kernel'] for j, t in enumerate(targets)})
    np.savez_compressed(folder/'model.npz', **arrays)
    write_json(folder/'targets.json', [{k: v for k, v in t.items() if k != 'kernel'} for t in targets])
    # A complete finite vertex cover gives the maximum of convex native losses.
    cache_path = folder/'pure_controls.npz'
    if cache_path.exists():
        cache = np.load(cache_path)
        assert str(cache['code_sha256']) == digest(__file__)
        pure_d = cache['deficiencies']; pure_v = cache['decision_values']
    else:
        pure_d = []; pure_v = []
        for i, weight in enumerate(pure):
            E = raw*weight
            ds = [core.fixed_deficiency(E, t['kernel'])[0] for t in targets]
            pure_d.append(ds); pure_v.append(decision_values(E))
            if i % 32 == 0:
                print(case['name'], 'pure controls', i, '/128', flush=True)
        pure_d = np.array(pure_d); pure_v = np.array(pure_v)
        np.savez_compressed(cache_path, weights=pure, deficiencies=pure_d,
                            decision_values=pure_v, code_sha256=digest(__file__))
    weights = np.array([t['weight'] for t in targets])
    maxima = {'native_weighted': float(np.max(pure_d@weights)),
              'native_minimax': float(np.max(pure_d))}
    maxima.update({key: float(-np.min(pure@r)) for key, r in rewards.items()})
    meta['maximal_costs'] = maxima
    meta['unconstrained_best_mean'] = float(pure_v.mean(axis=1).max())
    meta['unconstrained_best_each'] = pure_v.max(axis=0).tolist()
    meta['uniform_decision_values'] = decision_values(raw/(2**H)).tolist()
    optimum_E = {}
    for objective in OBJECTIVES:
        try:
            template, w, x, allocations, deficits = program(lev, p, targets, objective, rewards)
            optimum_sol, record = core.solve(template, folder/f'{objective}_optimum.npz')
            E, rows, rw = replay(lev, p, x, optimum_sol)
            optimum = float(optimum_sol.fun); width = max(0., maxima[objective]-optimum)
            if objective in rewards:
                expected = -float(np.max(pure@rewards[objective]))
                assert abs(expected-optimum) < 2e-8, (objective, expected, optimum)
            else:
                actual_ds = [core.fixed_deficiency(E, t['kernel'])[0] for t in targets]
                actual = max(actual_ds) if objective == 'native_minimax' else float(weights@actual_ds)
                assert abs(actual-optimum) < 3e-8, (objective, actual, optimum)
            optimum_E[objective] = E
            np.savez_compressed(folder/f'{objective}_optimum_policy.npz', E=E, rows=rows,
                                weights=rw, terminal_w_indices=[w[h] for h in lev[-1]])
            record.update(objective=objective, cost=optimum, range=width,
                          decision_values=decision_values(E).tolist())
            meta['optima'].append(record)
            for fraction in FRACTIONS:
                eta = fraction*width
                for purpose in PURPOSES:
                    lp = copy.deepcopy(template)
                    original = np.array(lp.cost)
                    lp.row({i: float(c) for i, c in enumerate(original) if c}, optimum+eta+PAD)
                    lp.cost = [0.]*len(lp.cost)
                    add_evaluation(lp, w, lev, p, purpose)
                    name = f'{objective}_f{fraction}_{purpose}'
                    sol, rec = core.solve(lp, folder/f'{name}.npz')
                    E, rows, rw = replay(lev, p, x, sol)
                    values = decision_values(E)
                    value = float(values.mean() if purpose == 'mean_seven' else values[PURPOSES.index(purpose)-1])
                    assert abs(value-sol.fun) < 3e-8
                    raw_cost = float(original@sol.x[:len(original)])
                    assert raw_cost <= optimum+eta+PAD+3e-8
                    policy_data = dict(E=E, rows=rows, weights=rw,
                                       terminal_w_indices=[w[h] for h in lev[-1]])
                    if allocations:
                        for j, z in enumerate(allocations):
                            policy_data[f'allocations_{j}'] = sol.x[z]
                        policy_data['deficit_upper'] = sol.x[deficits]
                    np.savez_compressed(folder/f'{name}_policy.npz', **policy_data)
                    rec.update(objective=objective, fraction=fraction, eta=eta,
                               threshold=optimum+eta+PAD, original_cost_upper=raw_cost,
                               purpose=purpose, value=value, decision_values=values.tolist())
                    meta['endpoints'].append(rec)
            write_json(result_path, meta)
            print(case['name'], objective, 'complete', round(time.monotonic()-start, 2), 's', flush=True)
        except Exception as exc:
            meta['failures'].append(dict(objective=objective, error=repr(exc)))
            write_json(result_path, meta)
            raise
    pairs = []
    for objective in OBJECTIVES[1:]:
        forward = core.fixed_deficiency(optimum_E['native_weighted'], optimum_E[objective])[0]
        reverse = core.fixed_deficiency(optimum_E[objective], optimum_E['native_weighted'])[0]
        pairs.append(dict(objective=objective, native_to_baseline=forward, baseline_to_native=reverse))
    meta['optimum_pair_witnesses'] = pairs
    meta['status'] = 'complete'; meta['seconds'] = time.monotonic()-start
    write_json(result_path, meta)
    return meta


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--case', default='all')
    parser.add_argument('--output', type=Path, default=HERE/'results')
    args = parser.parse_args(); args.output.mkdir(parents=True, exist_ok=True)
    cases = environments()
    write_json(args.output/'design.json', dict(code_sha256=digest(__file__),
               protocol_sha256=digest(HERE/'PROTOCOL.md'), core_sha256=digest(CORE_PATH),
               H=H, cases=[{k:v for k,v in c.items() if k not in ['T','Z']} for c in cases],
               objectives=OBJECTIVES, fractions=FRACTIONS, purposes=PURPOSES))
    for case in cases:
        if args.case in ['all', case['name']]:
            run_case(case, args.output)


if __name__ == '__main__':
    main()
