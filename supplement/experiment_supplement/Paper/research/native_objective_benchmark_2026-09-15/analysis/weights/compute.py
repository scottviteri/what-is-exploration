#!/usr/bin/env python3
"""Weight sensitivity of fixed audited records under target-order constraints."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

import numpy as np


HERE = Path(__file__).resolve().parent
BENCH = HERE.parent.parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


b = load('weight_sensitivity_benchmark', BENCH / 'compute.py')
a = load('weight_sensitivity_auditor', BENCH / 'audit.py')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    out = HERE / 'results'
    out.mkdir(exist_ok=True)
    design = json.loads((BENCH / 'results/design.json').read_text())
    assert design['code_sha256'] == digest(BENCH / 'compute.py')
    assert design['protocol_sha256'] == digest(BENCH / 'PROTOCOL.md')
    assert design['core_sha256'] == digest(b.CORE_PATH)
    report = dict(
        scope='Post-hoc reweighting of fixed saved optimum pairs; no collector reoptimization.',
        code_sha256=digest(Path(__file__)),
        plan_sha256=digest(HERE / 'PLAN.md'),
        parent_compute_sha256=digest(BENCH / 'compute.py'),
        parent_auditor_sha256=digest(BENCH / 'audit.py'),
        order_threshold=1e-8, uniform_component=.01, cases=[])
    for case in design['cases']:
        folder = BENCH / 'results' / case['name']
        model = np.load(folder / 'model.npz')
        meta = json.loads((folder / 'targets.json').read_text())
        targets = []
        for index, target in enumerate(meta):
            kernel = np.array([
                a.literal_probability(model['T'], model['Z'], h)
                for h in target['signals']]).T
            if target['name'].startswith('tagged'):
                kernel *= .5
            a.check('literal_target', kernel - model[f'target_{index}'])
            targets.append(kernel)
        records = {
            objective: np.load(folder / f'{objective}_optimum_policy.npz')['E']
            for objective in ['native_weighted', 'brier']}
        errors = {
            objective: np.array([a.decoder_error(record, target) for target in targets])
            for objective, record in records.items()}
        order_errors = np.array([
            [a.decoder_error(source, target) for target in targets]
            for source in targets])
        n = len(targets)
        order = order_errors <= report['order_threshold']
        for threshold in [1e-9, 1e-7]:
            assert np.array_equal(order, order_errors <= threshold), (case, threshold)
        for i in range(n):
            assert order[i, i]
            for j in range(n):
                for k in range(n):
                    assert not (order[i, j] and order[j, k]) or order[i, k]
        difference = errors['native_weighted'] - errors['brier']
        original_weights = np.array([t['weight'] for t in meta])
        original_weights /= original_weights.sum()
        row = dict(
            name=case['name'], family=case['family'], targets=[t['name'] for t in meta],
            target_deficiencies=order_errors.tolist(), record_errors={k:v.tolist() for k,v in errors.items()},
            native_minus_brier_by_target=difference.tolist(),
            original_weights=original_weights.tolist(),
            original_gap=float(original_weights @ difference),
            original_weight_order_violation=max(
                [original_weights[j]-original_weights[i]
                 for i in range(n) for j in range(n) if order[i,j]]),
            least_positive_target_deficiency=float(order_errors[~order].min()) if (~order).any() else None,
            order_relations=int(order.sum()), extremes=[])
        for name, sign in [('minimum', 1.), ('maximum', -1.)]:
            lp = b.LP()
            variables = [lp.var(sign*cost, (.01/n, 1.)) for cost in difference]
            lp.row({i:1. for i in variables}, 1., True)
            for i in range(n):
                for j in range(n):
                    if i != j and order[i,j]:
                        lp.row({variables[j]:1., variables[i]:-1.}, 0.)
            path = out / f'{case["name"]}_{name}.npz'
            solution, certificate = b.core.solve(lp, path)
            a.certificate(path)
            weights = solution.x
            gap = float(weights @ difference)
            a.check('weight_gap_objective', gap-sign*solution.fun)
            a.check('weight_sum', weights.sum()-1)
            a.check('weight_floor', np.maximum(.01/n-weights, 0))
            a.check('weight_order', np.array([
                max(0., weights[j]-weights[i]) for i in range(n) for j in range(n) if order[i,j]]))
            row['extremes'].append(dict(name=name, gap=gap, weights=weights.tolist()))
        report['cases'].append(row)
        print(case['name'], 'gap range', [r['gap'] for r in row['extremes']], flush=True)
    report['verification'] = dict(status='passed', checks=a.COUNT,
                                  max_errors=a.ERRORS, maximum_residual=max(a.ERRORS.values()))
    (HERE / 'results.json').write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print(report['verification'], flush=True)


if __name__ == '__main__':
    main()
