#!/usr/bin/env python3
"""Independently replay the count-extension near-optimal comparison.

Does not import either planner, the comparison producer, or the certificate
verifier. Reuses the immutable parent policy audits and recomputes original
optimum-based outer budgets, certificate portfolio values, and eligibility of
every reported lower witness. Certificate feasibility is audited separately by
audit_counts.py; this script does not solve any policy or deficiency LP.
"""
from __future__ import annotations

import csv
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
WEIGHTS = {'L': .2, 'R': .2, 'tagged': .1, 'LR': .1, 'LLL': .1, 'RRR': .1}
TOLERANCE = 2e-7


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    rows = list(csv.DictReader((HERE/'comparison.csv').open()))
    certificates = json.loads((HERE/'results.json').read_text())['certificates']
    optimum_paths = [PARENT/sub/'results.json' for sub in ('results', 'results_h4')]
    parent_audit_paths = [PARENT/name for name in ('audit_h3.json', 'audit_h4.json')]
    optima = sum((json.loads(path.read_text())['optima'] for path in optimum_paths), [])
    parent_audits = [json.loads(path.read_text()) for path in parent_audit_paths]
    assert all(audit['status'] == 'passed' for audit in parent_audits)
    collectors = sum((audit['rows'] for audit in parent_audits), [])
    by_id = {row['id']: row for row in collectors}
    assert len(by_id) == len(collectors) == 984
    errors, cases = {}, set()

    def check(name, actual, expected):
        error = abs(float(actual)-float(expected))
        errors[name] = max(errors.get(name, 0.), error)
        assert error <= TOLERANCE, (name, error, actual, expected)

    def upper(name, actual, bound):
        check(name, max(0., float(actual)-float(bound)), 0.)

    for row in rows:
        noise = json.loads(row['noise'])
        objective, horizon, eta = row['objective'], int(row['H']), float(row['eta'])
        assert objective in ('native_repeats', 'native_minimax')
        matches = [opt for opt in optima if opt['H'] == horizon
                   and opt['noise'] == noise and opt['objective'] == objective]
        assert len(matches) == 1
        optimum = matches[0]
        budget = max(0., optimum['actual_cost'])+eta+5e-8
        check('outer_budget', row['native_loss_bound'], budget)
        if row['fraction'] != '':
            check('normalization', eta, float(row['fraction'])*optimum['normalization_scale'])
        loss = budget/.2 if objective == 'native_repeats' else budget
        check('diagnostic_mean_budget', loss, row['diagnostic_average_bound_new'])
        values = {}
        for source in ('majority3', 'count3'):
            selected = [certificate for certificate in certificates
                        if certificate['diagnostic_source'] == source
                        and tuple(map(Q, certificate['eps'])) == tuple(Q(str(x)) for x in noise)
                        and certificate['word'] == row['target']]
            assert len(selected) == 5
            values[source] = min(float(Q(certificate['intercept'])
                                       +Q(certificate['slope'])*Q(str(loss)))
                                 for certificate in selected)
        check('majority_portfolio', values['majority3'], row['new_majority_upper'])
        check('count_portfolio', values['count3'], row['new_count_upper'])
        baseline = min(float(row['guaranteed_upper']), values['majority3'])
        refined = min(baseline, values['count3'])
        check('baseline', baseline, row['baseline_including_new_majority'])
        check('refined', refined, row['refined_upper'])
        witness = by_id[row['witness_id']]
        deficits = witness['target_deficiencies']
        witness_cost = (sum(WEIGHTS[target]*deficits[target] for target in WEIGHTS)
                        if objective == 'native_repeats'
                        else max(deficits[target] for target in WEIGHTS))
        check('witness_cost', witness_cost, row['witness_native_cost'])
        upper('witness_eligibility', witness_cost, budget)
        check('witness_error', deficits[row['target']], row['witnessed_lower'])
        upper('witness_vs_upper', deficits[row['target']], refined)
        assert row['lower_witness_scope'] == (
            'numerically enlarged cost sublevel; not an exact eta-optimality assertion')
        cases.add((horizon, tuple(noise), objective, row['fraction'], eta, row['normalization']))

    assert len(rows) == 252 and len(cases) == 42
    assert sum(row['held_out'] == 'True' for row in rows) == 126
    assert len({(int(row['H']), row['noise'], row['objective'], row['fraction'],
                 row['eta'], row['normalization'], row['target']) for row in rows}) == 252
    inputs = [HERE/'comparison.csv', HERE/'results.json', *optimum_paths, *parent_audit_paths]
    result = {
        'status': 'passed',
        'scope': ('Independent recomputation of all comparison budgets, portfolio bounds, '
                  'and eligibility of saved lower witnesses; no new policy optimization '
                  'or worst-target envelope claim.'),
        'audit_source_sha256': digest(Path(__file__)),
        'protocol_sha256': digest(HERE/'PROTOCOL.md'),
        'comparison_count': 252,
        'distinct_objective_sublevels': 42,
        'held_out_count': 126,
        'numerical_tolerance': TOLERANCE,
        'max_errors': errors,
        'inputs': {str(path.relative_to(HERE)) if path.is_relative_to(HERE)
                   else '../'+str(path.relative_to(PARENT)): digest(path) for path in inputs},
    }
    (HERE/'audit_comparison.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
