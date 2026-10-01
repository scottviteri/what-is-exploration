#!/usr/bin/env python3
"""Exact independent full-history common-decoder upper-bound audit.

Each event objective is bound to p_theta(h)*G(h,event) on the independently
reconstructed native-optimal LP's terminal flow variables. All other objective
coordinates must be zero. Exact repaired duals then prove every event bound.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import hashlib
import importlib.util
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location('independent_history_bound_audit', HERE/'audit_compressed.py')
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=HERE/'native_history_certificate.json')
    parser.add_argument('--output', type=Path, default=HERE/'audit_native_history_bound.json')
    args = parser.parse_args();start = time.monotonic()
    model = AUDIT.ExactModel()
    AUDIT.verify_metadata(model, json.loads((HERE/'compressed_oracle_metadata.json').read_text()))
    AUDIT.verify_exact_model_export(model, HERE/'compressed_oracle_exact_model.json')
    five = AUDIT.verify_five_target(model)
    certificate = json.loads(args.input.read_text())
    assert certificate['H'] == 4 and list(map(Q, certificate['noise'])) == [Q(1, 10)]*2
    assert Q(certificate['native_cost_bound']) == Q(9, 1250)
    for field, name in {'source_sha256': 'certify_native_history.py',
                        'linear_oracle_sha256': 'linear_native_oracle.py',
                        'compressed_oracle_sha256': 'compressed_oracle.py',
                        'exact_helper_sha256': 'exact_oracle_certificate.py',
                        'exact_model_sha256': 'compressed_oracle_exact_model.json'}.items():
        assert certificate[field] == digest(HERE/name)
    assert certificate['input_sha256'] == digest(HERE/certificate['input_path'])
    source_input = json.loads((HERE/certificate['input_path']).read_text())
    assert source_input['protocol_sha256'] == digest(HERE/'PROTOCOL.md')
    terminal = model.reachable[-1]
    assert tuple(tuple(map(tuple, history)) for history in certificate['terminal_histories']) == tuple(terminal)
    indices = [model.w[history] for history in terminal]
    assert certificate['terminal_indices'] == indices
    likelihoods = [model.likelihoods[history] for history in terminal]
    assert [[Q(x) for x in row] for row in certificate['terminal_prefix_laws']] == likelihoods
    assert certificate['target_count_groups'] == five['groups_from_six']
    assert certificate['target_rows'] == five['target_rows']
    target = [[Q(x) for x in row] for row in certificate['target_rows']]
    original = model.targets['adaptive_L']
    assert [[Q(x) for x in row] for row in certificate['target_count_rows']] == original['rows']
    assert [[Q(x) for x in row] for row in certificate['target_full_rows']] == original['full']
    assert certificate['target_full_groups'] == original['groups']
    lift = [[Q(x) for x in row] for row in certificate['five_to_six_lift']]
    encoding = [[Q(int(index in group)) for group in certificate['target_count_groups']] for index in range(6)]
    assert AUDIT.INDEPENDENT.matmul(target, lift) == original['rows']
    assert AUDIT.INDEPENDENT.matmul(lift, encoding) == [[Q(int(i == j)) for j in range(5)] for i in range(5)]
    assert all(sum(row) == 1 and min(row) >= 0 for row in lift)
    decoder = [[Q(x) for x in row] for row in certificate['decoder']]
    assert len(decoder) == 208 and all(len(row) == 5 and min(row) >= 0 and sum(row) == 1 for row in decoder)
    expected = {(world, mask) for world in range(4) for mask in range(32)}
    covered, results, worst = set(), [], Q(0)
    for event in certificate['events']:
        world, mask = event['world'], event['mask']
        assert (world, mask) in expected and (world, mask) not in covered
        covered.add((world, mask))
        objective = [Q(0)]*model.n
        for index, law, row in zip(indices, likelihoods, decoder):
            objective[index] = law[world]*sum(row[column] for column in range(5) if mask & (1 << column))
        support = event['support_certificate']
        assert list(map(Q, support['max_objective'])) == objective
        verified = AUDIT.verify_linear_certificate(model, support)
        target_mass = sum(target[world][column] for column in range(5) if mask & (1 << column))
        assert Q(event['target_mass']) == target_mass
        upper = Q(verified['exact_upper'])-target_mass
        assert upper == Q(event['event_error_upper'])
        worst = max(worst, upper)
        results.append({'world': world, 'mask': mask, 'exact_error_upper_float': float(upper),
                        'all_objective_coordinates_bound': True, 'dual_residual_coordinates_checked': model.n})
    assert covered == expected and worst == Q(certificate['exact_upper'])
    lower = Q(9, 125)
    assert worst >= lower
    clean = Q(certificate['clean_exact_upper'])
    assert clean >= worst and certificate['sharp_at_9_over_125'] == (worst <= lower)
    assert args.output.name.startswith('audit_')
    result = {'status': 'passed', 'audit_source_sha256': digest(Path(__file__)),
              'independent_model_audit_sha256': digest(HERE/'audit_compressed.py'),
              'protocol_sha256': digest(HERE/'PROTOCOL.md'),
              'certificate_path': args.input.name, 'certificate_sha256': digest(args.input),
              'exact_model_sha256': digest(HERE/'compressed_oracle_exact_model.json'),
              'decoder_rows_checked': 208, 'target_outputs': 5, 'event_world_checks': len(covered),
              'exact_objective_coordinates_bound': len(covered)*model.n,
              'exact_dual_residual_coordinates_checked': len(covered)*model.n,
              'exact_inequality_multiplier_signs_checked': len(covered)*len(model.ub),
              'exact_upper': str(worst), 'exact_upper_float': float(worst),
              'clean_exact_upper': str(clean), 'clean_exact_upper_float': float(clean),
              'known_exact_lower': str(lower), 'remaining_clean_bracket_width': str(clean-lower),
              'matching_upper_certified': worst <= lower,
              'events': results, 'run_seconds': time.monotonic()-start,
              'scope': ('One common full-history decoder proves the upper for every exact native-repeat '
                        'minimizer at H4, noise .1/.1. A strictly positive residual above .072 remains '
                        'a certified bracket rather than an equality proof. Positive objective gaps are excluded.')}
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: value for key, value in result.items() if key not in ('events', 'exact_upper')}, indent=2))


if __name__ == '__main__':
    main()
