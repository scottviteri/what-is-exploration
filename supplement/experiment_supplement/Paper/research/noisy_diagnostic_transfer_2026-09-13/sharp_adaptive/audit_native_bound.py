#!/usr/bin/env python3
"""Independently check every event of a native-optimal common-decoder bound.

Reconstructs the exact policy LP via audit_compressed, binds each event objective
to the declared rational decoder and world law, and rechecks the rational dual
multipliers and every box residual. No planner or certificate producer import.
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
SPEC = importlib.util.spec_from_file_location('independent_compressed_bound_audit', HERE/'audit_compressed.py')
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=HERE/'native_count_certificate.json')
    parser.add_argument('--output', type=Path, default=HERE/'audit_native_count_bound.json')
    args = parser.parse_args()
    start = time.monotonic()
    model = AUDIT.ExactModel()
    metadata_path = HERE/'compressed_oracle_metadata.json'
    AUDIT.verify_metadata(model, json.loads(metadata_path.read_text()))
    AUDIT.verify_exact_model_export(model, HERE/'compressed_oracle_exact_model.json')
    certificate = json.loads(args.input.read_text())
    assert certificate['H'] == 4 and list(map(Q, certificate['noise'])) == [Q(1, 10)]*2
    assert Q(certificate['native_cost_bound']) == Q(9, 1250)
    provenance = {'source_sha256': 'certify_native_count.py',
                  'linear_oracle_sha256': 'linear_native_oracle.py',
                  'compressed_oracle_sha256': 'compressed_oracle.py',
                  'exact_helper_sha256': 'exact_oracle_certificate.py',
                  'exact_model_sha256': 'compressed_oracle_exact_model.json'}
    for key, filename in provenance.items():
        assert certificate[key] == digest(HERE/filename)
    assert certificate['checkpoint_sha256'] == digest(HERE/certificate['checkpoint_path'])
    assert list(map(tuple, certificate['states'])) == model.states
    assert [[Q(x) for x in row] for row in certificate['rays']] == model.rays
    target = model.targets['adaptive_L']
    assert [[Q(x) for x in row] for row in certificate['target_rows']] == target['rows']
    assert [[Q(x) for x in row] for row in certificate['target_full_rows']] == target['full']
    assert certificate['target_groups'] == target['groups']
    decoder = [[Q(x) for x in row] for row in certificate['decoder']]
    assert len(decoder) == 28 and all(len(row) == 6 and min(row) >= 0 and sum(row) == 1 for row in decoder)
    expected_coverage = {(world, mask) for world in range(4) for mask in range(64)}
    covered, event_results, worst = set(), [], Q(0)
    for event in certificate['events']:
        world, mask = event['world'], event['mask']
        assert (world, mask) in expected_coverage and (world, mask) not in covered
        covered.add((world, mask))
        coefficients = [ray[world]*sum(row[column] for column in range(6) if mask & (1 << column))
                        for ray, row in zip(model.rays, decoder)]
        support = event['support_certificate']
        assert list(map(Q, support['coefficients'])) == coefficients
        verified = AUDIT.verify_repaired_certificate(model, support)
        target_mass = sum(target['rows'][world][column] for column in range(6) if mask & (1 << column))
        assert Q(event['target_mass']) == target_mass
        upper = Q(verified['exact_upper'])-target_mass
        assert upper == Q(event['event_error_upper'])
        worst = max(worst, upper)
        event_results.append({'world': world, 'mask': mask, 'exact_error_upper_float': float(upper),
                              'exact_coefficient_binding': True, 'residual_coordinates_checked': model.n})
    assert covered == expected_coverage
    assert worst == Q(certificate['exact_upper'])
    clean = Q(certificate['clean_exact_upper'])
    assert worst <= clean == Q(923, 12500)
    assert args.output.name.startswith('audit_')
    result = {'status': 'passed', 'audit_source_sha256': digest(Path(__file__)),
              'independent_model_audit_sha256': digest(HERE/'audit_compressed.py'),
              'protocol_sha256': digest(HERE/'PROTOCOL.md'),
              'certificate_path': args.input.name, 'certificate_sha256': digest(args.input),
              'exact_model_sha256': digest(HERE/'compressed_oracle_exact_model.json'),
              'decoder_rows_checked': 28, 'target_outputs': 6, 'event_world_checks': len(covered),
              'exact_dual_residual_coordinates_checked': len(covered)*model.n,
              'exact_inequality_multiplier_signs_checked': len(covered)*len(model.ub),
              'exact_upper': str(worst), 'exact_upper_float': float(worst),
              'clean_exact_upper': str(clean), 'clean_exact_upper_float': float(clean),
              'known_exact_lower': '9/125', 'remaining_clean_bracket_width': str(clean-Q(9, 125)),
              'events': event_results, 'run_seconds': time.monotonic()-start,
              'scope': ('A verified common signed-count decoder proves the upper for every exact '
                        'native-repeat minimizer at H4, noise .1/.1. The policy-specific extremum '
                        'is bracketed, not certified sharp; this does not apply to positive objective gaps.')}
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: value for key, value in result.items() if key not in ('events', 'exact_upper')}, indent=2))


if __name__ == '__main__':
    main()
