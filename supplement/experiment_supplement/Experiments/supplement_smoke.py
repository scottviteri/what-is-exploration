"""Bounded checks of extracted planning code; no archived runs or output writes."""
from pathlib import Path
import sys
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'Paper/research/target_selection_2026-09-23'))
sys.path.insert(0, str(ROOT / 'Paper/research/target_selection_followups_2026-09-23'))
import scaling_core as core
import objective_dp as dp
from recovery_decoder import RecoveryDecoder


def main():
    model = core.model('sensors_0.1_0.3')
    geometry = core.geometry(model['T'], model['Z'], 2)
    scores = dp.terminal_scores(geometry.layers, geometry.p)
    checks = []
    for name in ('information', 'brier'):
        answer = dp.plan_terminal_rewards(geometry.layers, geometry.p, scores[name])
        _, _, _, lp = core.reward_plan(geometry, geometry.raw.mean(0) * scores[name])
        assert abs(answer['objective'] + lp['primal']) < 2e-7
        assert np.max(abs(answer['E'].sum(1) - 1)) < 1e-10
        checks.append(name + ': DP/LP agreement')
    uninformative = np.array([[1., 0.], [1., 0.]])
    perfect = np.eye(2)
    for source, target, expected in [(uninformative, perfect, .5), (perfect, uninformative, 0.)]:
        report, witness = RecoveryDecoder(source, 2, time_limit=20.).solve(target)
        assert abs(report['upper'] - expected) < 2e-7
        assert abs(report['lower'] - expected) < 2e-7
        checks.append(f'deficiency known answer: {expected}')
    print('Passed bounded numerical smoke checks: ' + '; '.join(checks))
    print('This does not rerun the reported experiment campaigns or validate their archived certificates.')


if __name__ == '__main__':
    main()
