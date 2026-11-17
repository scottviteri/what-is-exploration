"""Exact finite-history forecasts for deterministic PLAY startup.

The unresolved finite tail is merged only because its literal observations
agree over the checked horizon. This computes predictive rewards, not a
world-posterior Brier score on that coarsened class. No policy optimization or
learning is performed. Rational Square checks and floating-point entropy checks
are independent of the Lean scalar-gap check.
"""
from fractions import Fraction as F
from math import log2
from pathlib import Path
import json


def worlds(horizon):
    return [(None, F(1, 2))] + [(k, F(1, 2 ** (k + 2)))
           for k in range(horizon - 1)] + [('late', F(1, 2 ** horizon))]


def observations(world, history, action):
    if not history:
        digit = int(world is not None) if action == 0 else 0
        return [((2 * digit, 0), F(1))]
    monitor = int(world == len(history) - 1)
    if history[0][0] == 0:
        return [((0, monitor), F(1))]
    digit = int(action == 2)
    return [((2 * digit + color, monitor), F(1, 2)) for color in (0, 1)]


def actions(history, startup, continuation):
    if not history:
        return [(startup, F(1))]
    if continuation == 'uniform':
        return [(a, F(1, 3)) for a in range(3)]
    if continuation == 'adaptive':
        return [((history[-1][1][0] + history[-1][1][1]) % 3, F(1))]
    if continuation == 'alternate':
        return [(1 + len(history) % 2, F(1))]
    return [(int(continuation), F(1))]


def evaluate(horizon, startup, continuation):
    model = worlds(horizon)
    assert sum(p for _, p in model) == 1
    frontier = {(): tuple(p for _, p in model)}
    square, shannon = F(0), 0.0
    for _ in range(horizon):
        next_frontier = {}
        for history, masses in frontier.items():
            node_mass = sum(masses)
            for action, action_prob in actions(history, startup, continuation):
                children = {}
                for i, (world, _) in enumerate(model):
                    if masses[i] == 0:
                        continue
                    for observation, probability in observations(world, history, action):
                        child = children.setdefault(observation, [F(0)] * len(model))
                        child[i] += masses[i] * action_prob * probability
                for observation, child in children.items():
                    mass = sum(child)
                    forecast = mass / (node_mass * action_prob)
                    square -= mass * forecast
                    shannon -= float(mass) * log2(float(forecast))
                    next_frontier[history + ((action, observation),)] = tuple(child)
        frontier = next_frontier
        assert sum(sum(m) for m in frontier.values()) == 1
    return square, shannon, len(frontier)


def binary_entropy(p):
    p = float(p)
    return -p * log2(p) - (1 - p) * log2(1 - p) if 0 < p < 1 else 0.0


def expected(horizon, inspect):
    if inspect:
        return -F(horizon) + 1 - F(1, 2 ** horizon), 2 - 2 ** (1 - horizon)
    square, shannon = F(-1), 0.0
    for k in range(horizon - 1):
        pulse = F(1, 2 ** (k + 2))
        silent = F(1, 2) + 2 * pulse
        conditional = pulse / silent
        square += -F(1, 2) + pulse * (1 - conditional)
        shannon += 1 + float(silent) * binary_entropy(conditional)
    return square, shannon


def main():
    records = []
    for horizon in range(1, 6):
        for startup in (0, 1, 2):
            for continuation in ('0', '1', '2', 'alternate', 'adaptive', 'uniform'):
                square, shannon, leaves = evaluate(horizon, startup, continuation)
                sq, sh = expected(horizon, startup == 0)
                assert square == sq
                assert abs(shannon - sh) < 1e-10
                records.append({'horizon': horizon, 'startup': startup,
                                'continuation': continuation, 'square': str(square),
                                'shannon': shannon, 'leaves': leaves})
    gaps = []
    for horizon in range(1, 65):
        i_sq, i_sh = expected(horizon, True)
        p_sq, p_sh = expected(horizon, False)
        assert (p_sq > i_sq) == (horizon >= 3)
        assert (p_sh > i_sh) == (horizon >= 2)
        gaps.append({'horizon': horizon, 'square_play_minus_inspect': str(p_sq - i_sq),
                     'shannon_play_minus_inspect': p_sh - i_sh})
    result = {'passed': True, 'literal_history_cases': len(records),
              'scope': 'Finite exact Square/float Shannon forecasts; no infinite or all-policy theorem certified by enumeration.',
              'cases': records, 'formula_checks': gaps}
    Path(__file__).with_name('checks.json').write_text(json.dumps(result, indent=2) + '\n')
    print('PASS:', len(records), 'literal history cases; 64 horizon formula checks.')


if __name__ == '__main__':
    main()
