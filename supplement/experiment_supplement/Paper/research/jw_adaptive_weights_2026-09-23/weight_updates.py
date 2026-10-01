"""Solver-free finite emphasis rules. These do not choose a rich background.

Use their returned distribution with Objective.rich and a fixed positive epsilon.
This is offline model-based optimization metadata, never the actual unknown world.
All cost collection, loss evaluation, and weight-search time must be charged.
"""
from fractions import Fraction as F
import math
from adaptive_weights import rational


def distribution(values):
    values = tuple(map(rational, values))
    if not values or any(x < 0 for x in values) or sum(values) <= 0:
        raise ValueError('Nonnegative, nonzero finite weights required')
    total = sum(values)
    return tuple(x/total for x in values)


def tractability_weights(reference, charged_costs, cost_scale):
    """Inverse measured-cost emphasis, independent of achieved deficiency values.

    This implements one prespecified cost heuristic, not a guarantee of speed.
    Costs are nonnegative cumulative per-target decoder seconds including failures.
    A common scale prevents arbitrary units from changing the convention.
    """
    reference = distribution(reference)
    costs = tuple(map(rational, charged_costs)); scale = rational(cost_scale)
    if len(costs) != len(reference) or any(c < 0 for c in costs) or scale <= 0:
        raise ValueError('Aligned nonnegative costs and positive scale required')
    return distribution(tuple(p/(1+c/scale) for p,c in zip(reference,costs)))


def hard_target_update(previous, intervals, learning_rate):
    """Multiplicative-weights emphasis using interval midpoints.

    Finite floating exponentiation is explicitly approximate. Exact normalization
    is restored to the represented rational outputs; mathematical MW guarantees
    require charging the score error and bounding update error separately.
    """
    previous = distribution(previous)
    rate = float(rational(learning_rate))
    if not 0 < rate <= 1 or len(intervals) != len(previous) or any(p <= 0 for p in previous):
        raise ValueError('0<rate<=1, aligned intervals and positive finite starting weights')
    exact = tuple((rational(lo),rational(hi)) for lo,hi in intervals)
    if any(not 0 <= lo <= hi <= 1 for lo,hi in exact):
        raise ValueError('Invalid certified deficiency interval')
    logs = [math.log(float(p)) + rate*float((lo+hi)/2) for p,(lo,hi) in zip(previous,exact)]
    pivot = max(logs)
    raw = [F.from_float(math.exp(v-pivot)) for v in logs]
    if any(v == 0 for v in raw):
        raise ArithmeticError('Floating weight underflow; use a bounded-ratio or higher precision implementation')
    return distribution(raw), {
        'score_error_upper': str(max((hi-lo)/2 for lo,hi in exact)),
        'update_arithmetic': 'floating log/exp; no certified rounding budget yet',
        'last_iterate_minimax_guarantee': False}


def average_realizations(plans):
    """Average realization vectors; average conditional policy rows would differ."""
    plans = tuple(tuple(map(rational,p)) for p in plans)
    if not plans or not plans[0] or any(len(p)!=len(plans[0]) for p in plans):
        raise ValueError('Nonempty equal-dimensional realization plans required')
    return tuple(sum(column,F(0))/len(plans) for column in zip(*plans))
