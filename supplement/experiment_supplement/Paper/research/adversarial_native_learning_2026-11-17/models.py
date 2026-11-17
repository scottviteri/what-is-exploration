"""Finite two-step environments and literal history experiments for the pilot.

The learner receives only empirical tables produced by ``sample_tables``.
True tables are a sampling/evaluation interface, never a learner feature.
"""
from __future__ import annotations

import hashlib
import itertools

import numpy as np


ACTIONS = (0, 1, 2)  # left, right, fresh world-independent fair coin
WORLDS = tuple(itertools.product((0, 1), repeat=2))
HISTORIES = tuple(itertools.product(ACTIONS, (0, 1), ACTIONS, (0, 1)))
TARGETS = tuple(itertools.product(ACTIONS, repeat=3))
OBS_STRINGS = tuple(itertools.product((0, 1), repeat=2))
HISTORY_INDEX = {h: i for i, h in enumerate(HISTORIES)}
TARGET_INDEX = {target: i for i, target in enumerate(TARGETS)}
# A leaf realization variable is indexed by (a0,o0,a1), irrespective of o1.
LEAF_INDEX = np.asarray([3 + (2 * a0 + o0) * 3 + a1
                         for a0, o0, a1, o1 in HISTORIES], dtype=np.int64)
SECOND_POLICY_ROW = np.asarray([1 + 2 * a0 + o0 for a0, o0, a1, o1 in HISTORIES])
CASES = ("compatible", "irreversible", "noisy")


def validate_tables(tables: dict) -> None:
    for name, shape in (("first", (4, 3, 2)), ("second", (4, 3, 2, 3, 2))):
        array = np.asarray(tables[name], dtype=float)
        if array.shape != shape or not np.all(np.isfinite(array)):
            raise ValueError(f"{name} must be a finite array of shape {shape}")
        if array.min() < -1e-14 or not np.allclose(array.sum(axis=-1), 1.0, atol=1e-12, rtol=0):
            raise ValueError(f"{name} rows must be probability distributions")


def true_tables(case: str) -> dict[str, np.ndarray]:
    """Return the true controlled response rows, including unreachable rows.

    Noisy readings have independent crossover probability .15. In the
    irreversible environment every second observation is zero, including after
    a first-step coin. Other environments permit the second requested action.
    """
    if case not in CASES:
        raise ValueError(f"Unknown case {case!r}; choose from {CASES}")
    first = np.empty((4, 3, 2), dtype=np.float64)
    second = np.empty((4, 3, 2, 3, 2), dtype=np.float64)
    error = .15 if case == "noisy" else 0.0
    for world_id, bits in enumerate(WORLDS):
        for action in ACTIONS:
            probability_one = .5 if action == 2 else (1 - error if bits[action] else error)
            first[world_id, action] = (1 - probability_one, probability_one)
        if case == "irreversible":
            second[world_id, ..., 0] = 1.0
            second[world_id, ..., 1] = 0.0
        else:
            for a0, o0, a1 in itertools.product(ACTIONS, (0, 1), ACTIONS):
                second[world_id, a0, o0, a1] = first[world_id, a1]
    result = {"first": first, "second": second}
    validate_tables(result)
    return result


def _empirical_rows(counts: np.ndarray) -> np.ndarray:
    totals = counts.sum(axis=-1, keepdims=True)
    return np.divide(counts, totals, out=np.full(counts.shape, .5, dtype=float), where=totals > 0)


def sample_tables(case: str, seed: int, episodes_per_world: int) -> tuple[dict, dict]:
    """Estimate response rows from independently reset, uniformly acted episodes.

    World labels identify the four training strata. Zero-visit response rows
    receive an explicit uniform fallback. The returned metadata retains counts
    and SHA-256 hashes of both the ordered episodes and empirical table bytes.
    """
    if not isinstance(episodes_per_world, (int, np.integer)) or episodes_per_world <= 0:
        raise ValueError("episodes_per_world must be a positive integer")
    actual = true_tables(case)
    rng = np.random.default_rng(seed)
    first_counts = np.zeros((4, 3, 2), dtype=np.int64)
    second_counts = np.zeros((4, 3, 2, 3, 2), dtype=np.int64)
    episodes = np.empty((4, episodes_per_world, 4), dtype=np.uint8)
    for world_id in range(4):
        a0 = rng.integers(0, 3, size=episodes_per_world)
        o0 = (rng.random(episodes_per_world) < actual["first"][world_id, a0, 1]).astype(np.int64)
        a1 = rng.integers(0, 3, size=episodes_per_world)
        o1 = (rng.random(episodes_per_world) < actual["second"][world_id, a0, o0, a1, 1]).astype(np.int64)
        np.add.at(first_counts[world_id], (a0, o0), 1)
        np.add.at(second_counts[world_id], (a0, o0, a1, o1), 1)
        episodes[world_id] = np.column_stack((a0, o0, a1, o1))
    tables = {"first": _empirical_rows(first_counts), "second": _empirical_rows(second_counts)}
    validate_tables(tables)
    metadata = {
        "case": case,
        "seed": int(seed),
        "episodes_per_world": int(episodes_per_world),
        "total_episodes": int(4 * episodes_per_world),
        "behavior": "independent uniform actions at both steps",
        "world_access": "labelled resets to every training world; no runtime world label",
        "episode_encoding": "uint8[world,episode,(a0,o0,a1,o1)] in C order",
        "episodes_sha256": hashlib.sha256(episodes.tobytes()).hexdigest(),
        "first_counts": first_counts.tolist(),
        "second_counts": second_counts.tolist(),
        "unvisited_first_rows": int(np.count_nonzero(first_counts.sum(-1) == 0)),
        "unvisited_second_rows": int(np.count_nonzero(second_counts.sum(-1) == 0)),
        "unvisited_row_rule": "uniform probability over the two observations",
        "tables_sha256": hashlib.sha256(tables["first"].tobytes() + tables["second"].tobytes()).hexdigest(),
    }
    return tables, metadata


def raw_history_likelihood(tables: dict) -> np.ndarray:
    """Controlled observation masses p_world(h), with no policy factors."""
    validate_tables(tables)
    out = np.empty((4, 36), dtype=np.float64)
    for index, (a0, o0, a1, o1) in enumerate(HISTORIES):
        out[:, index] = tables["first"][:, a0, o0] * tables["second"][:, a0, o0, a1, o1]
    return out


def collector_kernel(tables: dict, policy: np.ndarray) -> np.ndarray:
    """World-to-full-history law of a history-dependent stochastic collector."""
    policy = np.asarray(policy, dtype=np.float64)
    if policy.shape != (7, 3) or not np.all(np.isfinite(policy)):
        raise ValueError("policy must have shape (7,3)")
    if policy.min() < -1e-14 or not np.allclose(policy.sum(-1), 1, atol=1e-12, rtol=0):
        raise ValueError("policy rows must be probability distributions")
    weights = np.asarray([policy[0, a0] * policy[1 + 2 * a0 + o0, a1]
                          for a0, o0, a1, o1 in HISTORIES])
    result = raw_history_likelihood(tables) * weights[None, :]
    if not np.allclose(result.sum(-1), 1, atol=1e-11, rtol=0):
        raise ArithmeticError("collector history rows failed normalization")
    return result


def _target_tuple(target) -> tuple[int, int, int]:
    if isinstance(target, (int, np.integer)):
        if not 0 <= int(target) < len(TARGETS):
            raise ValueError("target index out of range")
        return TARGETS[int(target)]
    target = tuple(int(x) for x in target)
    if target not in TARGET_INDEX:
        raise ValueError("target must be a three-action tuple")
    return target


def target_kernel(tables: dict, target) -> np.ndarray:
    """World-to-observation-string law for a known deterministic target tree."""
    validate_tables(tables)
    tree = _target_tuple(target)
    out = np.empty((4, 4), dtype=np.float64)
    for index, (o0, o1) in enumerate(OBS_STRINGS):
        a0, a1 = tree[0], tree[1 + o0]
        out[:, index] = tables["first"][:, a0, o0] * tables["second"][:, a0, o0, a1, o1]
    if not np.allclose(out.sum(-1), 1, atol=1e-11, rtol=0):
        raise ArithmeticError("target rows failed normalization")
    return out


def target_full_kernel(tables: dict, target) -> np.ndarray:
    """Reconstruct literal target actions, making the output equivalence explicit."""
    tree = _target_tuple(target)
    observation_law = target_kernel(tables, tree)
    out = np.zeros((4, 36), dtype=np.float64)
    for index, (o0, o1) in enumerate(OBS_STRINGS):
        history = (tree[0], o0, tree[1 + o0], o1)
        out[:, HISTORY_INDEX[history]] = observation_law[:, index]
    return out


def target_policy(target) -> np.ndarray:
    """Embed a deterministic target in the full collector policy parameterization."""
    tree = _target_tuple(target)
    policy = np.zeros((7, 3), dtype=np.float64)
    policy[0, tree[0]] = 1.0
    for a0, o0 in itertools.product(ACTIONS, (0, 1)):
        policy[1 + 2 * a0 + o0, tree[1 + o0]] = 1.0
    return policy
