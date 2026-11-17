"""Independent finite linear-program evaluation, never called by learner updates.

The bounds are replayed floating-point numerical certificates. Explicit
feasibility residuals and rounding allowances are retained; they are not Lean
proofs or exact rational certificates for the stochastic source probabilities.
"""
from __future__ import annotations

import time

import numpy as np
from scipy import sparse
from scipy.optimize import linprog

from models import (HISTORIES, LEAF_INDEX, TARGETS, collector_kernel,
                    raw_history_likelihood, target_kernel, validate_tables)


NUMERICAL_PADDING = 2e-10


def _valid_experiment(matrix: np.ndarray) -> np.ndarray:
    matrix = np.asarray(matrix, dtype=np.float64)
    if matrix.ndim != 2 or min(matrix.shape) == 0 or not np.all(np.isfinite(matrix)):
        raise ValueError("an experiment must be a nonempty finite matrix")
    if matrix.min() < -1e-14 or not np.allclose(matrix.sum(1), 1, atol=1e-11, rtol=0):
        raise ValueError("experiment rows must be probability distributions")
    return matrix


def _matrix(rows, cols, values, shape):
    return sparse.coo_matrix((values, (rows, cols)), shape=shape).tocsr()


def _solve(c, A_ub, b_ub, A_eq, b_eq):
    result = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                     bounds=(0.0, 1.0), method="highs",
                     options={"dual_feasibility_tolerance": 1e-9,
                              "primal_feasibility_tolerance": 1e-9})
    if not result.success:
        raise RuntimeError(f"Finite oracle LP failed: {result.status}: {result.message}")
    return result


def _box_dual_lower(c, A_ub, b_ub, A_eq, b_eq, result) -> tuple[float, float]:
    """A weak-duality bound valid even with nonzero dual stationarity residual.

    For variables in [0,1], clip inequality multipliers to the feasible negative
    cone and minimize each residual affine coefficient over that box. Equality
    multipliers are free. The padding covers ordinary floating-point evaluation;
    it is reported rather than presented as a formal interval-arithmetic proof.
    """
    inequality = np.minimum(np.asarray(result.ineqlin.marginals), 0.0).astype(np.longdouble)
    equality = np.asarray(result.eqlin.marginals).astype(np.longdouble)
    residual = (np.asarray(c, dtype=np.longdouble)
                - A_ub.T.astype(np.longdouble) @ inequality
                - A_eq.T.astype(np.longdouble) @ equality)
    affine = np.dot(np.asarray(b_ub, dtype=np.longdouble), inequality)
    affine += np.dot(np.asarray(b_eq, dtype=np.longdouble), equality)
    correction = np.minimum(residual, 0).sum(dtype=np.longdouble)
    scale = 1 + abs(affine) + np.abs(residual).sum(dtype=np.longdouble)
    padding = float(NUMERICAL_PADDING * scale)
    return float(affine + correction) - padding, padding


def _feasibility(A_ub, b_ub, A_eq, b_eq, x) -> dict:
    return {
        "equality_residual": float(np.max(np.abs(A_eq @ x - b_eq), initial=0)),
        "inequality_violation": float(np.max(A_ub @ x - b_ub, initial=0)),
        "box_violation": float(max(0, -x.min(), x.max() - 1)),
    }


def deficiency(E: np.ndarray, F: np.ndarray) -> dict:
    """Independent decoder LP with a replayed kernel upper and dual lower bound."""
    started = time.perf_counter()
    E, F = _valid_experiment(E), _valid_experiment(F)
    if E.shape[0] != F.shape[0]:
        raise ValueError("experiments must have the same worlds")
    worlds, sources, outputs = E.shape[0], E.shape[1], F.shape[1]
    ng, ns = sources * outputs, worlds * outputs
    nv = ng + ns + 1
    c = np.zeros(nv); c[-1] = 1
    ir, ic, iv, rhs = [], [], [], []
    row = 0
    for world in range(worlds):
        for output in range(outputs):
            for sign in (1.0, -1.0):
                for source in range(sources):
                    coefficient = sign * E[world, source]
                    if coefficient:
                        ir.append(row); ic.append(source * outputs + output); iv.append(coefficient)
                ir.append(row); ic.append(ng + world * outputs + output); iv.append(-1.0)
                rhs.append(sign * F[world, output]); row += 1
        for output in range(outputs):
            ir.append(row); ic.append(ng + world * outputs + output); iv.append(.5)
        ir.append(row); ic.append(nv - 1); iv.append(-1)
        rhs.append(0.0); row += 1
    A_ub = _matrix(ir, ic, iv, (row, nv)); b_ub = np.asarray(rhs)
    er = np.repeat(np.arange(sources), outputs)
    ec = np.arange(ng)
    A_eq = _matrix(er, ec, np.ones(ng), (sources, nv)); b_eq = np.ones(sources)
    result = _solve(c, A_ub, b_ub, A_eq, b_eq)
    G = np.maximum(result.x[:ng].reshape(sources, outputs), 0)
    sums = G.sum(1, keepdims=True)
    G = np.divide(G, sums, out=np.full_like(G, 1 / outputs), where=sums > 0)
    achieved = float(np.max(.5 * np.abs(E @ G - F).sum(1)))
    lower, dual_padding = _box_dual_lower(c, A_ub, b_ub, A_eq, b_eq, result)
    lower = max(0.0, lower)
    upper = min(1.0, achieved + NUMERICAL_PADDING)
    if lower > upper + 1e-9:
        raise ArithmeticError(f"Decoder certificate bounds cross: {lower}, {upper}")
    return {
        "lower": lower, "upper": upper, "G": G,
        "value": float(result.fun), "achieved_error": achieved,
        "duality_gap": upper - lower, "dual_rounding_allowance": dual_padding,
        "kernel_rounding_allowance": NUMERICAL_PADDING,
        "feasibility": _feasibility(A_ub, b_ub, A_eq, b_eq, result.x),
        "seconds": time.perf_counter() - started,
        "certificate_kind": "floating-point replay and box-corrected weak duality",
    }


def audit_policy(tables: dict, policy: np.ndarray, targets=TARGETS) -> dict:
    E = collector_kernel(tables, policy)
    targets = tuple(targets)
    if not targets:
        raise ValueError("audit requires at least one target")
    details = [deficiency(E, target_kernel(tables, target)) for target in targets]
    lower = np.asarray([d["lower"] for d in details])
    upper = np.asarray([d["upper"] for d in details])
    return {"lower": lower, "upper": upper,
            "worst_lower": float(lower.max()), "worst_upper": float(upper.max()),
            "worst_target_index": int(np.argmax(upper)),
            "G": np.stack([d["G"] for d in details]),
            "seconds": float(sum(d["seconds"] for d in details)),
            "max_duality_gap": float(np.max(upper - lower)),
            "max_lp_feasibility_residual": float(max(max(d["feasibility"].values()) for d in details))}


def minimax_reference(tables: dict, targets=TARGETS, min_action_probability: float = 0.0) -> dict:
    """Optimize all stochastic two-step collectors and one decoder per target.

    Root realization weights occupy 0:3; the next 18 weights describe
    (a0,o0,a1). Decoder variables z[target,h,y] equal a leaf weight times
    G[target,h,y], making the simultaneous policy/decoder program linear.
    """
    started = time.perf_counter()
    validate_tables(tables)
    floor = float(min_action_probability)
    if not np.isfinite(floor) or not 0 <= floor <= 1 / 3:
        raise ValueError("min_action_probability must lie between zero and one third")
    targets = tuple(targets)
    if not targets:
        raise ValueError("minimax reference requires at least one target")
    raw = raw_history_likelihood(tables)
    target_laws = [target_kernel(tables, target) for target in targets]
    count, nw, nh, ny = len(targets), 4, 36, 4
    zbase = 21
    sbase = zbase + count * nh * ny
    radius = sbase + count * nw * ny
    nv = radius + 1
    c = np.zeros(nv); c[radius] = 1.0
    er, ec, ev, eqrhs = [], [], [], []
    row = 0
    for a0 in range(3):
        er.append(row); ec.append(a0); ev.append(1.0)
    eqrhs.append(1.0); row += 1
    for a0 in range(3):
        for o0 in range(2):
            er.append(row); ec.append(a0); ev.append(-1.0)
            for a1 in range(3):
                er.append(row); ec.append(3 + (2 * a0 + o0) * 3 + a1); ev.append(1.0)
            eqrhs.append(0.0); row += 1
    for j in range(count):
        for history in range(nh):
            er.append(row); ec.append(int(LEAF_INDEX[history])); ev.append(-1.0)
            for y in range(ny):
                er.append(row); ec.append(zbase + (j * nh + history) * ny + y); ev.append(1.0)
            eqrhs.append(0.0); row += 1
    A_eq = _matrix(er, ec, ev, (row, nv)); b_eq = np.asarray(eqrhs)
    ir, ic, iv, rhs = [], [], [], []
    row = 0
    if floor:
        for a0 in range(3):
            ir.append(row); ic.append(a0); iv.append(-1.0)
            rhs.append(-floor); row += 1
            for o0 in range(2):
                for a1 in range(3):
                    ir.extend((row, row))
                    ic.extend((a0, 3 + (2 * a0 + o0) * 3 + a1))
                    iv.extend((floor, -1.0))
                    rhs.append(0.0); row += 1
    for j, F in enumerate(target_laws):
        for world in range(nw):
            for y in range(ny):
                for sign in (1.0, -1.0):
                    for history in range(nh):
                        coefficient = sign * raw[world, history]
                        if coefficient:
                            ir.append(row); ic.append(zbase + (j * nh + history) * ny + y); iv.append(coefficient)
                    ir.append(row); ic.append(sbase + (j * nw + world) * ny + y); iv.append(-1.0)
                    rhs.append(sign * F[world, y]); row += 1
            for y in range(ny):
                ir.append(row); ic.append(sbase + (j * nw + world) * ny + y); iv.append(.5)
            ir.append(row); ic.append(radius); iv.append(-1.0)
            rhs.append(0.0); row += 1
    A_ub = _matrix(ir, ic, iv, (row, nv)); b_ub = np.asarray(rhs)
    result = _solve(c, A_ub, b_ub, A_eq, b_eq)
    lower, padding = _box_dual_lower(c, A_ub, b_ub, A_eq, b_eq, result)
    policy = np.zeros((7, 3), dtype=float)
    policy[0] = np.maximum(result.x[:3], 0)
    policy[0] /= policy[0].sum()
    for a0 in range(3):
        for o0 in range(2):
            values = np.maximum(result.x[3 + (2 * a0 + o0) * 3:6 + (2 * a0 + o0) * 3], 0)
            policy[1 + 2 * a0 + o0] = values / values.sum() if values.sum() > 1e-14 else 1 / 3
    if floor:
        # Remove possible floating-point violations of the per-action floor.
        for row_id in range(7):
            surplus = np.maximum(policy[row_id] - floor, 0.0)
            policy[row_id] = (floor + (1 - 3 * floor) * surplus / surplus.sum()
                              if surplus.sum() > 0 else np.full(3, 1 / 3))
    # Independent fresh decoder LPs audit the recovered executable policy.
    profile = audit_policy(tables, policy, targets)
    lower, upper = max(0.0, lower), profile["worst_upper"]
    if lower > upper + 1e-8:
        raise ArithmeticError(f"Minimax reference bounds cross: {lower}, {upper}")
    return {
        "policy": policy, "lower": lower, "upper": upper,
        "min_action_probability": floor,
        "value": float(result.fun), "duality_gap": upper - lower,
        "profile": profile, "dual_rounding_allowance": padding,
        "feasibility": _feasibility(A_ub, b_ub, A_eq, b_eq, result.x),
        "targets": [list(t) if not isinstance(t, (int, np.integer)) else list(TARGETS[int(t)]) for t in targets],
        "seconds": time.perf_counter() - started,
        "certificate_kind": "finite floating-point policy LP, corrected dual lower, independent decoder replay upper",
    }
