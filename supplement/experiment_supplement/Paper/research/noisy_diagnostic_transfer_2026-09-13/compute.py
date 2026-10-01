#!/usr/bin/env python3
"""Certified full-history finite planning for noisy diagnostic transfer.

All-world-null histories containing WAIT -> 1 are omitted. Every retained
policy extends to all syntactic histories by prescribing WAIT on omitted
histories. Their probability is zero in every world under every policy.
Float64 primal/dual certificates are numerical checks, not interval proofs.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
from itertools import product
import json
from pathlib import Path
import platform
import sys
import time
import traceback
import numpy as np
import scipy
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

HERE = Path(__file__).resolve().parent
WORLDS = np.asarray(list(product((0, 1), repeat=2)), dtype=int)
EDGES = ((0, 0), (0, 1), (1, 0), (1, 1), (2, 0))
TARGET_NAMES = ("L", "R", "tagged", "LR", "LLL", "RRR", "LLR", "LRR", "adaptive_L")
WEIGHTS = np.asarray((.2, .2, .1, .1, .1, .1, 0., 0., 0.))
NATIVE_COUNTS = {"native_singles": 2, "native_tagged": 3, "native_joint": 4,
                 "native_repeats": 6, "native_minimax": 6}
PURPOSE_NAMES = ("U", "V", "world", "U_asymmetric", "parity")
TOL = 5e-8
SOLVER_OPTIONS = {"primal_feasibility_tolerance": 1e-9,
                  "dual_feasibility_tolerance": 1e-9,
                  "ipm_optimality_tolerance": 1e-10}
RESIDUALS = {}
COUNTS = {"planning_lps": 0, "deficiency_primal_lps": 0, "deficiency_dual_lps": 0}


def verify(name, value, tolerance=TOL):
    error = float(np.max(np.abs(np.asarray(value)), initial=0.))
    RESIDUALS[name] = max(RESIDUALS.get(name, 0.), error)
    if not np.isfinite(error) or error > tolerance:
        raise AssertionError((name, error, tolerance))


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, data):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, indent=2, allow_nan=False) + "\n")
    temporary.replace(path)


def histories(H):
    levels = [[()]]
    for _ in range(H):
        levels.append([h + (edge,) for h in levels[-1] for edge in EDGES])
    return levels


def behavior(levels, noise):
    p = {(): np.ones(4)}
    for layer in levels[:-1]:
        for h in layer:
            for a, o in EDGES:
                likelihood = np.ones(4) if a == 2 else np.where(WORLDS[:, a] == o, 1-noise[a], noise[a])
                p[h + ((a, o),)] = p[h] * likelihood
    return p


def prior(q):
    return np.where(WORLDS[:, 0] == 1, q, 1-q) * .5


def purpose(name):
    mu = prior(.25 if name == "U_asymmetric" else .5)
    labels = (np.arange(4) if name == "world" else WORLDS[:, 0] ^ WORLDS[:, 1]
              if name == "parity" else WORLDS[:, 1] if name == "V" else WORLDS[:, 0])
    utility = np.asarray([labels == d for d in range(int(labels.max())+1)], dtype=float)
    return mu, utility


def purpose_value(E, name):
    mu, utility = purpose(name)
    return float(np.max((utility * mu) @ E, axis=0).sum())


def potential(post, kind):
    if kind == "information":
        positive = post > 0
        return float(np.sum(post[positive] * np.log2(post[positive])))
    if kind == "quadratic":
        return float(post @ post)
    raise ValueError(kind)


def posterior_value(E, q, kind):
    mu = prior(q)
    joint = mu[:, None] * E
    mass = joint.sum(axis=0)
    total = sum(mass[k] * potential(joint[:, k] / mass[k], kind)
                for k in np.flatnonzero(mass > 0))
    return float(total - potential(mu, kind))


def realization(levels, action_rows):
    rows = iter(action_rows)
    w = {(): 1.}
    for layer in levels[:-1]:
        for h in layer:
            actions = next(rows)
            for a, o in EDGES:
                w[h + ((a, o),)] = w[h] * actions[a]
    return w


def experiment(levels, p, w):
    return np.stack([p[h] * w[h] for h in levels[-1]], axis=1)


def target_library(noise):
    targets = []
    specs = [("L", (0,)), ("R", (1,)), ("tagged", None), ("LR", (0, 1)),
             ("LLL", (0, 0, 0)), ("RRR", (1, 1, 1)), ("LLR", (0, 0, 1)), ("LRR", (0, 1, 1)), ("adaptive_L", "adaptive")]
    for i, (name, schedule) in enumerate(specs):
        H = 1 if schedule is None else 3 if schedule == "adaptive" else len(schedule)
        lev = histories(H)
        p = behavior(lev, noise)
        rows = np.asarray([(.5, .5, 0.) if schedule is None else
                           np.eye(3)[0 if not h else h[0][1]] if schedule == "adaptive" else
                           np.eye(3)[schedule[len(h)]] for layer in lev[:-1] for h in layer])
        E = experiment(lev, p, realization(lev, rows))
        keep = E.sum(axis=0) > 0
        E = E[:, keep]
        verify("target_stochastic", E.sum(axis=1)-1)
        targets.append({"name": name, "weight": float(WEIGHTS[i]), "kernel": E, "horizon": H,
                        "schedule": schedule, "signals": [h for h, k in zip(lev[-1], keep) if k]})
    return targets


class LP:
    def __init__(self):
        self.cost, self.bounds, self.eq, self.ub = [], [], [], []

    def var(self, cost=0., bounds=(0., 1.)):
        i = len(self.cost)
        self.cost.append(float(cost)); self.bounds.append(bounds)
        return i

    def row(self, coefficients, rhs, equality=False):
        (self.eq if equality else self.ub).append((coefficients, float(rhs)))

    def matrix(self, rows):
        rr, cc, vv = [], [], []
        for r, (coefficients, _) in enumerate(rows):
            for c, value in coefficients.items():
                if value:
                    rr.append(r); cc.append(c); vv.append(value)
        return coo_matrix((vv, (rr, cc)), shape=(len(rows), len(self.cost))).tocsr()


@dataclass
class Model:
    lp: LP
    w: dict
    x: dict
    levels: list
    p: dict
    targets: list
    objective: str
    planning_q: float | None
    deficit_indices: dict


def model(H, noise, targets, objective, q):
    lev = histories(H); p = behavior(lev, noise); lp = LP()
    w = {h: lp.var() for layer in lev for h in layer}
    x = {}
    lp.row({w[()]: 1}, 1, True)
    for layer in lev[:-1]:
        for h in layer:
            row = {w[h]: -1}
            for a in range(3):
                x[h, a] = lp.var(); row[x[h, a]] = 1
                for aa, o in EDGES:
                    if aa == a:
                        lp.row({w[h + ((a, o),)]: 1, x[h, a]: -1}, 0, True)
            lp.row(row, 0, True)
    deficits = {}
    if objective in NATIVE_COUNTS:
        minimax = lp.var(1.) if objective == "native_minimax" else None
        for target in targets[:NATIVE_COUNTS[objective]]:
            T = target["kernel"]; Y = T.shape[1]
            d = lp.var(0. if minimax is not None else target["weight"])
            deficits[target["name"]] = d
            if minimax is not None:
                lp.row({d: 1, minimax: -1}, 0)
            allocations = {}
            for h in lev[-1]:
                row = {w[h]: -1}
                for y in range(Y):
                    allocations[h, y] = lp.var(); row[allocations[h, y]] = 1
                lp.row(row, 0, True)
            for theta in range(4):
                errors = []
                for y in range(Y):
                    error = lp.var(); errors.append(error)
                    row = {allocations[h, y]: p[h][theta] for h in lev[-1]}
                    lp.row(row | {error: -1}, T[theta, y])
                    lp.row({i: -v for i, v in row.items()} | {error: -1}, -T[theta, y])
                lp.row({i: .5 for i in errors} | {d: -1}, 0)
    else:
        mu = prior(q); initial = potential(mu, objective)
        for h in lev[-1]:
            mass = float(mu @ p[h])
            lp.cost[w[h]] = -mass * (potential(mu*p[h]/mass, objective)-initial)
    return Model(lp, w, x, lev, p, targets, objective, q, deficits)


def certificate_arrays(lp, sol, ae, au, be, bu):
    result = {"cost": np.asarray(lp.cost), "bounds": np.asarray(lp.bounds), "solution": sol.x,
              "objective": np.asarray(sol.fun), "b_eq": be, "b_ub": bu,
              "eq_dual": sol.eqlin.marginals, "ub_dual": sol.ineqlin.marginals,
              "lower_dual": sol.lower.marginals, "upper_dual": sol.upper.marginals}
    for name, matrix in (("A_eq", ae), ("A_ub", au)):
        result.update({name+"_data": matrix.data, name+"_indices": matrix.indices,
                       name+"_indptr": matrix.indptr, name+"_shape": np.asarray(matrix.shape)})
    return result


def solve(lp, path, extra=None):
    ae, au = lp.matrix(lp.eq), lp.matrix(lp.ub)
    be = np.asarray([rhs for _, rhs in lp.eq]); bu = np.asarray([rhs for _, rhs in lp.ub])
    start = time.monotonic()
    sol = linprog(lp.cost, A_eq=ae, b_eq=be, A_ub=au if len(bu) else None,
                  b_ub=bu if len(bu) else None, bounds=lp.bounds, method="highs", options=SOLVER_OPTIONS)
    elapsed = time.monotonic()-start
    if not sol.success:
        arrays = {"cost": lp.cost, "bounds": lp.bounds, "b_eq": be, "b_ub": bu}
        for name, matrix in (("A_eq", ae), ("A_ub", au)):
            arrays.update({name+"_data": matrix.data, name+"_indices": matrix.indices,
                           name+"_indptr": matrix.indptr, name+"_shape": matrix.shape})
        np.savez_compressed(path.with_name(path.stem+"_FAILED.npz"), **arrays)
        raise RuntimeError(f"{path.name}: {sol.message}")
    COUNTS["planning_lps"] += 1
    lower, upper = np.asarray(lp.bounds).T
    verify("primal_equality", ae@sol.x-be)
    verify("primal_inequality", np.maximum(au@sol.x-bu, 0))
    verify("bound_violation", np.maximum(np.maximum(lower-sol.x, sol.x-upper), 0))
    verify("ub_dual_sign", np.maximum(sol.ineqlin.marginals, 0))
    verify("lower_dual_sign", np.minimum(sol.lower.marginals, 0))
    verify("upper_dual_sign", np.maximum(sol.upper.marginals, 0))
    dual = float(be@sol.eqlin.marginals + bu@sol.ineqlin.marginals + lower@sol.lower.marginals + upper@sol.upper.marginals)
    verify("primal_dual_gap", sol.fun-dual)
    verify("stationarity", np.asarray(lp.cost)-ae.T@sol.eqlin.marginals-au.T@sol.ineqlin.marginals-sol.lower.marginals-sol.upper.marginals)
    arrays = certificate_arrays(lp, sol, ae, au, be, bu)
    if extra:
        arrays.update(extra)
    np.savez_compressed(path, **arrays)
    return sol, {"solver_seconds": elapsed, "primal_value": float(sol.fun), "dual_value": dual,
                 "variables": len(lp.cost), "equalities": len(lp.eq), "inequalities": len(lp.ub),
                 "iterations": int(sol.nit), "certificate_path": str(path)}


def replay(m, sol):
    rows = []
    for layer in m.levels[:-1]:
        for h in layer:
            mass = sol.x[m.w[h]]
            actions = np.maximum([sol.x[m.x[h, a]] for a in range(3)], 0.)
            actions = actions/actions.sum() if mass > 1e-13 and actions.sum() > 0 else np.array([0., 0., 1.])
            rows.append(actions)
    rows = np.asarray(rows); weights = realization(m.levels, rows)
    verify("policy_weight_replay", [weights[h]-sol.x[m.w[h]] for layer in m.levels for h in layer])
    E = experiment(m.levels, m.p, weights)
    verify("source_stochastic", E.sum(axis=1)-1)
    return E, rows, weights


def fixed_deficiency(Efull, T):
    """Independent fixed-experiment primal and TV minimax dual, with witnesses."""
    keep = np.flatnonzero(np.max(Efull, axis=0) > 0)
    E = Efull[:, keep]; X, Y = E.shape[1], T.shape[1]
    lp = LP()
    g = np.asarray([[lp.var() for _ in range(Y)] for _ in range(X)])
    d = lp.var(1.)
    for x in range(X):
        lp.row({i: 1 for i in g[x]}, 1, True)
    for theta in range(4):
        errors = []
        for y in range(Y):
            error = lp.var(); errors.append(error)
            row = {int(g[x, y]): E[theta, x] for x in range(X)}
            lp.row(row | {error: -1}, T[theta, y])
            lp.row({i: -v for i, v in row.items()} | {error: -1}, -T[theta, y])
        lp.row({i: .5 for i in errors} | {d: -1}, 0)
    sol = linprog(lp.cost, A_eq=lp.matrix(lp.eq), b_eq=[b for _, b in lp.eq],
                  A_ub=lp.matrix(lp.ub), b_ub=[b for _, b in lp.ub], bounds=lp.bounds,
                  method="highs", options=SOLVER_OPTIONS)
    if not sol.success:
        raise RuntimeError("Fixed source decoder: "+sol.message)
    COUNTS["deficiency_primal_lps"] += 1
    decoder = np.maximum(sol.x[g], 0.); decoder /= decoder.sum(axis=1, keepdims=True)
    primal = float(np.max(np.abs(E@decoder-T).sum(axis=1)/2))
    verify("decoder_row_sum", decoder.sum(axis=1)-1); verify("decoder_value", primal-sol.fun)
    dual = LP()
    alpha = np.asarray([dual.var() for _ in range(4)])
    b = np.asarray([[dual.var(-T[theta, y]) for y in range(Y)] for theta in range(4)])
    s = np.asarray([dual.var(1.) for _ in range(X)])
    dual.row({i: 1 for i in alpha}, 1, True)
    for theta in range(4):
        for y in range(Y):
            dual.row({int(b[theta, y]): 1, int(alpha[theta]): -1}, 0)
    for x in range(X):
        for y in range(Y):
            dual.row({int(b[theta, y]): E[theta, x] for theta in range(4)} | {int(s[x]): -1}, 0)
    ds = linprog(dual.cost, A_eq=dual.matrix(dual.eq), b_eq=[rhs for _, rhs in dual.eq],
                 A_ub=dual.matrix(dual.ub), b_ub=[rhs for _, rhs in dual.ub], bounds=dual.bounds,
                 method="highs", options=SOLVER_OPTIONS)
    if not ds.success:
        raise RuntimeError("Fixed source minimax dual: "+ds.message)
    COUNTS["deficiency_dual_lps"] += 1
    aa, bb = ds.x[alpha], ds.x[b]
    lower = float(np.sum(T*bb)-np.max(E.T@bb, axis=1).sum())
    verify("deficiency_primal_dual", primal-lower)
    return primal, {"source_indices": keep, "decoder": decoder, "dual_alpha": aa,
                    "dual_b": bb, "upper_value": np.asarray(primal), "lower_value": np.asarray(lower)}


def diagnostics(E, targets):
    deficits, witnesses = {}, {}
    for target in targets:
        value, witness = fixed_deficiency(E, target["kernel"])
        deficits[target["name"]] = value
        witnesses.update({target["name"]+"__"+name: array for name, array in witness.items()})
    return deficits, witnesses


def actual_cost(E, targets, deficits, objective, q):
    if objective == "native_minimax":
        return max(deficits[t["name"]] for t in targets[:6])
    if objective in NATIVE_COUNTS:
        return sum(t["weight"]*deficits[t["name"]] for t in targets[:NATIVE_COUNTS[objective]])
    return -posterior_value(E, q, objective)


def add_purpose_envelope(m, optimum, eta, name):
    original = np.asarray(m.lp.cost).copy()
    m.lp.row({i: float(c) for i, c in enumerate(original) if c}, optimum+eta)
    m.lp.cost = [0.] * len(m.lp.cost)
    mu, utility = purpose(name)
    for h in m.levels[-1]:
        epigraph = m.lp.var(1.)
        for coefficient in (utility * mu) @ m.p[h]:
            m.lp.row({m.w[h]: float(coefficient), epigraph: -1}, 0)
    return original


def purpose_benchmark(levels, p, name):
    mu, utility = purpose(name)
    values = {h: float(np.max((utility*mu)@p[h])) for h in levels[-1]}
    for layer in reversed(levels[:-1]):
        for h in layer:
            values[h] = max(sum(values[h+((a, o),)] for aa, o in EDGES if aa == a) for a in range(3))
    return values[()]


def bindings(m):
    return {"w_indices": np.asarray([m.w[h] for layer in m.levels for h in layer]),
            "x_indices": np.asarray([[m.x[h, a] for a in range(3)] for layer in m.levels[:-1] for h in layer]),
            "terminal_w_indices": np.asarray([m.w[h] for h in m.levels[-1]])}


def save_collector(out, row_id, m, sol, targets):
    E, rows, weights = replay(m, sol)
    deficits, witnesses = diagnostics(E, targets)
    policy_path = Path("policies")/(row_id+".npz")
    witness_path = Path("deficiency_witnesses")/(row_id+".npz")
    np.savez_compressed(out/policy_path, source_kernel=E, action_rows=rows,
                        realization_weights=[weights[h] for layer in m.levels for h in layer])
    np.savez_compressed(out/witness_path, **witnesses)
    return E, {"policy_path": str(policy_path), "deficiency_witness_path": str(witness_path),
               "target_deficiencies": deficits,
               "purpose_values": {name: purpose_value(E, name) for name in PURPOSE_NAMES},
               "actual_cost": actual_cost(E, targets, deficits, m.objective, m.planning_q),
               "active_terminal_histories": int(np.count_nonzero(E.sum(axis=0)>0)),
               "planning_prior_ig": None if m.planning_q is None else posterior_value(E, m.planning_q, "information"),
               "planning_prior_quadratic": None if m.planning_q is None else posterior_value(E, m.planning_q, "quadratic")}


def base_config(Hs, mode):
    return {"mode": mode, "worlds": WORLDS.tolist(), "actions": ["L", "R", "WAIT"],
            "observations": [0, 1], "histories": "layer order, then edges "+str(EDGES),
            "null_history_pruning": "omit exactly prefixes containing WAIT->1",
            "horizons": Hs, "noise_pairs": [[.1, .1], [.25, .25], [.1, .3]],
            "planning_q": [.5, .01], "fractions": [0., .01, .05],
            "secondary_absolute_eta": .005,
            "purpose_names": list(PURPOSE_NAMES), "target_names": list(TARGET_NAMES),
            "target_weights": dict(zip(TARGET_NAMES, WEIGHTS.tolist())), "native_counts": NATIVE_COUNTS,
            "normalization_name": "full_feasible_return_range",
            "normalization_derivation": "WAIT attains no data; every experiment dominates no data",
            "information_units": "bits", "aggregation": "terminal undiscounted",
            "scored_targets": list(TARGET_NAMES[:6]), "held_out_targets": list(TARGET_NAMES[6:]),
            "solver": "scipy.optimize.linprog(method=highs)", "solver_options": SOLVER_OPTIONS,
            "check_tolerance": TOL}


def run(args):
    start = time.monotonic()
    out = Path(args.output).resolve() if args.output else HERE/("smoke" if args.mode == "smoke" else "results")
    out.mkdir(parents=True, exist_ok=True)
    for name in ("certificates", "policies", "deficiency_witnesses"):
        (out/name).mkdir(exist_ok=True)
    Hs = args.horizons; config = base_config(Hs, args.mode); protocol_path = HERE/"PROTOCOL.md"
    if args.mode == "production" and not protocol_path.exists():
        raise RuntimeError("Production requires frozen PROTOCOL.md")
    report = {"schema_version": 1, "status": "running", "config": config,
              "started_utc": datetime.now(timezone.utc).isoformat(), "source_sha256": digest(__file__),
              "protocol_sha256": digest(protocol_path) if protocol_path.exists() else None,
              "versions": {"python": sys.version, "numpy": np.__version__, "scipy": scipy.__version__, "platform": platform.platform()},
              "arithmetic": "float64 numerical primal/dual certificates; not interval proofs",
              "optima": [], "rows": [], "failures": []}
    if args.resume and (out/"results.json").exists():
        old = json.loads((out/"results.json").read_text())
        if old["source_sha256"] != report["source_sha256"]:
            raise RuntimeError("Refuse resume after planner source changed; use fresh output directory")
        if old["protocol_sha256"] != report["protocol_sha256"]:
            raise RuntimeError("Refuse resume after protocol changed")
        report = old; report["status"] = "running"
        report["config"]["horizons"] = sorted(set(old["config"]["horizons"]+Hs))
        RESIDUALS.update(old.get("max_residuals", {})); COUNTS.update(old.get("counts", COUNTS))
    def checkpoint():
        report["counts"] = COUNTS.copy(); report["max_residuals"] = RESIDUALS.copy()
        report["updated_utc"] = datetime.now(timezone.utc).isoformat()
        report["run_seconds"] = time.monotonic()-start
        write_json(out/"results.json", report)
    checkpoint()
    noises = config["noise_pairs"] if args.mode == "production" else [[.1, .1]]
    specs = [(kind, q) for q in config["planning_q"] for kind in ("information", "quadratic")]
    specs += [(kind, None) for kind in NATIVE_COUNTS]
    if args.mode == "smoke":
        specs = [("information", .01), ("native_singles", None), ("native_repeats", None), ("native_minimax", None)]
    if args.tolerances == "secondary":
        specs = [(kind, q) for kind, q in specs if kind in NATIVE_COUNTS and kind != "native_minimax"]
    if args.objectives:
        specs = [(kind, q) for kind, q in specs if kind in args.objectives]
    fractions = config["fractions"] if args.mode == "production" else [0., .01]
    purposes = PURPOSE_NAMES if args.mode == "production" else ("U", "world")
    if args.purposes:
        purposes = tuple(args.purposes)
    report["executed_subset"] = {"noises": noises, "objective_specs": specs, "fractions": fractions, "purposes": purposes, "tolerances": args.tolerances}
    done_optima = {row["id"]: row for row in report["optima"]}; done_rows = {row["id"] for row in report["rows"]}
    try:
        for noise in noises:
            noise_tag = "e"+"_".join(str(x).replace(".", "p") for x in noise)
            targets = target_library(noise)
            np.savez_compressed(out/("targets_"+noise_tag+".npz"), **{t["name"]: t["kernel"] for t in targets})
            write_json(out/("targets_"+noise_tag+".json"), [{k: v for k, v in t.items() if k != "kernel"} for t in targets])
            null_deficits = {t["name"]: fixed_deficiency(np.ones((4, 1)), t["kernel"])[0] for t in targets}
            for H in Hs:
                lev = histories(H); p = behavior(lev, noise)
                write_json(out/f"histories_H{H}.json", {"levels": lev,
                           "policy_histories": [h for layer in lev[:-1] for h in layer],
                           "terminal_histories": lev[-1], "edges": EDGES})
                benchmarks = {name: purpose_benchmark(lev, p, name) for name in PURPOSE_NAMES}
                for objective, q in specs:
                    tag = f"H{H}_{noise_tag}_{objective}_q{q}"
                    common = {"H": H, "noise": list(noise), "objective": objective, "planning_q": q,
                              "prior_independent": q is None,
                              "planning_q_applicability": config["planning_q"] if q is None else [q],
                              "native_prior_cache": "single solve reused for both planning priors" if q is None else None,
                              "purpose_benchmarks": benchmarks}
                    if tag in done_optima:
                        optrow = done_optima[tag]
                    else:
                        m = model(H, noise, targets, objective, q)
                        cp = Path("certificates")/(tag+"_optimum.npz")
                        sol, info = solve(m.lp, out/cp, bindings(m))
                        E, collector = save_collector(out, tag+"_optimum", m, sol, targets)
                        verify("actual_optimum_cost", collector["actual_cost"]-sol.fun)
                        null_cost = actual_cost(np.ones((4, 1)), targets, null_deficits, objective, q)
                        scale = null_cost-float(sol.fun)
                        if scale <= 0:
                            raise AssertionError(("nonpositive full range", tag, scale))
                        info["certificate_path"] = str(cp)
                        optrow = common | collector | info | {"id": tag, "optimum_cost": float(sol.fun),
                            "null_cost": null_cost, "normalization_scale": scale,
                            "normalization_name": "full_feasible_return_range",
                            "normalization_scale_interval": [null_cost-info["primal_value"], null_cost-info["dual_value"]]}
                        report["optima"].append(optrow); done_optima[tag] = optrow; checkpoint()
                    tolerances = ([("full_feasible_return_range", fraction,
                                    fraction*optrow["normalization_scale"]) for fraction in fractions]
                                  if args.tolerances != "secondary" else [])
                    if args.tolerances != "primary" and objective in NATIVE_COUNTS and objective != "native_minimax":
                        tolerances.append(("absolute", None, .005))
                    for (normalization, fraction, eta), name in product(tolerances, purposes):
                        suffix = f"f{fraction}" if fraction is not None else "absolute0.005"
                        row_id = f"{tag}_{suffix}_{name}"
                        if row_id in done_rows:
                            continue
                        m = model(H, noise, targets, objective, q)
                        original = add_purpose_envelope(m, optrow["optimum_cost"], eta, name)
                        cp = Path("certificates")/(row_id+".npz")
                        extra = bindings(m) | {"original_objective_cost": original, "objective_cut_rhs": optrow["optimum_cost"]+eta}
                        sol, info = solve(m.lp, out/cp, extra)
                        E, collector = save_collector(out, row_id, m, sol, targets)
                        value = collector["purpose_values"][name]
                        verify("purpose_envelope_replay", value-sol.fun)
                        gap = collector["actual_cost"]-optrow["optimum_cost"]
                        verify("near_optimal_feasibility", max(0., gap-eta, -gap))
                        info["certificate_path"] = str(cp)
                        row = common | collector | info | {"id": row_id, "optimum_id": tag,
                            "fraction": fraction, "eta": eta, "normalization_scale": optrow["normalization_scale"],
                            "normalization_name": normalization, "optimum_cost": optrow["optimum_cost"],
                            "actual_gap": gap, "purpose": name, "purpose_value": value, "purpose_loss": benchmarks[name]-value}
                        report["rows"].append(row); done_rows.add(row_id); checkpoint()
                    print(tag, "optimum", round(optrow["optimum_cost"], 9), "endpoints", len(report["rows"]), flush=True)
        report["status"] = "passed_development_smoke" if args.mode == "smoke" else "passed_requested_stage"
        checkpoint()
        print(json.dumps({"status": report["status"], "optima": len(report["optima"]), "endpoints": len(report["rows"]),
                          "seconds": report["run_seconds"], "max_residuals": RESIDUALS}, indent=2), flush=True)
    except Exception:
        report["status"] = "failed"
        report["failures"].append({"utc": datetime.now(timezone.utc).isoformat(), "traceback": traceback.format_exc()})
        checkpoint()
        raise


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("smoke", "production"), default="smoke")
    parser.add_argument("--horizons", type=int, nargs="+", default=[3])
    parser.add_argument("--output"); parser.add_argument("--resume", action="store_true")
    parser.add_argument("--tolerances", choices=("primary", "secondary", "all"), default="primary")
    parser.add_argument("--objectives", nargs="+", choices=["information", "quadratic", *NATIVE_COUNTS])
    parser.add_argument("--purposes", nargs="+", choices=PURPOSE_NAMES)
    args = parser.parse_args()
    if any(H not in (1, 2, 3, 4) for H in args.horizons):
        parser.error("Supported horizons are 1 through 4")
    return args


if __name__ == "__main__":
    run(parse_args())
