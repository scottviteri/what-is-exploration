#!/usr/bin/env python3
"""Independent audit of noisy diagnostic transfer.

This module does not import compute.py or any predecessor planner. It builds
literal controlled histories, target laws, Bayesian dynamic programs, and a
separate fixed-channel stochastic-decoder LP. The LP certificates saved by the
planner are checked algebraically, not accepted on solver status alone.

Run --controls before production, then --input results/results.json. Results
written by this script have audit_ prefixes and never replace production files.
Numerical residual checks are not interval-arithmetic proofs.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
import hashlib
from itertools import product
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix, csr_matrix


HERE = Path(__file__).resolve().parent
WORLDS = tuple(product((0, 1), repeat=2))
CHILDREN = ((0, 0), (0, 1), (1, 0), (1, 1), (2, 0))
TARGETS = ("L", "R", "tagged", "LR", "LLL", "RRR", "LLR", "LRR", "adaptive_L")
WEIGHTS = {"L": .2, "R": .2, "tagged": .1, "LR": .1, "LLL": .1, "RRR": .1}
LIBRARIES = {
    "native_singles": ("L", "R"),
    "native_tagged": ("L", "R", "tagged"),
    "native_joint": ("L", "R", "tagged", "LR"),
    "native_repeats": ("L", "R", "tagged", "LR", "LLL", "RRR"),
    "native_minimax": ("L", "R", "tagged", "LR", "LLL", "RRR"),
}
TOL = 4e-7


class Checks:
    def __init__(self):
        self.errors = {}
        self.count = 0
        self.decoder_lps = 0
        self.cache_hits = 0
        self.channel_cache = {}

    def close(self, name, actual, expected, tol=TOL):
        error = float(np.max(np.abs(np.asarray(actual)-np.asarray(expected)), initial=0))
        self.errors[name] = max(self.errors.get(name, 0.), error)
        self.count += 1
        if not np.isfinite(error) or error > tol:
            raise AssertionError((name, error, tol))
        return error

    def at_most(self, name, actual, upper, tol=TOL):
        return self.close(name, max(0., float(actual)-float(upper)), 0., tol)


@lru_cache(None)
def histories(H):
    levels = [((),)]
    for _ in range(H):
        levels.append(tuple(h+(ao,) for h in levels[-1] for ao in CHILDREN))
    return tuple(levels)


def transition(theta, action, observation, noise):
    if action == 2:
        return float(observation == 0)
    return 1-noise[action] if theta[action] == observation else noise[action]


def literal_record(H, noise, action_rows, checks):
    """Forward execute the supplied history policy separately in each world."""
    levels = histories(H)
    before = tuple(h for layer in levels[:-1] for h in layer)
    rows = np.asarray(action_rows, dtype=float)
    if rows.shape != (len(before), 3):
        raise AssertionError(("policy_shape", rows.shape, len(before)))
    checks.close("policy_row_sum", rows.sum(axis=1), np.ones(len(before)))
    checks.at_most("negative_policy_probability", -float(rows.min(initial=0)), 0.)
    policies = dict(zip(before, rows))
    laws = {(): np.ones(4)}
    weights = {(): 1.}
    for layer in levels[:-1]:
        for h in layer:
            for a, o in CHILDREN:
                child = h+((a, o),)
                likelihood = np.array([transition(w, a, o, noise) for w in WORLDS])
                laws[child] = laws[h] * policies[h][a] * likelihood
                weights[child] = weights[h] * policies[h][a]
    E = np.column_stack([laws[h] for h in levels[-1]])
    checks.close("record_row_sum", E.sum(axis=1), np.ones(4))
    return E, np.array([weights[h] for layer in levels for h in layer])


def target_kernel(name, noise):
    """Target columns are literal outcomes of the declared native schedule."""
    if name == "tagged":
        return np.concatenate((target_kernel("L", noise)/2,
                               target_kernel("R", noise)/2), axis=1)
    if name == "adaptive_L":
        outcomes = tuple(product((0, 1), repeat=3))
        return np.array([[np.prod([transition(theta, a, o, noise)
                                   for a, o in zip((0, obs[0], obs[0]), obs)])
                          for obs in outcomes] for theta in WORLDS])
    actions = tuple(0 if a == "L" else 1 for a in name)
    outcomes = tuple(product((0, 1), repeat=len(actions)))
    return np.array([[np.prod([transition(theta, a, o, noise)
                              for a, o in zip(actions, obs)])
                      for obs in outcomes] for theta in WORLDS])


def prior(q):
    return np.array([(q if u else 1-q)/2 for u, v in WORLDS])


def posterior_potential(rho, objective):
    if objective == "information":
        positive = rho > 0
        return float(np.sum(rho[positive]*np.log2(rho[positive])))
    if objective == "quadratic":
        return float(rho@rho)
    raise ValueError(objective)


def posterior_gain(E, q, objective):
    mu = prior(q)
    joint = mu[:, None]*E
    masses = joint.sum(axis=0)
    good = masses > 0
    posterior = joint[:, good]/masses[good]
    total = sum(m*posterior_potential(rho, objective)
                for m, rho in zip(masses[good], posterior.T))
    return total-posterior_potential(mu, objective)


def purpose_spec(name):
    # Accept the descriptive names independently of dictionary insertion order.
    normalized = {"guess_U": "U", "guess_V": "V", "guess_world": "world",
                  "guess_parity": "parity", "asymmetric_U": "U_asymmetric",
                  "guess_U_asymmetric": "U_asymmetric"}.get(name, name)
    mu = prior(.25) if normalized == "U_asymmetric" else np.ones(4)/4
    if normalized in ("U", "U_asymmetric"):
        labels = np.array([u for u, v in WORLDS])
    elif normalized == "V":
        labels = np.array([v for u, v in WORLDS])
    elif normalized == "parity":
        labels = np.array([u ^ v for u, v in WORLDS])
    elif normalized == "world":
        labels = np.arange(4)
    else:
        raise ValueError(("unknown purpose", name))
    utility = (labels[:, None] == np.arange(labels.max()+1)[None, :]).astype(float)
    return mu, utility


def purpose_value(E, name):
    mu, utility = purpose_spec(name)
    return float(np.max(utility.T@(mu[:, None]*E), axis=0).sum())


def decoder_deficiency(E, T, checks):
    """Independent direct decoder LP, without policy realization variables.

    Remove only exactly zero columns. No approximate source compression or
    low-probability pruning is used. Return the matching decoder certificate.
    """
    source = E[:, np.any(E != 0, axis=0)]
    key = (source.shape, source.tobytes(), T.shape, T.tobytes())
    if key in checks.channel_cache:
        checks.cache_hits += 1
        return checks.channel_cache[key]
    n, X = source.shape
    Y = T.shape[1]
    variables = X*Y+n*Y+1
    c = np.zeros(variables)
    c[-1] = 1.
    eq_r, eq_c, eq_v = [], [], []
    for x in range(X):
        for y in range(Y):
            eq_r.append(x); eq_c.append(x*Y+y); eq_v.append(1.)
    ae = coo_matrix((eq_v, (eq_r, eq_c)), shape=(X, variables)).tocsr()
    rr, cc, vv, rhs = [], [], [], []
    for theta in range(n):
        for y in range(Y):
            for sign in (1., -1.):
                r = len(rhs)
                for x in range(X):
                    if source[theta, x]:
                        rr.append(r); cc.append(x*Y+y); vv.append(sign*source[theta, x])
                rr.append(r); cc.append(X*Y+theta*Y+y); vv.append(-1.)
                rhs.append(sign*T[theta, y])
        r = len(rhs)
        for y in range(Y):
            rr.append(r); cc.append(X*Y+theta*Y+y); vv.append(.5)
        rr.append(r); cc.append(variables-1); vv.append(-1.)
        rhs.append(0.)
    au = coo_matrix((vv, (rr, cc)), shape=(len(rhs), variables)).tocsr()
    be, bu = np.ones(X), np.array(rhs)
    sol = linprog(c, A_eq=ae, b_eq=be, A_ub=au, b_ub=bu,
                  bounds=(0., None), method="highs",
                  options={"dual_feasibility_tolerance": 1e-9,
                           "primal_feasibility_tolerance": 1e-9})
    if not sol.success:
        raise RuntimeError(("independent decoder LP", sol.status, sol.message))
    checks.decoder_lps += 1
    decoder = sol.x[:X*Y].reshape(X, Y)
    checks.close("independent_decoder_rows", decoder.sum(axis=1), np.ones(X))
    checks.close("independent_decoder_error", np.max(abs(source@decoder-T).sum(axis=1)/2), sol.fun)
    dual = float(be@sol.eqlin.marginals+bu@sol.ineqlin.marginals)
    checks.close("independent_decoder_dual_gap", sol.fun, dual)
    checks.close("independent_decoder_stationarity", c,
                 ae.T@sol.eqlin.marginals+au.T@sol.ineqlin.marginals+sol.lower.marginals)
    value = float(sol.fun)
    checks.channel_cache[key] = value
    return value


@lru_cache(None)
def posterior_optimum(H, noise, q, objective):
    """Independent count/belief Bellman recursion including WAIT.

    Sensor outcomes are conditionally independent and policy factors cancel.
    Counts therefore determine the posterior, and the remaining budget plus
    posterior determines every continuation law in this specific interface.
    """
    mu = prior(q)

    @lru_cache(None)
    def solve(left, nL, sL, nR, sR):
        likelihood = np.ones(4)
        for i, theta in enumerate(WORLDS):
            for a, n, s in ((0, nL, sL), (1, nR, sR)):
                p = 1-noise[a] if theta[a] else noise[a]
                likelihood[i] *= p**s*(1-p)**(n-s)
        rho = mu*likelihood
        rho /= rho.sum()
        if left == 0:
            return posterior_potential(rho, objective)
        candidates = [solve(left-1, nL, sL, nR, sR)]
        for a in (0, 1):
            expected = 0.
            for obs in (0, 1):
                prob = sum(rho[i]*transition(theta, a, obs, noise)
                           for i, theta in enumerate(WORLDS))
                state = (nL+1, sL+obs, nR, sR) if a == 0 else (nL, sL, nR+1, sR+obs)
                expected += prob*solve(left-1, *state)
            candidates.append(expected)
        return max(candidates)

    return solve(H, 0, 0, 0, 0)-posterior_potential(mu, objective)


@lru_cache(None)
def purpose_optimum(H, noise, purpose):
    """Independent Bayes decision planning on sufficient measurement counts."""
    mu, utility = purpose_spec(purpose)

    @lru_cache(None)
    def solve(left, nL, sL, nR, sR):
        likelihood = np.ones(4)
        for i, theta in enumerate(WORLDS):
            for a, n, s in ((0, nL, sL), (1, nR, sR)):
                p = 1-noise[a] if theta[a] else noise[a]
                likelihood[i] *= p**s*(1-p)**(n-s)
        rho = mu*likelihood
        rho /= rho.sum()
        if left == 0:
            return float(np.max(rho@utility))
        candidates = [solve(left-1, nL, sL, nR, sR)]
        for a in (0, 1):
            expected = 0.
            for obs in (0, 1):
                prob = sum(rho[i]*transition(theta, a, obs, noise)
                           for i, theta in enumerate(WORLDS))
                state = (nL+1, sL+obs, nR, sR) if a == 0 else (nL, sL, nR+1, sR+obs)
                expected += prob*solve(left-1, *state)
            candidates.append(expected)
        return max(candidates)

    return solve(H, 0, 0, 0, 0)


def pure_policy_values(H, noise, qs, checks):
    """Enumerate deterministic observation trees; H=3 has 3^7=2187.

    WAIT's impossible observation-1 branches create harmless duplicates. Every
    deterministic executable policy is represented; own earlier actions are
    determined by its observation-tree prescriptions.
    """
    if H > 3:
        raise ValueError("Pure enumeration intentionally bounded to H<=3")
    before = [h for layer in histories(H)[:-1] for h in layer]
    indices = []
    for h in before:
        obs_index = sum(o*2**(len(h)-i-1) for i, (_, o) in enumerate(h))
        indices.append(2**len(h)-1+obs_index)
    maxima = {(q, k): -np.inf for q in qs for k in ("information", "quadratic")}
    purpose_maxima = {k: -np.inf for k in ("U", "V", "world", "parity", "U_asymmetric")}
    count = 0
    eye = np.eye(3)
    for choices in product(range(3), repeat=2**H-1):
        rows = eye[[choices[i] for i in indices]]
        E, _ = literal_record(H, noise, rows, checks)
        for key in maxima:
            maxima[key] = max(maxima[key], posterior_gain(E, *key))
        for name in purpose_maxima:
            purpose_maxima[name] = max(purpose_maxima[name], purpose_value(E, name))
        count += 1
    for (q, kind), value in maxima.items():
        checks.close("DP_pure_enumeration", posterior_optimum(H, tuple(noise), q, kind), value)
    for name, value in purpose_maxima.items():
        checks.close("purpose_DP_pure_enumeration", purpose_optimum(H, tuple(noise), name), value)
    return count, {f"q{q}_{k}": v for (q, k), v in maxima.items()}, purpose_maxima


def saved_lp_certificate(path, checks):
    """Check feasibility, signs, complementary slackness and duality."""
    with np.load(path, allow_pickle=False) as z:
        def matrix(prefix):
            return csr_matrix((z[prefix+"_data"], z[prefix+"_indices"], z[prefix+"_indptr"]),
                              shape=tuple(z[prefix+"_shape"]))
        ae, au = matrix("A_eq"), matrix("A_ub")
        be, bu, c, x = z["b_eq"], z["b_ub"], z["cost"], z["solution"]
        bounds = z["bounds"]
        lower, upper = bounds[:, 0], bounds[:, 1]
        de, du, dl, dh = (z[k] for k in ("eq_dual", "ub_dual", "lower_dual", "upper_dual"))
        checks.close("saved_primal_equality", ae@x, be)
        checks.at_most("saved_primal_inequality", np.max(au@x-bu, initial=0), 0.)
        checks.at_most("saved_primal_lower", np.max(lower-x, initial=0), 0.)
        checks.at_most("saved_primal_upper", np.max(x-upper, initial=0), 0.)
        checks.at_most("saved_dual_ub_sign", np.max(du, initial=0), 0.)
        checks.at_most("saved_dual_lower_sign", -np.min(dl, initial=0), 0.)
        checks.at_most("saved_dual_upper_sign", np.max(dh, initial=0), 0.)
        checks.close("saved_stationarity", c, ae.T@de+au.T@du+dl+dh)
        finite_lo, finite_hi = np.isfinite(lower), np.isfinite(upper)
        checks.close("saved_unbounded_lower_dual", dl[~finite_lo], np.zeros((~finite_lo).sum()))
        checks.close("saved_unbounded_upper_dual", dh[~finite_hi], np.zeros((~finite_hi).sum()))
        dual = be@de+bu@du+lower[finite_lo]@dl[finite_lo]+upper[finite_hi]@dh[finite_hi]
        checks.close("saved_dual_gap", c@x, dual)
        checks.close("saved_objective", c@x, z["objective"])
        checks.close("saved_ub_complementarity", (au@x-bu)*du, np.zeros(len(du)))
        checks.close("saved_lower_complementarity", (x[finite_lo]-lower[finite_lo])*dl[finite_lo], np.zeros(finite_lo.sum()))
        checks.close("saved_upper_complementarity", (upper[finite_hi]-x[finite_hi])*dh[finite_hi], np.zeros(finite_hi.sum()))
        return dict(variables=len(x), equalities=len(be), inequalities=len(bu), objective=float(c@x))


def objective_cost(name, E, noise, q, deficits):
    if name in ("information", "quadratic"):
        return -posterior_gain(E, q, name)
    if name == "native_minimax":
        return max(deficits[k] for k in LIBRARIES[name])
    return sum(WEIGHTS[k]*deficits[k] for k in LIBRARIES[name])


def rational_h4_blind_spot(e, checks):
    """Exact pilot-feasible marginal decoders and matching joint certificates.

    Independent fair tie coins turn coordinate MAP guesses into BSC(e) marginal
    decoders. Their product is an explicit joint decoder. Its TV error and the
    parity-decision disadvantage both equal twice the joint-guessing gap.
    """
    b = 2*e*(1-e)
    a1, a3 = 1-e, 1-3*e**2+2*e**3
    schedules = {"LLLR": (1-b)/2, "RRRL": (1-b)/2,
                 "LLLL": b/2, "RRRR": b/2}
    columns = []
    for schedule, weight in schedules.items():
        actions = tuple(0 if s == "L" else 1 for s in schedule)
        for obs in product((0, 1), repeat=4):
            h = tuple(zip(actions, obs))
            mass = []
            for theta in WORLDS:
                p = weight
                for a, o in h:
                    p *= 1-e if theta[a] == o else e
                mass.append(p)
            columns.append((h, mass))
    assert all(sum(column[i] for _, column in columns) == 1 for i in range(4))
    bit_decoders = []
    for bit in (0, 1):
        decoder = []
        for _, column in columns:
            totals = [sum(column[i] for i, theta in enumerate(WORLDS) if theta[bit] == v)
                      for v in (0, 1)]
            if totals[0] == totals[1]:
                decoder.append((Fraction(1, 2), Fraction(1, 2)))
            else:
                choice = int(totals[1] > totals[0])
                decoder.append((Fraction(choice == 0), Fraction(choice == 1)))
        for i, theta in enumerate(WORLDS):
            for v in (0, 1):
                decoded = sum(column[i]*g[v] for (_, column), g in zip(columns, decoder))
                assert decoded == (1-e if theta[bit] == v else e)
        bit_decoders.append(decoder)
    joint_value = sum(max(column) for _, column in columns)/4
    gap = (a3-a1)**2
    assert joint_value == a1*a1-gap
    joint_decoder = [[g0[u]*g1[v] for u, v in WORLDS]
                     for g0, g1 in zip(*bit_decoders)]
    decoded_rows, target_rows = [], []
    for i, theta in enumerate(WORLDS):
        decoded = [sum(column[i]*g[j] for (_, column), g in zip(columns, joint_decoder))
                   for j in range(4)]
        target = [(1-e if u == theta[0] else e)*(1-e if v == theta[1] else e)
                  for u, v in WORLDS]
        assert sum(abs(x-y) for x, y in zip(decoded, target))/2 == 2*gap
        decoded_rows.append(decoded);target_rows.append(target)
    parity_value = sum(max(sum(column[i] for i, (u, v) in enumerate(WORLDS) if u ^ v == parity)
                           for parity in (0, 1)) for _, column in columns)/4
    target_parity = (1-e)**2+e**2
    assert target_parity-parity_value == 2*gap
    # Independently realize the same schedule lottery as a behavioral policy.
    schedule_actions = {tuple(0 if s == "L" else 1 for s in name): weight
                        for name, weight in schedules.items()}
    action_rows = []
    for layer in histories(4)[:-1]:
        for h in layer:
            prefix = tuple(a for a, o in h)
            matching = [(actions, weight) for actions, weight in schedule_actions.items()
                        if actions[:len(h)] == prefix]
            total = sum(weight for actions, weight in matching)
            row = [Fraction(0)]*3
            if total:
                for actions, weight in matching:
                    row[actions[len(h)]] += weight/total
            else:
                row[2] = Fraction(1)
            action_rows.append([float(x) for x in row])
    noise = (float(e), float(e))
    E, _ = literal_record(4, noise, action_rows, checks)
    by_history = dict(columns)
    expected = np.array([[float(by_history[h][i]) if h in by_history else 0.
                          for h in histories(4)[-1]] for i in range(4)])
    checks.close("H4_literal_rational_record", E, expected)
    checks.close("H4_rational_joint_value", purpose_value(E, "world"), float(joint_value))
    checks.close("H4_rational_parity_value", purpose_value(E, "parity"), float(parity_value))
    deficits = {name: decoder_deficiency(E, target_kernel(name, noise), checks) for name in TARGETS}
    for name in ("L", "R", "tagged"):
        checks.close("H4_exact_marginal_simulation", deficits[name], 0.)
    checks.close("H4_exact_joint_deficiency", deficits["LR"], float(2*gap))
    return dict(noise=str(e), schedules={k: str(v) for k, v in schedules.items()},
                exact_marginal_decoders=[[[str(x) for x in row] for row in decoder] for decoder in bit_decoders],
                exact_joint_decoder=[[str(x) for x in row] for row in joint_decoder],
                exact_decoded_joint_rows=[[str(x) for x in row] for row in decoded_rows],
                exact_LR_target_rows=[[str(x) for x in row] for row in target_rows],
                exact_joint_guessing_value=str(joint_value), exact_LR_joint_guessing_value=str(a1*a1),
                exact_parity_value=str(parity_value), exact_LR_parity_value=str(target_parity),
                exact_joint_guessing_loss=str(gap), exact_joint_deficiency=str(2*gap),
                numerical_native_deficiencies=deficits,
                scope="Exact rational marginal decoders and matching joint decoder/parity certificates; independently replayed as a native behavioral policy.")


def controls(checks):
    rows = []
    for e in (Fraction(1, 10), Fraction(1, 4), Fraction(3, 10)):
        noise = (float(e), float(e))
        source = target_kernel("LR", noise)
        e3 = 3*e*e-2*e*e*e
        improvement = e-e3
        assert improvement == e*(1-e)*(1-2*e)
        for name in ("L", "R", "tagged", "LR"):
            checks.close("rational_short_target_zero", decoder_deficiency(source, target_kernel(name, noise), checks), 0.)
        for name in ("LLL", "RRR"):
            value = decoder_deficiency(source, target_kernel(name, noise), checks)
            checks.close("rational_repetition_gap", value, float(improvement))
        rows.append(dict(noise=str(e), single_error=str(e), majority_three_error=str(e3),
                         repeat_deficiency=str(improvement), short_target_errors=0))
        for name in TARGETS:
            T = target_kernel(name, noise)
            checks.close("target_rows", T.sum(axis=1), np.ones(4))
            checks.close("self_simulation", decoder_deficiency(T, T, checks), 0.)
        # Literal WAIT policy yields a constant experiment, not fresh sensor noise.
        H = 2
        E, _ = literal_record(H, noise, np.tile((0., 0., 1.), (len(histories(H)[0])+len(histories(H)[1]), 1)), checks)
        for kind in ("information", "quadratic"):
            checks.close("WAIT_zero_posterior_gain", posterior_gain(E, .01, kind), 0.)
        for purpose in ("U", "V", "world", "parity", "U_asymmetric"):
            checks.close("WAIT_purpose", purpose_value(E, purpose), purpose_value(np.ones((4, 1)), purpose))
    # Uninformative sensors make every declared target a constant experiment.
    for name in TARGETS:
        checks.close("uninformative_sensor", decoder_deficiency(np.ones((4, 1)), target_kernel(name, (.5, .5)), checks), 0.)
    # A noiseless joint record can reproduce every target.
    for name in TARGETS:
        checks.close("noiseless_joint_top", decoder_deficiency(target_kernel("LR", (0., 0.)), target_kernel(name, (0., 0.)), checks), 0.)
    enumerations = []
    for noise in ((.1, .1), (.25, .25), (.1, .3)):
        count, maxima, purpose_maxima = pure_policy_values(3, noise, (.5, .01), checks)
        enumerations.append(dict(H=3, noise=noise, pure_policy_count=count,
                                 posterior_maxima=maxima, purpose_maxima=purpose_maxima))
    blind_spots = [rational_h4_blind_spot(e, checks) for e in (Fraction(1, 10), Fraction(1, 4))]
    return dict(rational_repetition_controls=rows, independent_pure_enumerations=enumerations,
                rational_H4_blind_spots=blind_spots)


def saved_deficiency_witness(path, E, targets, deficits, checks):
    with np.load(path, allow_pickle=False) as z:
        for name, T in targets.items():
            prefix = name+"__"
            source = E[:, z[prefix+"source_indices"]]
            checks.close("saved_decoder_source_mass", source.sum(axis=1), E.sum(axis=1))
            G, alpha, payoff = (z[prefix+k] for k in ("decoder", "dual_alpha", "dual_b"))
            checks.close("saved_decoder_rows", G.sum(axis=1), np.ones(G.shape[0]))
            checks.at_most("saved_decoder_nonnegative", -G.min(initial=0), 0.)
            checks.close("saved_decision_prior", alpha.sum(), 1.)
            checks.at_most("saved_decision_prior_nonnegative", -alpha.min(initial=0), 0.)
            checks.at_most("saved_decision_payoff_nonnegative", -payoff.min(initial=0), 0.)
            checks.at_most("saved_decision_payoff_upper", np.max(payoff-alpha[:, None], initial=0), 0.)
            upper = float(np.max(abs(source@G-T).sum(axis=1)/2))
            lower = float(np.sum(T*payoff)-np.max(source.T@payoff, axis=1).sum())
            checks.close("saved_decoder_reported_upper", upper, z[prefix+"upper_value"])
            checks.close("saved_decision_reported_lower", lower, z[prefix+"lower_value"])
            checks.close("saved_decoder_decision_bracket", upper, lower)
            checks.close("saved_vs_independent_deficiency", upper, deficits[name])


def saved_target_and_history_artifacts(base, noise, H, targets, checks):
    tag = "_".join(str(float(e)).replace(".", "p") for e in noise)
    with np.load(base/f"targets_e{tag}.npz", allow_pickle=False) as z:
        for name, T in targets.items():
            checks.close("independent_target_kernel", z[name], T)
    manifest = json.loads((base/f"targets_e{tag}.json").read_text())
    for entry in manifest:
        name = entry["name"]
        checks.close("target_manifest_weight", entry["weight"], WEIGHTS.get(name, 0.))
        signals = [tuple(tuple(ao) for ao in h) for h in entry["signals"]]
        if len(set(signals)) != len(signals):
            raise AssertionError(("duplicate target signal", name))
        literal = []
        for theta in WORLDS:
            row = []
            for h in signals:
                if name == "tagged":
                    assert len(h) == 1 and h[0][0] in (0, 1)
                    factor = .5
                elif name == "adaptive_L":
                    assert len(h) == 3 and tuple(a for a, o in h) == (0, h[0][1], h[0][1])
                    factor = 1.
                else:
                    assert tuple(a for a, o in h) == tuple(0 if a == "L" else 1 for a in name)
                    factor = 1.
                row.append(factor*np.prod([transition(theta, a, o, noise) for a, o in h]))
            literal.append(row)
        checks.close("literal_target_manifest", literal, targets[name])
    saved = json.loads((base/f"histories_H{H}.json").read_text())
    expected = histories(H)
    for key, hs in (("policy_histories", [h for layer in expected[:-1] for h in layer]),
                    ("terminal_histories", expected[-1])):
        decoded = tuple(tuple(tuple(ao) for ao in h) for h in saved[key])
        if decoded != tuple(hs):
            raise AssertionError(("history order", H, key))


def fraction_linear_solve(rows, rhs):
    """Independent four-variable exact elimination for arrangement vertices."""
    matrix = [[Fraction(x) for x in row]+[Fraction(b)] for row, b in zip(rows, rhs)]
    n = len(rhs)
    for col in range(n):
        pivots = [i for i in range(col, n) if matrix[i][col]]
        if not pivots:
            return None
        pivot = pivots[0]
        matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
        divisor = matrix[col][col]
        matrix[col] = [x/divisor for x in matrix[col]]
        for i in range(n):
            if i != col:
                factor = matrix[i][col]
                matrix[i] = [x-factor*y for x, y in zip(matrix[i], matrix[col])]
    return tuple(row[-1] for row in matrix)


def independent_transfer_certificates(path):
    """Check exact affine decoder bounds on all marginal-sign-cell vertices.

    The arrangement uses the simplex faces and two marginal hyperplanes.
    Enumerating their intersections is independent of the producer's four
    signed-halfspace enumeration. Convexity on each cell supplies the extension
    to its interior; this routine checks the finite certificate hypotheses.
    """
    from itertools import combinations
    data = json.loads(path.read_text())
    count = 0
    for cert in data['certificates']:
        eps = tuple(map(Fraction, cert['diagnostic_eps']))
        target_eps = tuple(map(Fraction, cert['eps']))
        w = tuple(map(Fraction, cert['weights']))
        decoder = [list(map(Fraction, row)) for row in cert['decoder']]
        b, k = Fraction(cert['intercept']), Fraction(cert['slope'])
        assert b >= 0 and k >= 0 and sum(w) == 1 and all(x > 0 for x in w)
        assert all(sum(row) == 1 and min(row) >= 0 for row in decoder)
        hyperplanes = [tuple(int(i == j) for i in range(4)) for j in range(4)]
        hyperplanes += [(0, 0, 1, 1), (0, 1, 0, 1)]
        rhs = [Fraction(0)]*4+list(eps)
        vertices = set()
        for active in combinations(range(6), 3):
            p = fraction_linear_solve([(1, 1, 1, 1)]+[hyperplanes[i] for i in active],
                                      [Fraction(1)]+[rhs[i] for i in active])
            if p is not None and min(p) >= 0:
                vertices.add(p)
        assert len(vertices) == cert['canonical_cell_vertices']
        word = cert['word']
        length = 3 if word == 'adaptive' else len(word)
        outcomes = list(product((0, 1), repeat=length))
        for theta in WORLDS:
            target = []
            for obs in outcomes:
                actions = (0, obs[0], obs[0]) if word == 'adaptive' else tuple(0 if a == 'L' else 1 for a in word)
                value = Fraction(1)
                for a, o in zip(actions, obs):
                    value *= 1-target_eps[a] if o == theta[a] else target_eps[a]
                target.append(value)
            for canonical in vertices:
                distribution = [canonical[2*(u ^ theta[0])+(v ^ theta[1])] for u, v in WORLDS]
                cost = w[0]*abs(canonical[2]+canonical[3]-eps[0])+w[1]*abs(canonical[1]+canonical[3]-eps[1])
                decoded = [sum(distribution[i]*decoder[i][j] for i in range(4)) for j in range(len(target))]
                tv = sum(abs(x-y) for x, y in zip(decoded, target))/2
                assert tv <= b+k*cost
                count += 1
    return data['certificates'], dict(certificate_count=len(data['certificates']),
                                     independent_exact_vertex_checks=count,
                                     certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                                     scope='Exact decoder-bound feasibility; no minimax or LP-optimality claim.')


def apply_transfer_certificates(noise, deficits, certificates, checks):
    results = {}
    for source, coordinates in (('singles', ('L', 'R')), ('majority3', ('LLL', 'RRR'))):
        candidates = {}
        for cert in certificates:
            if cert['diagnostic_source'] != source or tuple(float(Fraction(e)) for e in cert['eps']) != noise:
                continue
            name = 'adaptive_L' if cert['word'] == 'adaptive' else cert['word']
            weights = [float(Fraction(w)) for w in cert['weights']]
            diagnostic_loss = sum(w*deficits[j] for w, j in zip(weights, coordinates))
            value = float(Fraction(cert['intercept']))+float(Fraction(cert['slope']))*diagnostic_loss
            candidates[name] = min(candidates.get(name, 1.), value)
        for name, bound in candidates.items():
            checks.at_most('transfer_'+source+'_bound', deficits[name], bound)
        results[source] = candidates
    return results


def audit_production(path, checks):
    report = json.loads(path.read_text())
    base = path.parent
    if report.get("status") not in ("passed", "complete", "passed_requested_stage", "passed_development_smoke"):
        raise AssertionError(("production not complete", report.get("status")))
    transfer_path = HERE/"theory/certificates.json"
    transfer_certificates, transfer_check = independent_transfer_certificates(transfer_path) if transfer_path.exists() else ([], {})
    targets_by_noise = {}
    checked_artifacts = set()
    hash_matches = {}
    for key, filename in (("source_sha256", "compute.py"), ("protocol_sha256", "PROTOCOL.md")):
        hash_matches[filename] = hashlib.sha256((HERE/filename).read_bytes()).hexdigest() == report.get(key)
        if report["status"] != "passed_development_smoke" and not hash_matches[filename]:
            raise AssertionError(("source hash changed", filename))
    certificate_paths = set()
    result_rows = []
    optima = {}
    for row in report["optima"]:
        optima[(row["H"], tuple(row["noise"]), row["objective"], row.get("planning_q"))] = row
    for index, row in enumerate(report["optima"]+report["rows"]):
        noise = tuple(row["noise"])
        q = row.get("planning_q")
        if noise not in targets_by_noise:
            targets_by_noise[noise] = {name: target_kernel(name, noise) for name in TARGETS}
        targets = targets_by_noise[noise]
        if (noise, row["H"]) not in checked_artifacts:
            saved_target_and_history_artifacts(base, noise, row["H"], targets, checks)
            checked_artifacts.add((noise, row["H"]))
        with np.load(base/row["policy_path"], allow_pickle=False) as z:
            action_rows = z["action_rows"].copy()
            E, weights = literal_record(row["H"], noise, action_rows, checks)
            checks.close("saved_source_kernel", E, z["source_kernel"])
            if "realization_weights" in z:
                checks.close("saved_realization_weights", weights, z["realization_weights"])
        deficits = {name: decoder_deficiency(E, target, checks) for name, target in targets.items()}
        if "deficiency_witness_path" in row:
            saved_deficiency_witness(base/row["deficiency_witness_path"], E, targets, deficits, checks)
        for name, value in row.get("target_deficiencies", {}).items():
            checks.close("saved_target_deficiency", deficits[name], value)
        purposes = {name: purpose_value(E, name) for name in ("U", "V", "world", "parity", "U_asymmetric")}
        for name, value in row.get("purpose_values", {}).items():
            checks.close("saved_purpose_value", purpose_value(E, name), value)
        for name, value in row.get("purpose_benchmarks", {}).items():
            checks.close("independent_purpose_Bellman", purpose_optimum(row["H"], noise, name), value)
        actual = objective_cost(row["objective"], E, noise, q, deficits)
        if "actual_cost" in row:
            checks.close("saved_actual_cost", actual, row["actual_cost"])
        optimum = optima[(row["H"], noise, row["objective"], q)]
        opt = optimum["optimum_cost"]
        null = np.ones((4, 1))
        null_deficits = {name: decoder_deficiency(null, target, checks) for name, target in targets.items()}
        scale = objective_cost(row["objective"], null, noise, q, null_deficits)-opt
        if row["objective"] in ("information", "quadratic"):
            checks.close("independent_Bellman_optimum", -opt, posterior_optimum(row["H"], noise, q, row["objective"]))
        if "normalization_scale" in row:
            if row.get("normalization_name") != "absolute":
                checks.close("saved_global_range", scale, row["normalization_scale"])
        if "eta" in row:
            if row.get("normalization_name") == "absolute":
                checks.close("saved_absolute_eta", row["eta"], .005)
            else:
                checks.close("saved_eta", row["eta"], row["fraction"]*scale)
            checks.at_most("near_optimal_feasibility", actual-opt, row["eta"])
            checks.at_most("optimum_lower_bound", opt, actual)
        if "actual_gap" in row:
            checks.close("saved_actual_gap", actual-opt, row["actual_gap"])
        if "purpose" in row:
            checks.close("saved_selected_purpose", purpose_value(E, row["purpose"]), row["purpose_value"])
            if "benchmark_value" in row:
                checks.close("independent_purpose_Bellman", purpose_optimum(row["H"], noise, row["purpose"]), row["benchmark_value"])
        certificate = base/row["certificate_path"]
        with np.load(certificate, allow_pickle=False) as z:
            solution = z["solution"]
            checks.close("certificate_policy_weights", solution[z["w_indices"]], weights)
            checks.close("certificate_action_weights", solution[z["x_indices"]],
                         weights[:len(action_rows), None]*action_rows)
            if "purpose" in row:
                checks.close("certificate_purpose_endpoint", z["objective"], purpose_value(E, row["purpose"]))
                if "original_objective_cost" in z:
                    original_cost = z["original_objective_cost"]@solution[:len(z["original_objective_cost"])]
                    checks.at_most("certificate_original_cost_lower", actual, original_cost)
                    checks.at_most("certificate_original_cost_threshold", original_cost, opt+row["eta"])
            else:
                checks.close("certificate_optimum_attainment", z["objective"], actual)
                checks.close("independent_optimum_attainment", actual, opt)
        if certificate not in certificate_paths:
            saved_lp_certificate(certificate, checks)
            certificate_paths.add(certificate)
        transfer_bounds = apply_transfer_certificates(noise, deficits, transfer_certificates, checks)
        result_rows.append(dict(id=row["id"], H=row["H"], noise=noise, actual_cost=actual,
                                purpose_values=purposes, target_deficiencies=deficits,
                                transfer_bounds=transfer_bounds))
        if (index+1) % 50 == 0:
            print(json.dumps(dict(audited_collectors=index+1, decoder_LPs=checks.decoder_lps,
                                  maximum_error=max(checks.errors.values(), default=0))), flush=True)
    return dict(production_status=report["status"], source_hash_matches=hash_matches,
                independent_transfer_certificate_check=transfer_check,
                production_rows=len(report["rows"]), production_optima=len(report["optima"]),
                checked_planning_certificates=len(certificate_paths), rows=result_rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--controls", action="store_true", help="Run independent finite controls only")
    parser.add_argument("--input", type=Path, default=HERE/"results/results.json")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    checks = Checks()
    body = controls(checks) if args.controls else audit_production(args.input.resolve(), checks)
    result = dict(status="passed", scope="Independent float64 controls, literal policy replay, and LP certificates; not interval proofs.",
                  check_count=checks.count, independent_decoder_LPs=checks.decoder_lps,
                  decoder_cache_hits=checks.cache_hits, max_errors=checks.errors,
                  elapsed_seconds=time.monotonic()-start,
                  audit_source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), **body)
    output = args.output or HERE/("audit_controls.json" if args.controls else "audit_results.json")
    if not output.name.startswith("audit_"):
        raise ValueError("Audit output basename must start with audit_")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ("rows",)}, indent=2))


if __name__ == "__main__":
    main()
