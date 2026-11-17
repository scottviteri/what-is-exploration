"""Exact LP / closed-form scalars on finite experiments (stochastic matrices P[c, y] = P_c(y)).

Shared by Exps 22-23.  All solves are dense scipy/HiGHS; sizes are tiny.
"""
import itertools

import numpy as np
from scipy.optimize import linprog


def minimax_id_error(P):
    """d_FR(E) = delta(E, K_full): inf over randomized decoders q(c|y) of max_c P_c(D != c)."""
    m, n = P.shape
    nv = m * n + 1
    c_obj = np.zeros(nv); c_obj[-1] = 1.0
    A_ub = np.zeros((m, nv)); b_ub = np.zeros(m)
    for c in range(m):
        A_ub[c, c * n:(c + 1) * n] = -P[c]
        A_ub[c, -1] = -1.0
        b_ub[c] = -1.0
    A_eq = np.zeros((n, nv)); b_eq = np.ones(n)
    for y in range(n):
        A_eq[y, [c * n + y for c in range(m)]] = 1.0
    res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=[(0, 1)] * (m * n) + [(0, 1)], method="highs")
    assert res.status == 0, res.message
    return float(res.x[-1])


def deficiency(P, Q, time_limit=5.0, methods=("highs", "highs-ipm", "highs-ds"), presolve=True):
    """delta(E, F) = inf over kernels G(y'|y) of max_c TV(G P_c, Q_c)."""
    m, n = P.shape; _, n2 = Q.shape
    nG = n * n2; nS = m * n2; nv = nG + nS + 1
    c_obj = np.zeros(nv); c_obj[-1] = 1.0
    rows = []; rhs = []
    for c in range(m):
        for y2 in range(n2):
            row = np.zeros(nv)
            for y in range(n):
                row[y * n2 + y2] = P[c, y]
            row[nG + c * n2 + y2] = -1.0
            rows.append(row.copy()); rhs.append(Q[c, y2])
            row2 = -row.copy(); row2[nG + c * n2 + y2] = -1.0
            rows.append(row2); rhs.append(-Q[c, y2])
        row = np.zeros(nv); row[nG + c * n2:nG + (c + 1) * n2] = 0.5; row[-1] = -1.0
        rows.append(row); rhs.append(0.0)
    A_eq = np.zeros((n, nv)); b_eq = np.ones(n)
    for y in range(n):
        A_eq[y, y * n2:(y + 1) * n2] = 1.0
    A_ub = np.array(rows); b_ub = np.array(rhs)
    bounds = [(0, 1)] * nG + [(0, None)] * nS + [(0, 1)]
    res = None
    for method in methods:
        res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method=method,
                      options={"time_limit": time_limit, "presolve": presolve})
        if res.status == 0:
            break
    assert res.status == 0, res.message
    return float(res.x[-1])


def deficiency_with_dual(P, Q, time_limit=5.0, methods=("highs", "highs-ds", "highs-ipm"), presolve=True):
    """Sibling of `deficiency` (same LP, same value) that also returns the optimal decoder and the LP
    dual read as a DECISION PROBLEM.  Added for Exp 46; `deficiency`'s signature is unchanged.

    Primal (as in `deficiency`):  delta(E, F) = min_G max_c TV(G P_c, Q_c),  TV = (1/2) L1.
    Dual (Le Cam / Torgersen; the finite-minimum inequality is App. D's dual-certificate lemma):

        delta(E, F) = max_{lam, u} [ sum_y min_{y'} sum_c u_{c,y'} P_c(y) - sum_{c,y'} u_{c,y'} Q_c(y') ]
                      s.t. lam_c >= 0, sum_c lam_c <= 1, |u_{c,y'}| <= lam_c / 2.

    Substituting u_{c,y'} = lam_c (ell_{c,y'} - 1/2) with a loss ell in [0,1] (utility w = 1 - ell) and
    using that every row of P and Q sums to one, the bracket equals

        R^Bayes_ell(E) - R^id_ell(F)  =  V^id_w(F) - V_w(E),

    where V_w(E) = sum_y max_{y'} sum_c lam_c P_c(y) w(c, y') is the Bayes value of E in the finite
    decision problem "guess the outcome y' of F" (prior lam, utility w(c, y') in [0,1], decision set =
    outcomes of F) and V^id_w(F) = sum_{c,y'} lam_c Q_c(y') w(c, y') is the value F obtains by reporting
    its own outcome.  By strong duality the optimum equals delta(E, F); by the readiness proposition
    V_w(F) - V_w(E) <= delta(E, F) for every (lam, w), so at the optimum V_w(F) = V^id_w(F) and the dual
    task attains the bound exactly: the deficiency IS the value lost on that task.

    The multipliers returned by HiGHS are projected onto the dual-feasible set (lam >= 0 normalised to
    sum 1; |u| clipped to lam/2) before anything is evaluated, so `dual_value` is a rigorous lower
    bound on delta(E, F) (weak duality) whatever the solver did; the caller checks it against the primal.

    Returns (value, info) with value = primal optimum (as `deficiency`) and info = dict(
        G          (n x n2) optimal decoder kernel,
        lam        (m,) prior over worlds,
        u          (m x n2) projected dual multipliers,
        loss       (m x n2) ell in [0,1],
        utility    (m x n2) w = 1 - ell in [0,1],
        dual_value the bracket above evaluated at (lam, u),
        V_E        Bayes value of E under (lam, w),
        V_F        Bayes value of F under (lam, w),
        V_F_id     value of F under the identity rule,
        method     the linprog method that solved).
    """
    P = np.asarray(P, float); Q = np.asarray(Q, float)
    m, n = P.shape; _, n2 = Q.shape
    nG = n * n2; nS = m * n2; nv = nG + nS + 1
    c_obj = np.zeros(nv); c_obj[-1] = 1.0
    rows = []; rhs = []
    for c in range(m):
        for y2 in range(n2):
            row = np.zeros(nv)
            for y in range(n):
                row[y * n2 + y2] = P[c, y]
            row[nG + c * n2 + y2] = -1.0
            rows.append(row.copy()); rhs.append(Q[c, y2])              # (+): G P_c(y') - s <= Q_c(y')
            row2 = -row.copy(); row2[nG + c * n2 + y2] = -1.0
            rows.append(row2); rhs.append(-Q[c, y2])                   # (-): -G P_c(y') - s <= -Q_c(y')
        row = np.zeros(nv); row[nG + c * n2:nG + (c + 1) * n2] = 0.5; row[-1] = -1.0
        rows.append(row); rhs.append(0.0)                              # (lam): (1/2) sum s_c - t <= 0
    A_eq = np.zeros((n, nv)); b_eq = np.ones(n)
    for y in range(n):
        A_eq[y, y * n2:(y + 1) * n2] = 1.0
    A_ub = np.array(rows); b_ub = np.array(rhs)
    bounds = [(0, 1)] * nG + [(0, None)] * nS + [(0, 1)]
    res = None; used = None
    for method in methods:
        res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method=method,
                      options={"time_limit": time_limit, "presolve": presolve})
        if res.status == 0 and res.ineqlin is not None and res.ineqlin.marginals is not None:
            used = method
            break
    assert res is not None and res.status == 0, res.message
    value = float(res.x[-1])
    G = res.x[:nG].reshape(n, n2)
    # marginals = d(objective)/d(b_ub) <= 0 for a minimisation; the Lagrange multipliers are their negatives
    marg = -np.asarray(res.ineqlin.marginals, float).reshape(m, 2 * n2 + 1)
    alpha = np.clip(marg[:, 0:2 * n2:2], 0.0, None)
    beta = np.clip(marg[:, 1:2 * n2:2], 0.0, None)
    lam = np.clip(marg[:, 2 * n2], 0.0, None)
    if lam.sum() <= 0:                                                  # delta = 0 and a trivial dual
        lam = np.full(m, 1.0 / m)
    lam = lam / lam.sum()                                               # homogeneous objective: scale up
    u = np.clip(alpha - beta, -0.5 * lam[:, None], 0.5 * lam[:, None])
    dual_value = float((P.T @ u).min(1).sum() - (u * Q).sum())
    with np.errstate(divide="ignore", invalid="ignore"):
        loss = np.where(lam[:, None] > 0, 0.5 + u / np.where(lam[:, None] > 0, lam[:, None], 1.0), 0.5)
    loss = np.clip(loss, 0.0, 1.0)
    utility = 1.0 - loss
    W = lam[:, None] * utility                                          # prior-weighted utility (m x n2)
    V_E = float((P.T @ W).max(1).sum())
    V_F = float((Q.T @ W).max(1).sum())
    V_F_id = float((Q * W).sum())
    return value, dict(G=G, lam=lam, u=u, loss=loss, utility=utility, dual_value=dual_value,
                       V_E=V_E, V_F=V_F, V_F_id=V_F_id, method=used, alpha=alpha, beta=beta)


# ----------------------------------------------------------------------------- certified deficiency
def _certify_deficiency(P, Q, G, mu=None, lam=None):
    """Rigorous two-sided bounds on delta(E, F) evaluated on the EXACT matrices P, Q.

    upper: any kernel G is feasible, so max_c TV(G P_c, Q_c) >= delta.  G is clipped to >= 0 and its
           rows renormalised so the bound is for an honest kernel.
    lower: weak duality.  For 0 <= mu_{c,y'} <= lam_c, sum_c lam_c = 1 and any kernel G,
           max_c TV(G P_c, Q_c) >= sum_c lam_c TV(G P_c, Q_c)
                                >= sum_{c,y'} mu_{c,y'} ((G P_c)(y') - Q_c(y'))        [(a)_+ >= theta a, theta in [0,1]]
                                 = sum_y sum_{y'} G(y,y') sum_c mu_{c,y'} P_c(y) - sum mu Q
                                >= sum_y min_{y'} sum_c mu_{c,y'} P_c(y) - sum mu Q,
           so the last expression (Le Cam's randomisation criterion / Torgersen's dual) lower-bounds
           delta for EVERY feasible (mu, lam); the LP duals are projected onto that feasible set.
    Returns (lower, upper, G_normalised)."""
    G = np.clip(np.asarray(G, float), 0.0, None)
    rs = G.sum(1, keepdims=True)
    G = np.where(rs > 0, G / np.where(rs > 0, rs, 1.0), 1.0 / G.shape[1])
    upper = float((0.5 * np.abs(P @ G - Q).sum(1)).max())
    if mu is None or lam is None:
        return 0.0, upper, G
    lam = np.clip(np.asarray(lam, float), 0.0, None)
    if lam.sum() <= 0:
        return 0.0, upper, G
    lam = lam / lam.sum()
    mu = np.clip(np.asarray(mu, float), 0.0, lam[:, None])
    lower = float((P.T @ mu).min(1).sum() - (mu * Q).sum())
    return max(lower, 0.0), upper, G


def _tv_lp_ipm(A, R, b_eq, lbD, ubD, time_limit=120.0, presolve=True, small_matrix_value=1e-12, iteration_limit=400):
    """HiGHS interior point (no crossover) for

        min tau  s.t.  sum_y D(y,y') A_c(y) - s_{c,y'} <= R_c(y'),   sum_{y'} s_{c,y'} <= tau,
                       sum_{y'} D(y,y') = b_eq[y],   lbD <= D <= ubD,   s >= 0

    (one-sided TV formulation: TV = sum of positive parts because both sides have equal mass).
    Returns (D, mu, lam, status) with mu, lam = -(row duals) of the two inequality blocks, or None.
    The vendored HiGHS binding is used directly so that an IPM point HiGHS labels "Unknown"
    (imprecise, but perfectly usable once certified) is not discarded; falls back to linprog."""
    from scipy.sparse import coo_matrix, vstack
    m, n = A.shape; n2 = R.shape[1]
    nG = n * n2; nS = m * n2; nv = nG + nS + 1
    c = np.zeros(nv); c[-1] = 1.0
    rows = []; cols = []; vals = []; rhs = []
    r = 0
    for cc in range(m):
        ys = np.nonzero(A[cc])[0]
        for y2 in range(n2):
            rows.append(np.full(len(ys) + 1, r)); cols.append(np.append(ys * n2 + y2, nG + cc * n2 + y2))
            vals.append(np.append(A[cc, ys], -1.0)); rhs.append(R[cc, y2]); r += 1
        rows.append(np.full(n2 + 1, r)); cols.append(np.append(np.arange(nG + cc * n2, nG + (cc + 1) * n2), nv - 1))
        vals.append(np.append(np.ones(n2), -1.0)); rhs.append(0.0); r += 1
    A_ub = coo_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))), shape=(r, nv)).tocsr()
    A_eq = coo_matrix((np.ones(nG), (np.repeat(np.arange(n), n2), np.arange(nG))), shape=(n, nv)).tocsr()
    b_ub = np.array(rhs)
    lb = np.concatenate([np.asarray(lbD, float).ravel(), np.zeros(nS + 1)])
    ub = np.concatenate([np.asarray(ubD, float).ravel(), np.full(nS + 1, np.inf)])
    opts = dict(solver="ipm", run_crossover="off", presolve="on" if presolve else "off", time_limit=float(time_limit),
                ipm_optimality_tolerance=1e-12, small_matrix_value=small_matrix_value, output_flag=False, log_to_console=False,
                ipm_iteration_limit=int(iteration_limit))
    try:
        from scipy.optimize._highspy import _core as _h
    except Exception:                                   # older/newer scipy: go through linprog
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=np.c_[lb, ub], method="highs-ipm",
                          options=dict(time_limit=time_limit, presolve=presolve, run_crossover="off", maxiter=int(iteration_limit),
                                       ipm_optimality_tolerance=1e-12, small_matrix_value=small_matrix_value))
        if res.status != 0:
            return None
        x = res.x; rd = res.ineqlin.marginals; status = "Optimal"
    else:
        M = vstack([A_ub, A_eq]).tocsc()
        lp = _h.HighsLp()
        lp.num_col_ = nv; lp.num_row_ = M.shape[0]
        lp.a_matrix_.num_col_ = nv; lp.a_matrix_.num_row_ = M.shape[0]
        lp.a_matrix_.format_ = _h.MatrixFormat.kColwise
        lp.col_cost_ = c; lp.col_lower_ = lb; lp.col_upper_ = ub
        lp.row_lower_ = np.concatenate([np.full(r, -np.inf), np.asarray(b_eq, float)])
        lp.row_upper_ = np.concatenate([b_ub, np.asarray(b_eq, float)])
        lp.a_matrix_.start_ = M.indptr.astype(np.int32); lp.a_matrix_.index_ = M.indices.astype(np.int32)
        lp.a_matrix_.value_ = M.data
        h = _h._Highs()
        for k, v in opts.items():
            h.setOptionValue(k, v)
        h.passModel(lp); h.run()
        status = h.modelStatusToString(h.getModelStatus())
        sol = h.getSolution()
        if not sol.value_valid:
            return None
        x = np.asarray(sol.col_value); rd = np.asarray(sol.row_dual)[:r] if sol.dual_valid else np.zeros(r)
    D = x[:nG].reshape(n, n2)
    marg = -rd.reshape(m, n2 + 1)
    return D, marg[:, :n2], marg[:, n2], status


def deficiency_certified(P, Q, tol=1e-10, floor=1e-12, max_rounds=8, time_limit=120.0, refine_time_limit=30.0):
    """delta(E, F) with a rigorous certificate, robust to ill-conditioned P (entries spanning 1e-45..1).

    Returns (value, info): value = certified upper bound `upper` (achieved by an explicit kernel), and
    info = dict(lower, upper, gap, rounds, statuses).  The exact LP optimum lies in [lower, upper];
    the loop stops once upper - lower <= tol.

    Method.  (1) Entries of P below `floor` are zeroed for the solver only (HiGHS itself silently drops
    matrix entries below 1e-9 by default; here small_matrix_value = 1e-12 and nothing is hidden); every
    bound is evaluated on the EXACT P, so flooring costs nothing in rigour.  (2) HiGHS IPM without
    crossover (crossover / dual simplex stall for hours on these degenerate LPs).  (3) Certificate of
    the IPM point (see _certify_deficiency).  (4) Iterative refinement (Gleixner-style) in FLOW
    variables f(y,y') = w_y G(y,y'), w_y = column mass: the IPM residual (~1e-8 absolute) lives in
    low-mass tail columns where fixing it needs O(1) changes of G(y,.), so the residual LP is posed for
    Delta f = eps D with eps = max residual, coefficient matrix = likelihood-ratio vectors P_c(y)/w_y,
    D >= -f/eps and |D| <= cap (cap schedule 1e6, 1e8, inf); each round gains ~1e-4..1e-8 in the
    certified gap.  The best kernel and the best dual are kept; nothing is ever trusted uncertified."""
    P = np.asarray(P, float); Q = np.asarray(Q, float)
    m, n = P.shape; n2 = Q.shape[1]
    Pf = np.where(P < floor, 0.0, P)
    statuses = []
    out = _tv_lp_ipm(Pf, Q, np.ones(n), np.zeros((n, n2)), np.ones((n, n2)), time_limit, presolve=True)
    if out is None:
        out = _tv_lp_ipm(Pf, Q, np.ones(n), np.zeros((n, n2)), np.ones((n, n2)), time_limit, presolve=False)
    if out is None:
        raise RuntimeError("deficiency_certified: HiGHS IPM returned no solution (presolve on and off)")
    D, mu, lam, st = out; statuses.append(st)
    lo, up, G = _certify_deficiency(P, Q, D, mu, lam)
    if up - lo <= tol:
        return up, dict(lower=lo, upper=up, gap=up - lo, rounds=0, statuses=statuses)
    w = Pf.sum(0); wsafe = np.where(w > 0, w, 1.0)
    LR = Pf / wsafe                                     # likelihood-ratio vectors (columns sum to 1 where w > 0)
    caps = [1e6, 1e6, 1e8, 1e8] + [np.inf] * max(0, max_rounds - 4)
    rounds = 0
    for cap in caps[:max_rounds]:
        if up - lo <= tol:
            break
        Rres = Q - P @ G
        eps = max(float(np.abs(Rres).max()), 1e-300)
        f0 = wsafe[:, None] * G
        lbD = np.maximum(-f0 / eps, -cap); ubD = np.full_like(lbD, cap)
        lbD[w == 0] = 0.0; ubD[w == 0] = 0.0            # columns invisible to the solver carry no flow
        out = _tv_lp_ipm(LR, Rres / eps, np.zeros(n), lbD, ubD, refine_time_limit, presolve=False)
        rounds += 1
        if out is None:
            statuses.append("none"); continue
        D, mu2, lam2, st = out; statuses.append(st)
        lo2, up2, G2 = _certify_deficiency(P, Q, (f0 + eps * D) / wsafe[:, None], mu2, lam2)
        lo = max(lo, lo2)
        if up2 < up:
            up, G = up2, G2
    lo = min(lo, up)
    return up, dict(lower=lo, upper=up, gap=up - lo, rounds=rounds, statuses=statuses)


def hellinger_worst_pair(P):
    m = P.shape[0]
    return min(1.0 - float(np.sqrt(P[c] * P[d]).sum())
               for c, d in itertools.combinations(range(m), 2))


def entropy(p):
    p = np.asarray(p, dtype=float)
    p = p[p > 0]
    return float(-(p * np.log(p)).sum())


def mutual_information(P, alpha=None):
    """I_alpha(C; Y) in nats for the channel P under prior alpha (uniform by default)."""
    m = P.shape[0]
    alpha = np.full(m, 1.0 / m) if alpha is None else np.asarray(alpha, dtype=float)
    mix = alpha @ P
    return entropy(mix) - float(sum(alpha[c] * entropy(P[c]) for c in range(m)))


def partition_channel(blocks, m):
    P = np.zeros((m, len(blocks)))
    for y, B in enumerate(blocks):
        for c in B:
            P[c, y] = 1.0
    return P


def dominates(P, Q, tol=1e-7):
    """E Blackwell-dominates F  <=>  delta(E, F) = 0."""
    return deficiency(P, Q) <= tol


# ----------------------------------------------------------------------------- Exp 24 helpers
def horizon_experiment(fam, word):
    """Class-conditional laws over observation sequences of an open-loop action word, grouped by
    likelihood-ratio vector (a sufficient statistic).  Same construction as Exp 20."""
    m, A, S, _ = fam.T.shape
    O = fam.E.shape[2]
    seqs = list(itertools.product(range(O), repeat=len(word)))
    P = np.zeros((m, len(seqs)))
    for j, seq in enumerate(seqs):
        for c in range(m):
            f = fam.mu[c].copy()
            for a, o in zip(word, seq):
                f = (f @ fam.T[c, a]) * fam.E[c, :, o]
            P[c, j] = f.sum()
    keep = P.sum(0) > 1e-9                      # drop numerically negligible outcomes (HiGHS pathologies)
    P = P[:, keep]
    P = P / P.sum(1, keepdims=True)
    ratios = np.round(P / P.sum(0, keepdims=True), 9)
    uniq, inv = np.unique(ratios.T, axis=0, return_inverse=True)
    G = np.zeros((m, len(uniq)))
    np.add.at(G.T, inv.ravel(), P.T)
    return G


def bayes_risk(P, L):
    """Bayes risk of the experiment P (rows P_c) for the loss L[c, a] with class weights folded in:
    sum_y min_a sum_c P_c(y) L(c, a)."""
    return float((P.T @ L).min(axis=1).sum())


def mixture_deficiency(E, others):
    """delta_mix(E) = min over label-observed mixtures M of `others` of delta(M, E), by the dual LP

        2 delta_mix(E) = max_{L, z} [ min_F R_L(F) - sum_{c,y'} E_c(y') L(c,y') ]
                         s.t. -z_c <= L(c, y') <= z_c,  sum_c z_c <= 1,

    where R_L(F) = sum_y min_{y'} sum_c F_c(y) L(c, y') is the Bayes risk of F in the decision
    problem with actions Y_E and loss L, and E is scored by the identity rule.  Returns
    (delta_mix, L) with L the exposing loss (actions = outcomes of E).  delta_mix > 0 iff no
    label-observed mixture of `others` Blackwell-dominates E iff E is the unique optimum of a
    bounded decision problem among `others` and all their mixtures.  Sparse construction.
    """
    from scipy.sparse import coo_matrix
    m, nE = E.shape
    nL = m * nE
    sizes = [F.shape[1] for F in others]
    nM = sum(sizes)
    nv = nL + m + nM + 1
    iz = nL; im = nL + m; ir = nL + m + nM
    c_obj = np.zeros(nv)
    c_obj[ir] = -1.0
    c_obj[:nL] = E.ravel()
    rows = []; cols = []; vals = []; rhs = []
    r = 0
    for c in range(m):
        for y in range(nE):
            rows += [r, r]; cols += [c * nE + y, iz + c]; vals += [1.0, -1.0]; rhs.append(0.0); r += 1
            rows += [r, r]; cols += [c * nE + y, iz + c]; vals += [-1.0, -1.0]; rhs.append(0.0); r += 1
    for c in range(m):
        rows.append(r); cols.append(iz + c); vals.append(1.0)
    rhs.append(1.0); r += 1
    off = 0
    for F, nF in zip(others, sizes):
        for y in range(nF):
            for yp in range(nE):
                rows.append(r); cols.append(im + off + y); vals.append(1.0)
                for c in range(m):
                    if F[c, y] != 0.0:
                        rows.append(r); cols.append(c * nE + yp); vals.append(-F[c, y])
                rhs.append(0.0); r += 1
        rows.append(r); cols.append(ir); vals.append(1.0)
        for y in range(nF):
            rows.append(r); cols.append(im + off + y); vals.append(-1.0)
        rhs.append(0.0); r += 1
        off += nF
    A_ub = coo_matrix((vals, (rows, cols)), shape=(r, nv)).tocsr()
    bounds = [(None, None)] * nL + [(0, None)] * m + [(None, None)] * nM + [(None, None)]
    res = linprog(c_obj, A_ub=A_ub, b_ub=np.array(rhs), bounds=bounds, method="highs")
    assert res.status == 0, res.message
    L = res.x[:nL].reshape(m, nE)
    return float(-res.fun / 2.0), L


def mixture_deficiency_primal(E, others):
    """Cross-check: min over nu, kernels of max_c TV((+)_nu G_F F_c, E_c) as a primal LP."""
    m, nE = E.shape
    sizes = [F.shape[1] for F in others]
    nG = sum(nF * nE for nF in sizes)
    nF_ = len(others)
    nS = m * nE
    nv = nG + nF_ + nS + 1
    inu = nG; isl = nG + nF_; it = nG + nF_ + nS
    c_obj = np.zeros(nv); c_obj[it] = 1.0
    A_eq = []; b_eq = []
    off = 0
    for k, nF in enumerate(sizes):
        for y in range(nF):
            row = np.zeros(nv); row[off + y * nE: off + (y + 1) * nE] = 1.0; row[inu + k] = -1.0
            A_eq.append(row); b_eq.append(0.0)
        off += nF * nE
    row = np.zeros(nv); row[inu:inu + nF_] = 1.0; A_eq.append(row); b_eq.append(1.0)
    rows = []; rhs = []
    for c in range(m):
        for yp in range(nE):
            row = np.zeros(nv)
            off = 0
            for F, nF in zip(others, sizes):
                for y in range(nF):
                    row[off + y * nE + yp] = F[c, y]
                off += nF * nE
            row[isl + c * nE + yp] = -1.0
            rows.append(row.copy()); rhs.append(E[c, yp])
            row2 = -row.copy(); row2[isl + c * nE + yp] = -1.0
            rows.append(row2); rhs.append(-E[c, yp])
        row = np.zeros(nv); row[isl + c * nE: isl + (c + 1) * nE] = 0.5; row[it] = -1.0
        rows.append(row); rhs.append(0.0)
    bounds = [(0, None)] * nG + [(0, 1)] * nF_ + [(0, None)] * nS + [(0, 1)]
    res = linprog(c_obj, A_ub=np.array(rows), b_ub=np.array(rhs), A_eq=np.array(A_eq), b_eq=np.array(b_eq),
                  bounds=bounds, method="highs")
    assert res.status == 0, res.message
    return float(res.x[it]), res.x[inu:inu + nF_]


# ----------------------------------------------------------------------------- richer projections
def hellinger_mean_pair(P):
    """Average pairwise squared Hellinger distance (positive-weight average of a strictly convex
    pairwise f-divergence; prior-free, relabeling-invariant)."""
    m = P.shape[0]
    pairs = list(itertools.combinations(range(m), 2))
    return float(np.mean([1.0 - np.sqrt(P[c] * P[d]).sum() for c, d in pairs]))


def channel_capacity(P, iters=3000, tol=1e-12):
    """Shannon capacity sup_alpha I_alpha(C; Y) in nats, by Blahut-Arimoto."""
    m, n = P.shape
    alpha = np.full(m, 1.0 / m)
    logP = np.log(np.where(P > 0, P, 1.0))
    for _ in range(iters):
        q = alpha @ P
        logq = np.log(np.where(q > 0, q, 1.0))
        D = np.array([(P[c] * (logP[c] - logq))[P[c] > 0].sum() for c in range(m)])
        new = alpha * np.exp(D)
        new /= new.sum()
        if np.abs(new - alpha).max() < tol:
            alpha = new
            break
        alpha = new
    return mutual_information(P, alpha)


def maximal_leakage(P):
    """log sum_y max_c P(y|c) (Issa-Wagner-Kamath), in nats."""
    return float(np.log(P.max(axis=0).sum()))


def deficiency_from_ignorance(P):
    """d_bot(E) = delta(K_ignorance, E) = min over distributions Q on Y of max_c TV(Q, P_c) (Torgersen's delta_i / 2)."""
    m, n = P.shape
    nv = n + m * n + 1               # Q, slacks s(c,y), t
    c_obj = np.zeros(nv); c_obj[-1] = 1.0
    rows = []; rhs = []
    for c in range(m):
        for y in range(n):
            row = np.zeros(nv); row[y] = 1.0; row[n + c * n + y] = -1.0; rows.append(row); rhs.append(P[c, y])
            row = np.zeros(nv); row[y] = -1.0; row[n + c * n + y] = -1.0; rows.append(row); rhs.append(-P[c, y])
        row = np.zeros(nv); row[n + c * n:n + (c + 1) * n] = 0.5; row[-1] = -1.0; rows.append(row); rhs.append(0.0)
    A_eq = np.zeros((1, nv)); A_eq[0, :n] = 1.0
    res = linprog(c_obj, A_ub=np.array(rows), b_ub=np.array(rhs), A_eq=A_eq, b_eq=[1.0],
                  bounds=[(0, 1)] * n + [(0, None)] * (m * n) + [(0, 1)], method="highs")
    assert res.status == 0, res.message
    return float(res.x[-1])
