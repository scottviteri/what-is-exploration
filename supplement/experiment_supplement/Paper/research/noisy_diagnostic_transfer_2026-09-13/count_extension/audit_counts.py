#!/usr/bin/env python3
"""Independent exact/event-dual audit for full repeat-count transfer.

No new or predecessor planner is imported. Count/full-record equivalence and
majority garbling are checked with Fraction; event support is independently
optimized in its primal distribution and dual potential formulations. Production
certificates are checked event by event with exact arithmetic, then evaluated
on the 984 already audited parent collectors. Old policy LPs are not rerun.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import hashlib
from itertools import product
import json
from math import comb
from pathlib import Path
import time
import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
WORLDS = tuple(product((0, 1), repeat=2))
NOISES = ((Q(1, 10), Q(1, 10)), (Q(1, 4), Q(1, 4)), (Q(1, 10), Q(3, 10)))
WORDS = ('LR', 'LLL', 'RRR', 'LLR', 'LRR', 'adaptive_L')
DESIGN_LOSSES = (Q(0), Q(1, 1000), Q(1, 100), Q(1, 20), Q(1, 10))
TOL = 5e-7


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def canonical_source(name):
    return 'count3' if name in ('count3', 'counts3') else name


def canonical_word(name):
    return 'adaptive_L' if name == 'adaptive' else name


def matrix(values):
    return [[Q(x) for x in row] for row in values]


def matmul(a, b):
    return [[sum(x*y for x, y in zip(row, column)) for column in zip(*b)] for row in a]


def tv(a, b):
    return sum(abs(x-y) for x, y in zip(a, b))/2


class Checks:
    def __init__(self):
        self.errors = {}
        self.exact_events = 0
        self.event_support_lps = 0
        self.decoder_lps = 0

    def close(self, name, actual, expected, tol=TOL):
        error = float(np.max(abs(np.asarray(actual, dtype=float)-np.asarray(expected, dtype=float)), initial=0))
        self.errors[name] = max(self.errors.get(name, 0.), error)
        if not np.isfinite(error) or error > tol:
            raise AssertionError((name, error, tol))
        return error

    def upper(self, name, actual, bound, tol=TOL):
        return self.close(name, max(0., float(actual)-float(bound)), 0., tol)


def count_law(noise, bit):
    result = []
    for theta in WORLDS:
        p = 1-noise[bit] if theta[bit] else noise[bit]
        result.append([Q(comb(3, k))*p**k*(1-p)**(3-k) for k in range(4)])
    return result


def diagnostic_laws(noise, source):
    counts = [count_law(noise, bit) for bit in (0, 1)]
    if canonical_source(source) == 'count3':
        return counts
    if source != 'majority3':
        raise ValueError(source)
    majority = [[Q(int((k >= 2) == b)) for b in (0, 1)] for k in range(4)]
    return [matmul(c, majority) for c in counts]


def output_sequences(word):
    return tuple(product((0, 1), repeat=3 if canonical_word(word) == 'adaptive_L' else len(word)))


def target_law(noise, word):
    word = canonical_word(word)
    sequences = output_sequences(word)
    rows = []
    for theta in WORLDS:
        row = []
        for obs in sequences:
            actions = (0, obs[0], obs[0]) if word == 'adaptive_L' else tuple(0 if a == 'L' else 1 for a in word)
            probability = Q(1)
            for action, observation in zip(actions, obs):
                probability *= 1-noise[action] if observation == theta[action] else noise[action]
            row.append(probability)
        rows.append(row)
    return rows


def fixed_deficiency(source, target, checks):
    """Small independently assembled stochastic decoder LP for controls."""
    E, T = np.array(source, float), np.array(target, float)
    n, X = E.shape
    Y = T.shape[1]
    N = X*Y+n*Y+1
    c = np.zeros(N); c[-1] = 1.
    ae = np.zeros((X, N))
    for x in range(X):
        ae[x, x*Y:(x+1)*Y] = 1.
    au, bu = [], []
    for theta in range(n):
        for y in range(Y):
            row = np.zeros(N); row[np.arange(X)*Y+y] = E[theta]
            for sign in (1., -1.):
                constraint = sign*row
                constraint[X*Y+theta*Y+y] = -1.
                au.append(constraint);bu.append(sign*T[theta, y])
        row = np.zeros(N);row[X*Y+theta*Y:X*Y+(theta+1)*Y] = .5;row[-1] = -1.
        au.append(row);bu.append(0.)
    sol = linprog(c, A_eq=ae, b_eq=np.ones(X), A_ub=np.asarray(au), b_ub=np.asarray(bu),
                  bounds=(0, None), method='highs')
    if not sol.success:
        raise RuntimeError(sol.message)
    G = sol.x[:X*Y].reshape(X, Y)
    checks.close('control_decoder_rows', G.sum(axis=1), np.ones(X))
    checks.close('control_decoder_value', np.max(abs(E@G-T).sum(axis=1)/2), sol.fun)
    checks.close('control_decoder_duality', sol.fun,
                 np.sum(sol.eqlin.marginals)+np.asarray(bu)@sol.ineqlin.marginals)
    checks.decoder_lps += 1
    return float(sol.fun)


def primal_event_support(d, a, b, slope, checks):
    """max_p d.p - slope*(TV(pL,a)+TV(pR,b))/2 over joint laws p."""
    d, a, b, k = np.asarray(d, float), np.asarray(a, float), np.asarray(b, float), float(slope)
    nl, nr = len(a), len(b)
    n = nl*nr
    c = np.r_[-d.reshape(-1), np.full(nl+nr, k/4)]
    ae = np.zeros((1, n+nl+nr));ae[0, :n] = 1.
    au, bu = [], []
    for i in range(nl):
        row = np.zeros(len(c));row[i*nr:(i+1)*nr] = 1.
        for sign in (1., -1.):
            constraint = sign*row;constraint[n+i] = -1.
            au.append(constraint);bu.append(sign*a[i])
    for j in range(nr):
        row = np.zeros(len(c));row[np.arange(nl)*nr+j] = 1.
        for sign in (1., -1.):
            constraint = sign*row;constraint[n+nl+j] = -1.
            au.append(constraint);bu.append(sign*b[j])
    sol = linprog(c, A_eq=ae, b_eq=[1.], A_ub=np.asarray(au), b_ub=np.asarray(bu),
                  bounds=(0, None), method='highs')
    if not sol.success:
        raise RuntimeError(('event primal', sol.message))
    p = sol.x[:n].reshape(nl, nr)
    actual = float(np.sum(d*p)-k*(np.abs(p.sum(axis=1)-a).sum()+np.abs(p.sum(axis=0)-b).sum())/4)
    checks.close('event_primal_value', actual, -sol.fun)
    checks.close('event_primal_mass', p.sum(), 1.)
    checks.upper('event_primal_nonnegative', -p.min(initial=0), 0.)
    checks.event_support_lps += 1
    return actual


def dual_event_support(d, a, b, slope, checks):
    """Independent nine/five-variable marginal-potential dual."""
    d, a, b, k = np.asarray(d, float), np.asarray(a, float), np.asarray(b, float), float(slope)
    nl, nr = len(a), len(b)
    c = np.r_[1., a, b]
    au = np.zeros((nl*nr, 1+nl+nr))
    for i, j in product(range(nl), range(nr)):
        au[i*nr+j, (0, 1+i, 1+nl+j)] = -1.
    sol = linprog(c, A_ub=au, b_ub=-d.reshape(-1),
                  bounds=[(None, None)]+[(-k/4, k/4)]*(nl+nr), method='highs')
    if not sol.success:
        raise RuntimeError(('event dual', sol.message))
    checks.upper('event_dual_feasibility', np.max(au@sol.x+d.reshape(-1)), 0.)
    checks.event_support_lps += 1
    return float(sol.fun)


def controls(checks):
    equivalences = []
    for noise in NOISES:
        for bit, word in ((0, 'LLL'), (1, 'RRR')):
            full = target_law(noise, word)
            counts = count_law(noise, bit)
            observations = tuple(product((0, 1), repeat=3))
            encoder = [[Q(int(sum(obs) == k)) for k in range(4)] for obs in observations]
            decoder = [[Q(int(sum(obs) == k), comb(3, k)) for obs in observations] for k in range(4)]
            assert matmul(full, encoder) == counts
            assert matmul(counts, decoder) == full
            majority = diagnostic_laws(noise, 'majority3')[bit]
            e = noise[bit]; e3 = 3*e*e-2*e**3
            assert majority == [[1-e3 if theta[bit] == value else e3 for value in (0, 1)] for theta in WORLDS]
            loss = fixed_deficiency(majority, counts, checks)
            exact_loss = 3*e*e*(1-e)**2*(1-2*e)
            checks.close('majority_count_exact_value', loss, exact_loss)
            a, d = 1-e, e3
            extreme = a**3+e**3
            middle0, middle1 = 3*a*a*e, 3*a*e*e
            r = [extreme, ((1-d)*middle0-d*middle1)/(1-2*d),
                 ((1-d)*middle1-d*middle0)/(1-2*d), Q(0)]
            exact_decoder = [r, r[::-1]]
            assert all(sum(row) == 1 and min(row) >= 0 for row in exact_decoder)
            simulated = matmul(majority, exact_decoder)
            assert max(tv(x, y) for x, y in zip(simulated, counts)) == exact_loss
            # Prior(bit=1)=d: count reports 1 only on count=3; majority
            # optimally always reports 0 (its report=1 posterior is tied).
            assert d*a**3-(1-d)*e**3 == exact_loss
            decision_count = sum(max((1-d)*counts[0][k], d*counts[3][k]) for k in range(4))
            decision_majority = sum(max((1-d)*majority[0][k], d*majority[3][k]) for k in range(2))
            assert decision_count-decision_majority == exact_loss
            assert decision_majority == 1-d
            equivalences.append(dict(noise=list(map(str, noise)), bit=bit,
                                     count_to_full_decoder=[[str(v) for v in row] for row in decoder],
                                     exact_count_full_equivalence=True, exact_majority_garbling=True,
                                     majority_to_count_deficiency=loss,
                                     exact_majority_to_count_deficiency=str(exact_loss),
                                     exact_decoder=[[str(x) for x in row] for row in exact_decoder],
                                     exact_matching_bayes_advantage=str(decision_count-decision_majority)))
    rng = np.random.default_rng(13092026)
    support_cases = []
    for noise, source in product(NOISES, ('majority3', 'count3')):
        left, right = diagnostic_laws(noise, source)
        for k in (Q(0), Q(1, 10), Q(1), Q(4)):
            # A randomized but fixed bounded event array, with exact rational entries.
            d = rng.integers(0, 21, size=(len(left[0]), len(right[0])))/20
            for theta in (0, 3):
                primal = primal_event_support(d, left[theta], right[theta], k, checks)
                dual = dual_event_support(d, left[theta], right[theta], k, checks)
                checks.close('event_primal_dual', primal, dual)
                support_cases.append(dict(noise=list(map(str, noise)), source=source, world=theta,
                                          slope=str(k), primal=primal, dual=dual))
    return dict(count_equivalence_controls=equivalences, event_support_controls=support_cases)


def verify_certificate(cert, checks, numerical_events=False):
    noise = tuple(map(Q, cert['eps']))
    source = canonical_source(cert['diagnostic_source'])
    word = canonical_word(cert['word'])
    left, right = diagnostic_laws(noise, source)
    assert tuple(map(Q, cert['weights'])) == (Q(1, 2), Q(1, 2))
    assert tuple(tuple(x) for x in cert['input_pairs']) == tuple(product(range(len(left[0])), range(len(right[0]))))
    target = target_law(noise, word)
    literal_sequences = output_sequences(word)
    compression_checks = None
    if 'target_compression' in cert or 'groups' in cert or 'target_groups' in cert:
        compression = cert.get('target_compression', cert)
        groups = compression.get('groups', cert.get('target_groups'))
        assert sorted(index for group in groups for index in group) == list(range(len(target[0])))
        assert all(len(group) > 0 for group in groups)
        assert matrix(cert['full_target_rows']) == target
        assert tuple(tuple(x) for x in cert['full_output_sequences']) == literal_sequences
        compressed = [[sum(row[index] for index in group) for group in groups] for row in target]
        # Independently reconstruct deterministic encoding C and disjoint uniform
        # lift U; U C = identity and full T = compressed T U.
        C = [[Q(int(index in group)) for group in groups] for index in range(len(target[0]))]
        U = [[Q(int(index in group), len(group)) for index in range(len(target[0]))] for group in groups]
        identity = [[Q(int(i == j)) for j in range(len(groups))] for i in range(len(groups))]
        if 'uniform_lift' in compression:
            assert matrix(compression['uniform_lift']) == U
        if 'full_to_compressed' in compression:
            assert compression['full_to_compressed'] == [next(i for i, group in enumerate(groups) if column in group) for column in range(len(target[0]))]
        if 'group_labels' in compression:
            assert cert['output_sequences'] == compression['group_labels']
        assert matmul(U, C) == identity and matmul(compressed, U) == target
        assert matmul(target, C) == compressed
        # Disjoint row support and unit mass give l1/TV isometry for every
        # signed vector, so all compressed events suffice for full-target TV.
        assert all(sum(row) == 1 and min(row) >= 0 for row in U)
        assert all(sum(U[i][column] != 0 for i in range(len(groups))) == 1 for column in range(len(target[0])))
        if 'compressed_target_rows' in cert:
            assert matrix(cert['compressed_target_rows']) == compressed
        compression_checks = dict(full_columns=len(target[0]), compressed_columns=len(groups),
                                  exact_partition=True, exact_mutual_garblings=True, exact_TV_isometry=True)
        target = compressed
    else:
        assert tuple(tuple(x) for x in cert['output_sequences']) == literal_sequences
    assert matrix(cert['diagnostic_left']) == left
    assert matrix(cert['diagnostic_right']) == right
    assert matrix(cert['target_rows']) == target
    if 'worlds' in cert:
        assert tuple(tuple(w) for w in cert['worlds']) == WORLDS
    D = matrix(cert['decoder'])
    if 'full_decoder' in cert:
        assert matrix(cert['full_decoder']) == matmul(D, U)
    nl, nr, Y = len(left[0]), len(right[0]), len(target[0])
    assert len(D) == nl*nr and all(len(row) == Y and sum(row) == 1 and min(row) >= 0 for row in D)
    intercept, slope = Q(cert['intercept']), Q(cert['slope'])
    assert intercept >= 0 and slope >= 0
    events = cert['events']
    covered = set()
    numerical = []
    for event in events:
        theta = event['world']
        if isinstance(theta, list):
            theta = WORLDS.index(tuple(theta))
        mask = int(event['mask'])
        assert 0 <= theta < 4 and 0 <= mask < 2**Y
        assert (theta, mask) not in covered
        covered.add((theta, mask))
        u, v, t = list(map(Q, event['u'])), list(map(Q, event['v'])), Q(event['t'])
        assert len(u) == nl and len(v) == nr
        assert all(abs(x) <= slope/4 for x in u+v)
        selected = [y for y in range(Y) if mask & (1 << y)]
        values = [sum(row[y] for y in selected) for row in D]
        for i, j in product(range(nl), range(nr)):
            assert t+u[i]+v[j] >= values[i*nr+j]
        target_event = sum(target[theta][y] for y in selected)
        support_upper = t+sum(a*x for a, x in zip(left[theta], u))+sum(b*x for b, x in zip(right[theta], v))
        assert support_upper-target_event <= intercept
        checks.exact_events += 1
        if numerical_events and theta == 0 and mask in (1, (2**Y-1)//3, 2**Y-2):
            d = np.array(values, dtype=float).reshape(nl, nr)
            primal = primal_event_support(d, left[theta], right[theta], slope, checks)
            dual = dual_event_support(d, left[theta], right[theta], slope, checks)
            checks.close('certificate_event_primal_dual', primal, dual)
            checks.upper('certificate_event_bound', primal, float(support_upper))
            numerical.append(dict(mask=mask, primal=primal, dual=dual, certified_upper=str(support_upper)))
    assert covered == set(product(range(4), range(2**Y)))
    if source == 'majority3':
        # Every majority certificate lifts exactly to the full-count signatures.
        lc, rc = diagnostic_laws(noise, 'count3')
        for theta in range(4):
            for bit, count, majority in ((0, lc, left), (1, rc, right)):
                assert [sum(count[theta][i] for i in range(4) if (i >= 2) == b) for b in (0, 1)] == majority[theta]
        for event in events:
            u, v = list(map(Q, event['u'])), list(map(Q, event['v']))
            ul, vl = [u[int(i >= 2)] for i in range(4)], [v[int(i >= 2)] for i in range(4)]
            theta = event['world']
            if isinstance(theta, list): theta = WORLDS.index(tuple(theta))
            assert sum(x*y for x, y in zip(lc[theta], ul)) == sum(x*y for x, y in zip(left[theta], u))
            assert sum(x*y for x, y in zip(rc[theta], vl)) == sum(x*y for x, y in zip(right[theta], v))
    return dict(noise=list(map(str, noise)), source=source, word=word,
                at_loss=cert['at_loss'], compression_checks=compression_checks, exact_event_checks=len(events), numerical_events=numerical,
                intercept=str(intercept), slope=str(slope), bound=str(intercept+slope*Q(cert['at_loss'])))


def apply_to_parent_collectors(certificates, checks):
    rows, inputs = [], []
    for name in ('audit_h3.json', 'audit_h4.json'):
        path = PARENT/name
        data = json.loads(path.read_text())
        assert data['status'] == 'passed'
        inputs.append(dict(path='../'+name, sha256=digest(path)))
        rows += data['rows']
    assert len(rows) == 984 and len({r['id'] for r in rows}) == 984
    output = []
    for row in rows:
        noise = tuple(Q(str(x)) for x in row['noise'])
        deficits = row['target_deficiencies']
        loss = (deficits['LLL']+deficits['RRR'])/2
        bounds = {}
        for source in ('majority3', 'count3'):
            bounds[source] = {}
            for word in WORDS:
                applicable = [c for c in certificates if tuple(map(Q, c['eps'])) == noise
                              and canonical_source(c['diagnostic_source']) == source
                              and canonical_word(c['word']) == word]
                if not applicable:
                    continue
                value = min(float(Q(c['intercept']))+float(Q(c['slope']))*loss for c in applicable)
                bounds[source][word] = min(1., value)
                checks.upper('collector_'+source+'_transfer', deficits[word], bounds[source][word])
        if all(len(bounds[s]) == len(WORDS) for s in bounds):
            lifted = {word: min(bounds['count3'][word], bounds['majority3'][word]) for word in WORDS}
        else:
            lifted = {}
        output.append(dict(id=row['id'], mean_repeat_deficiency=loss,
                           majority_bounds=bounds['majority3'], raw_count_bounds=bounds['count3'],
                           count_with_lifted_majority_bounds=lifted))
    return dict(parent_collector_count=len(rows), parent_inputs=inputs, rows=output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--controls', action='store_true')
    parser.add_argument('--smoke', action='store_true', help='Audit available smoke cases without requiring the complete frozen grid.')
    parser.add_argument('--input', type=Path, default=HERE/'results.json')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    start = time.monotonic();checks = Checks()
    if args.controls:
        body = controls(checks)
    else:
        index = json.loads(args.input.read_text())
        entries = index.get('certificates', index.get('rows', []))
        assert entries
        assert index['protocol_sha256'] == digest(HERE/'PROTOCOL.md')
        assert index['source_sha256'] == digest(HERE/'compute_counts.py')
        assert not index['failures']
        certificates, details, certificate_inputs = [], [], []
        for position, entry in enumerate(entries):
            path = HERE/entry['certificate_path']
            cert = json.loads(path.read_text())
            assert cert['protocol_sha256'] == index['protocol_sha256']
            assert cert['source_sha256'] == index['source_sha256']
            for key in ('eps', 'diagnostic_source', 'word', 'at_loss', 'intercept', 'slope', 'bound'):
                assert entry[key] == cert[key], (path, key)
            assert Q(cert['bound']) == Q(cert['intercept'])+Q(cert['slope'])*Q(cert['at_loss'])
            certificate_inputs.append(dict(path=entry['certificate_path'], sha256=digest(path)))
            details.append(verify_certificate(cert, checks, numerical_events=position < 4 or args.smoke))
            certificates.append(cert)
        expected = set(product(NOISES, ('majority3', 'count3'), WORDS, DESIGN_LOSSES))
        actual = {(tuple(map(Q, c['eps'])), canonical_source(c['diagnostic_source']),
                   canonical_word(c['word']), Q(c['at_loss'])) for c in certificates}
        assert actual <= expected and len(actual) == len(certificates)
        if not args.smoke:
            assert actual == expected and len(certificates) == len(expected)
        comparisons = []
        for noise, word, loss in product(NOISES, WORDS, DESIGN_LOSSES):
            values = {}
            for source in ('majority3', 'count3'):
                c = next((c for c in certificates if tuple(map(Q, c['eps'])) == noise
                         and canonical_word(c['word']) == word and Q(c['at_loss']) == loss
                         and canonical_source(c['diagnostic_source']) == source), None)
                if c is None:
                    break
                values[source] = Q(c['intercept'])+Q(c['slope'])*loss
            if len(values) < 2:
                continue
            comparisons.append(dict(noise=list(map(str, noise)), word=word, at_loss=str(loss),
                                    majority_bound=str(values['majority3']), count_bound=str(values['count3']),
                                    count_minus_majority=float(values['count3']-values['majority3'])))
        violations = [r for r in comparisons if r['count_minus_majority'] > 2e-7]
        assert not violations, ('Investigate count search monotonicity violations', violations)
        body = dict(index_sha256=digest(args.input), certificate_inputs=certificate_inputs, certificate_count=len(certificates),
                    details=details, matched_design_comparisons=comparisons,
                    count_search_monotonicity_violations=violations,
                    **({} if args.smoke else apply_to_parent_collectors(certificates, checks)))
    result = dict(status='passed', scope='Exact certificate feasibility and numerical independent controls, not certificate-search optimality or fresh policy optimization.',
                  audit_source_sha256=digest(__file__), protocol_sha256=digest(HERE/'PROTOCOL.md'),
                  exact_event_checks=checks.exact_events, event_support_LPs=checks.event_support_lps,
                  control_decoder_LPs=checks.decoder_lps, max_errors=checks.errors,
                  elapsed_seconds=time.monotonic()-start, **body)
    output = args.output or HERE/('audit_controls.json' if args.controls else 'audit_results.json')
    assert output.name.startswith('audit_')
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('rows', 'details', 'matched_design_comparisons', 'event_support_controls', 'count_equivalence_controls')},indent=2))


if __name__ == '__main__':
    main()
