#!/usr/bin/env python3
"""Independent exact model audit for the 28-ray optimal-policy oracle.

Imports only the independently written rational witness/Bellman audit. No
planner/search module is imported. Reconstructs exact LP rows from the declared
policy and decoder semantics, checks source/target sufficiency, and checks saved
numerical smoke primal/dual certificates with an exact box-residual repair.
"""
from __future__ import annotations
from fractions import Fraction as Q
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import numpy as np
from scipy.sparse import csr_matrix

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location('independent_sharp_audit', HERE/'audit.py')
INDEPENDENT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(INDEPENDENT)
EDGES, WORLDS = INDEPENDENT.EDGES, INDEPENDENT.WORLDS


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def signed_counts(history):
    return tuple(sum(2*observation-1 for action, observation in history if action == side) for side in (0, 1))


class ExactModel:
    def __init__(self):
        bellman = INDEPENDENT.bellman_certificate()
        self.actions = {tuple(map(tuple, row['history'])): tuple(row['allowed_actions']) for row in bellman['history_rows']}
        self.levels, self.reachable = [[()]], [[()]]
        for _ in range(4):
            self.levels.append([history+(edge,) for history in self.levels[-1] for edge in EDGES])
            self.reachable.append([history+(edge,) for history in self.reachable[-1] for edge in EDGES
                                   if edge[0] in self.actions[history]])
        self.histories = self.levels[-1]
        self.likelihoods = {history: INDEPENDENT.history_likelihoods(history)
                            for level in self.levels for history in level}
        self.states = sorted({signed_counts(history) for history in self.reachable[-1]})
        assert len(self.states) == 28
        self.state_index = {state: index for index, state in enumerate(self.states)}
        self.scale = {history: max(self.likelihoods[history]) for history in self.histories}
        self.rays = []
        for state in self.states:
            history = next(h for h in self.reachable[-1] if signed_counts(h) == state)
            self.rays.append([mass/self.scale[history] for mass in self.likelihoods[history]])
        self.targets = {}
        for name in ('LR', 'LLL', 'RRR', 'adaptive_L'):
            full = INDEPENDENT.target_kernel(name)
            sequences = INDEPENDENT.observations(2 if name == 'LR' else 3)
            labels, groups = [], []
            for index, observation in enumerate(sequences):
                label = (observation if name == 'LR' else sum(observation) if name in ('LLL', 'RRR')
                         else (observation[0], sum(observation[1:])))
                if label not in labels:
                    labels.append(label);groups.append([])
                groups[labels.index(label)].append(index)
            compressed = [[sum(row[index] for index in group) for group in groups] for row in full]
            self.targets[name] = {'full': full, 'rows': compressed, 'groups': groups, 'labels': labels}
        self.eq, self.ub, self.n = [], [], 0
        self.w = {history: self.var() for level in self.reachable for history in level}
        self.x = {}
        self.add({self.w[()]: Q(1)}, Q(1), equality=True)
        for level in self.reachable[:-1]:
            for history in level:
                row = {self.w[history]: -Q(1)}
                for action in self.actions[history]:
                    variable = self.var();self.x[history, action] = variable;row[variable] = Q(1)
                    for candidate, observation in EDGES:
                        if candidate == action:
                            self.add({self.w[history+((action, observation),)]: Q(1), variable: -Q(1)}, Q(0), True)
                self.add(row, Q(0), True)
        self.z = [self.var() for _ in self.states]
        for state, index in self.state_index.items():
            row = {self.w[history]: self.scale[history] for history in self.reachable[-1]
                   if signed_counts(history) == state}
            row[self.z[index]] = -Q(1);self.add(row, Q(0), True)
        self.allocations, self.deficits = {}, {}
        for name in ('LR', 'LLL', 'RRR'):
            target = self.targets[name]['rows'];width = len(target[0])
            allocation = [[self.var() for _ in range(width)] for _ in self.states]
            self.allocations[name] = allocation
            for state in range(28):
                self.add({variable: Q(1) for variable in allocation[state]}|{self.z[state]: -Q(1)}, Q(0), True)
            if name != 'LR':
                self.deficits[name] = self.var()
            for world in range(4):
                errors = []
                for output in range(width):
                    row = {allocation[state][output]: self.rays[state][world] for state in range(28)}
                    if name == 'LR':
                        self.add(row, target[world][output], True)
                    else:
                        error = self.var();errors.append(error)
                        self.add(row|{error: -Q(1)}, target[world][output])
                        self.add({key: -value for key, value in row.items()}|{error: -Q(1)}, -target[world][output])
                if name != 'LR':
                    self.add({error: Q(1, 2) for error in errors}|{self.deficits[name]: -Q(1)}, Q(0))
        self.add({variable: Q(1) for variable in self.deficits.values()}, Q(9, 125))
        assert (self.n, len(self.eq), len(self.ub)) == (857, 514, 73)

    def var(self):
        index = self.n;self.n += 1;return index

    def add(self, row, rhs, equality=False):
        (self.eq if equality else self.ub).append((row, rhs))


def verify_metadata(model, metadata):
    assert metadata['source_sha256'] == digest(HERE/'compressed_oracle.py')
    assert metadata['search_sha256'] == digest(HERE/'search.py')
    assert metadata['parent_compute_sha256'] == digest(HERE.parent/'compute.py')
    assert Q(metadata['cost_bound']) == Q(9, 1250)
    assert Q(metadata['bellman_root_value']) == Q(234, 125)
    assert tuple(map(tuple, metadata['states'])) == tuple(model.states)
    assert [[Q(value) for value in row] for row in metadata['rays']] == model.rays
    assert tuple(tuple(map(tuple, history)) for history in metadata['terminal_histories']) == tuple(model.histories)
    assert metadata['reachable_sizes'] == list(map(len, model.reachable)) == [1, 4, 16, 68, 208]
    expected_state = [model.state_index.get(signed_counts(history), -1) for history in model.histories]
    assert metadata['history_state'] == expected_state
    assert list(map(Q, metadata['history_scale'])) == [model.scale[history] for history in model.histories]
    ray_checks = 0
    for history, state in zip(model.histories, expected_state):
        if state >= 0:
            assert [model.scale[history]*entry for entry in model.rays[state]] == model.likelihoods[history]
            ray_checks += 1
    for name, target in model.targets.items():
        saved = metadata['targets'][name]
        assert saved['groups'] == target['groups']
        assert saved['labels'] == INDEPENDENT.strings(target['labels'])
        assert [[Q(x) for x in row] for row in saved['rows']] == target['rows']
        assert [[Q(x) for x in row] for row in saved['full_rows']] == target['full']
        groups = target['groups'];width = len(target['full'][0])
        encoding = [[Q(int(output in group)) for group in groups] for output in range(width)]
        lift = [[Q(int(output in group), len(group)) for output in range(width)] for group in groups]
        assert INDEPENDENT.matmul(target['full'], encoding) == target['rows']
        assert INDEPENDENT.matmul(target['rows'], lift) == target['full']
        assert INDEPENDENT.matmul(lift, encoding) == [[Q(int(i == j)) for j in range(len(groups))] for i in range(len(groups))]
    # LR's exact garblings recover each singleton and its independently tagged lottery.
    LR = model.targets['LR']['full']
    for name in ('L', 'R', 'tagged'):
        decoder = []
        for left, right in product((0, 1), repeat=2):
            if name == 'L':row = [Q(int(output == left)) for output in (0, 1)]
            elif name == 'R':row = [Q(int(output == right)) for output in (0, 1)]
            else:row = [Q(int(output == left), 2) for output in (0, 1)]+[Q(int(output == right), 2) for output in (0, 1)]
            decoder.append(row)
        assert INDEPENDENT.matmul(LR, decoder) == INDEPENDENT.target_kernel(name)
    return {'exact_ray_checks': ray_checks, 'reachable_rays': 28, 'reachable_terminal_histories': 208,
            'target_sufficiency_checks': 4, 'LR_garbling_checks': 3}


def randomized_equivalence_controls(model):
    controls = []
    for mode in ('uniform_allowed', 'biased_allowed', 'deterministic_first_allowed'):
        weights = {(): Q(1)}
        for level in model.levels[:-1]:
            for history in level:
                allowed = model.actions[history]
                if mode == 'uniform_allowed':probabilities = {action: Q(1, len(allowed)) for action in allowed}
                elif mode == 'biased_allowed':probabilities = {action: Q(action+1, sum(a+1 for a in allowed)) for action in allowed}
                else:probabilities = {action: Q(int(action == allowed[0])) for action in allowed}
                for action, observation in EDGES:
                    weights[history+((action, observation),)] = weights[history]*probabilities.get(action, Q(0))
        source = [[weights[history]*model.likelihoods[history][world] for history in model.histories] for world in range(4)]
        assert all(sum(row) == 1 for row in source)
        z = [sum(model.scale[history]*weights[history] for history in model.histories
                 if signed_counts(history) == state) for state in model.states]
        compressed = [[ray[world]*mass for ray, mass in zip(model.rays, z)] for world in range(4)]
        inverse = []
        for state, mass in zip(model.states, z):
            candidates = [index for index, history in enumerate(model.histories) if signed_counts(history) == state]
            row = [Q(0)]*625
            if mass:
                for index in candidates:
                    history = model.histories[index];row[index] = model.scale[history]*weights[history]/mass
            else:row[candidates[0]] = Q(1)
            assert min(row) >= 0 and sum(row) == 1
            inverse.append(row)
        assert INDEPENDENT.matmul(compressed, inverse) == source
        assert all(sum(row) == 1 for row in compressed)
        controls.append({'policy': mode, 'active_states': sum(mass != 0 for mass in z),
                         'exact_world_independent_inverse_checked': True})
    return controls


def check_saved_model(model, data):
    for prefix, expected in (('A_eq', model.eq), ('A_ub', model.ub)):
        matrix = csr_matrix((data[prefix+'_data'], data[prefix+'_indices'], data[prefix+'_indptr']), shape=tuple(data[prefix+'_shape']))
        assert matrix.shape == (len(expected), model.n)
        rhs = data['b_eq' if prefix == 'A_eq' else 'b_ub']
        for index, (row, bound) in enumerate(expected):
            saved = matrix.getrow(index)
            got = {int(column): Q(float(value)).limit_denominator(10**9) for column, value in zip(saved.indices, saved.data) if value}
            assert got == row, (prefix, index)
            assert Q(float(rhs[index])).limit_denominator(10**9) == bound
    assert np.array_equal(data['bounds'], np.array([[0., 1.]]*model.n))
    assert np.array_equal(data['state_indices'], model.z)
    if 'native_deficit_indices' in data:
        assert np.array_equal(data['native_deficit_indices'], list(model.deficits.values()))


def repaired_dual_bound(model, cost, equality_dual, inequality_dual, return_details=False):
    """Rigorous min bound for any rational y and nonpositive rational mu.

    c*x >= y*b_eq + mu*b_ub + min_{x in [0,1]^n} r*x,
    where r=c-A_eq^T*y-A_ub^T*mu. No stationarity assumption is needed.
    """
    assert len(cost) == model.n and len(equality_dual) == len(model.eq) and len(inequality_dual) == len(model.ub)
    assert max(inequality_dual) <= 0
    residual = list(cost);bound = Q(0)
    for multiplier, (row, rhs) in zip(equality_dual, model.eq):
        bound += multiplier*rhs
        for column, value in row.items():residual[column] -= multiplier*value
    for multiplier, (row, rhs) in zip(inequality_dual, model.ub):
        bound += multiplier*rhs
        for column, value in row.items():residual[column] -= multiplier*value
    correction = sum(min(Q(0), entry) for entry in residual)
    return (bound+correction, correction, residual, bound) if return_details else (bound+correction, correction)


def smoke_certificate(model, path):
    data = np.load(path);check_saved_model(model, data)
    solution, cost = data['solution'], data['cost']
    errors = {}
    def compare(name, actual, expected):
        error = float(np.max(abs(np.asarray(actual)-np.asarray(expected)), initial=0))
        errors[name] = max(errors.get(name, 0.), error)
        assert error <= 2e-7, (name, error)
    for label, rows in (('eq', model.eq), ('ub', model.ub)):
        residual = np.array([sum(float(value)*solution[column] for column, value in row.items())-float(rhs) for row, rhs in rows])
        compare(label+'_primal', residual if label == 'eq' else np.maximum(residual, 0.), 0.)
    compare('bounds', np.maximum(np.maximum(-solution, solution-1), 0.), 0.)
    compare('cost_binding', cost[model.z], -data['state_coefficients'])
    assert np.count_nonzero(np.delete(cost, model.z)) == 0
    actions = data['action_rows'];hist_index = {history: index for index, history in enumerate(sum(model.levels[:-1], []))}
    weights = {(): 1.}
    for level in model.levels[:-1]:
        for history in level:
            row = actions[hist_index[history]]
            compare('policy_stochastic', row.sum(), 1.)
            assert row.min() >= -2e-7
            for action, observation in EDGES:weights[history+((action, observation),)] = weights[history]*row[action]
    replay = np.array([[weights[h]*float(model.likelihoods[h][world]) for h in model.histories] for world in range(4)])
    compare('full_policy_replay', replay, data['full_source_kernel'])
    compressed = np.array([replay[:,[signed_counts(h) == state for h in model.histories]].sum(axis=1) for state in model.states]).T
    compare('ray_policy_replay', compressed, data['source_kernel'])
    compare('ray_solution_binding', compressed, np.array(model.rays, float).T*solution[model.z])
    decoder_errors = {}
    for name, allocation_indices in model.allocations.items():
        allocation = solution[np.array(allocation_indices)]
        compare(name+'_allocation_rows', allocation.sum(axis=1), solution[model.z])
        simulated = np.array(model.rays, float).T@allocation
        error = float(np.max(abs(simulated-np.array(model.targets[name]['rows'], float)).sum(axis=1)/2))
        decoder_errors[name] = error
        assert error <= (2e-7 if name == 'LR' else solution[model.deficits[name]]+2e-7)
    assert decoder_errors['LLL']+decoder_errors['RRR'] <= .072+2e-7
    # Rationalize only multipliers; the model is the independently assembled exact one.
    y = [Q(float(value)).limit_denominator(10**8) for value in data['eq_dual']]
    mu = [min(Q(0), Q(float(value)).limit_denominator(10**8)) for value in data['ub_dual']]
    exact_cost = [Q(float(value)) for value in cost]
    lower, correction = repaired_dual_bound(model, exact_cost, y, mu)
    maximum_upper = -lower
    numerical_value = -float(cost@solution)
    assert numerical_value <= float(maximum_upper)+2e-7
    return {'input': path.name, 'sha256': digest(path), 'exact_model_rows_verified': len(model.eq)+len(model.ub),
            'max_errors': errors, 'native_decoder_upper_errors': decoder_errors,
            'numerical_maximum': numerical_value, 'exact_repaired_maximum_upper': str(maximum_upper),
            'dual_box_correction': str(correction),
            'numerical_value_minus_exact_upper': numerical_value-float(maximum_upper)}


def verify_exact_model_export(model, path):
    data = json.loads(path.read_text())
    assert data['source_sha256'] == digest(HERE/'exact_oracle_certificate.py')
    assert data['oracle_sha256'] == digest(HERE/'compressed_oracle.py')
    assert data['variables'] == model.n and data['bounds'] == ['0', '1']
    assert list(map(tuple, data['states'])) == model.states and data['state_indices'] == model.z
    for names, expected in ((('equalities', 'equality_rhs'), model.eq), (('inequalities', 'inequality_rhs'), model.ub)):
        rows, rhs = data[names[0]], data[names[1]]
        assert len(rows) == len(rhs) == len(expected)
        for actual, bound, (row, target) in zip(rows, rhs, expected):
            coefficients = {index: Q(value) for index, value in actual}
            assert len(coefficients) == len(actual)
            assert coefficients == row and Q(bound) == target
    return {'path': path.name, 'sha256': digest(path), 'exact_sparse_row_checks': len(model.eq)+len(model.ub)}


def verify_repaired_certificate(model, certificate):
    coefficients = list(map(Q, certificate['coefficients']))
    assert len(coefficients) == len(model.z)
    cost = [Q(0)]*model.n
    for index, coefficient in zip(model.z, coefficients):cost[index] = -coefficient
    equality = list(map(Q, certificate['equality_multipliers']))
    inequality = list(map(Q, certificate['inequality_multipliers']))
    lower, correction, residual, constant = repaired_dual_bound(model, cost, equality, inequality, True)
    assert Q(certificate['minimization_lower']) == lower
    assert Q(certificate['upper']) == -lower
    assert Q(certificate['lagrangian_constant']) == constant
    assert Q(certificate['box_residual_correction']) == correction
    assert list(map(Q, certificate['stationarity_residual'])) == residual
    assert Q(certificate['maximum_stationarity_residual']) == max(map(abs, residual))
    return {'exact_upper': str(-lower), 'exact_upper_float': float(-lower),
            'residual_coordinates_checked': len(residual),
            'exact_box_correction': str(correction),
            'exact_nonpositive_inequality_multipliers_checked': len(inequality)}


def verify_exact_smoke(model, path):
    data = json.loads(path.read_text())
    assert data['source_sha256'] == digest(HERE/'exact_oracle_certificate.py')
    assert data['model_sha256'] == digest(HERE/'compressed_oracle_exact_model.json')
    assert len(data['tests']) == 3
    return {'input_path': path.name, 'input_sha256': digest(path),
            'certificates': [verify_repaired_certificate(model, certificate) for certificate in data['tests']]}


def verify_five_target(model):
    original = model.targets['adaptive_L']['rows']
    groups = [[0], [1], [2, 4], [3], [5]]
    assert all(row[4] == 2*row[2] for row in original)
    compressed = [[sum(row[index] for index in group) for group in groups] for row in original]
    encoding = [[Q(int(index in group)) for group in groups] for index in range(6)]
    lift = [[Q(0)]*6 for _ in groups]
    for index, group in enumerate(groups):
        if len(group) == 1:lift[index][group[0]] = Q(1)
        else:lift[index][2], lift[index][4] = Q(1, 3), Q(2, 3)
    assert INDEPENDENT.matmul(original, encoding) == compressed
    assert INDEPENDENT.matmul(compressed, lift) == original
    assert INDEPENDENT.matmul(lift, encoding) == [[Q(int(i == j)) for j in range(5)] for i in range(5)]
    assert all(sum(row) == 1 and min(row) >= 0 for row in lift)
    assert all(sum(row[index] != 0 for row in lift) == 1 for index in range(6))
    full_groups = [[0], [1, 2], [3, 5, 6], [4], [7]]
    full_lift = [[Q(int(index in group), len(group)) for index in range(8)] for group in full_groups]
    assert INDEPENDENT.matmul(compressed, full_lift) == model.targets['adaptive_L']['full']
    return {'groups_from_six': groups, 'full_output_groups': full_groups,
            'exact_mutual_garblings': True, 'exact_TV_isometry': True,
            'target_rows': [[str(x) for x in row] for row in compressed]}


def verify_linear_certificate(model, certificate):
    objective = list(map(Q, certificate['max_objective']))
    assert len(objective) == model.n
    equality = list(map(Q, certificate['equality_multipliers']))
    inequality = list(map(Q, certificate['inequality_multipliers']))
    lower, correction, residual, constant = repaired_dual_bound(model, [-x for x in objective], equality, inequality, True)
    assert Q(certificate['minimization_lower']) == lower and Q(certificate['upper']) == -lower
    assert Q(certificate['lagrangian_constant']) == constant
    assert Q(certificate['box_residual_correction']) == correction
    assert list(map(Q, certificate['stationarity_residual'])) == residual
    return {'exact_upper': str(-lower), 'exact_upper_float': float(-lower),
            'residual_coordinates_checked': len(residual),
            'exact_nonpositive_inequality_multipliers_checked': len(inequality)}


def verify_linear_smoke(model, path):
    data = json.loads(path.read_text())
    assert data['source_sha256'] == digest(HERE/'linear_native_oracle.py')
    assert data['compressed_oracle_sha256'] == digest(HERE/'compressed_oracle.py')
    assert data['exact_helper_sha256'] == digest(HERE/'exact_oracle_certificate.py')
    terminal = model.reachable[-1]
    indices = [model.w[history] for history in terminal]
    assert tuple(tuple(map(tuple, history)) for history in data['terminal_histories']) == tuple(terminal)
    assert data['terminal_indices'] == indices
    results = []
    for index, report in enumerate(data['tests']):
        arrays = np.load(HERE/f'linear_native_smoke_{index}.npz')
        check_saved_model(model, arrays)
        assert np.array_equal(arrays['terminal_indices'], indices)
        expected_laws = np.array([model.likelihoods[h] for h in terminal], float).T
        assert np.array_equal(arrays['terminal_prefix_laws'], expected_laws)
        objective = np.array(list(map(Q, report['exact']['max_objective'])), float)
        assert np.max(abs(arrays['cost']+objective)) <= 1e-14
        assert np.count_nonzero(np.delete(objective, indices)) == 0
        solution = arrays['solution'];errors = {}
        for label, rows in (('eq', model.eq), ('ub', model.ub)):
            differences = [sum(float(v)*solution[k] for k, v in row.items())-float(rhs) for row, rhs in rows]
            error = max(abs(x) for x in differences) if label == 'eq' else max(0., max(differences))
            assert error <= 2e-7;errors[label] = error
        assert np.max(np.maximum(-solution, solution-1)) <= 2e-7
        source = expected_laws*solution[indices]
        assert np.max(abs(source-arrays['source_kernel'])) <= 2e-7
        full = np.zeros((4, 625));positions = [model.histories.index(h) for h in terminal]
        full[:, positions] = source
        assert np.max(abs(full-arrays['full_source_kernel'])) <= 2e-7
        assert np.max(abs(np.array(model.rays, float).T*solution[model.z]-arrays['compressed_source_kernel'])) <= 2e-7
        values = {'input': f'linear_native_smoke_{index}.npz',
                  'sha256': digest(HERE/f'linear_native_smoke_{index}.npz'),
                  'max_errors': errors, **verify_linear_certificate(model, report['exact'])}
        results.append(values)
    assert len(results) == 3
    return {'input_path': path.name, 'input_sha256': digest(path), 'certificates': results}


def main():
    model = ExactModel()
    metadata_path = HERE/'compressed_oracle_metadata.json'
    metadata = json.loads(metadata_path.read_text())
    checks = verify_metadata(model, metadata)
    controls = randomized_equivalence_controls(model)
    smoke_paths = sorted(HERE.glob('compressed_oracle_smoke_*.npz'))
    assert len(smoke_paths) == 3
    smoke = [smoke_certificate(model, path) for path in smoke_paths]
    output = {'status': 'passed', 'audit_source_sha256': digest(Path(__file__)),
              'independent_model_source_sha256': digest(HERE/'audit.py'),
              'protocol_sha256': digest(HERE/'PROTOCOL.md'),
              'metadata_sha256': digest(metadata_path), 'variables': model.n,
              'equalities': len(model.eq), 'inequalities': len(model.ub),
              'exact_metadata_checks': checks, 'randomized_policy_controls': controls,
              'smoke_certificates': smoke,
              'exact_model_export': verify_exact_model_export(model, HERE/'compressed_oracle_exact_model.json'),
              'exact_dual_certificate_smoke': verify_exact_smoke(model, HERE/'exact_oracle_certificate_smoke.json'),
              'five_signal_adaptive_target': verify_five_target(model),
              'linear_oracle_smoke': verify_linear_smoke(model, HERE/'linear_native_smoke.json'),
              'scope': ('Exact source/target compression and intended constraint reconstruction; '
                        'numerical smoke feasibility with exact repaired dual bounds. '
                        'All randomized full-history policies in the native-optimal set remain represented. '
                        'No shared-decoder or worst-adaptive-deficiency conclusion follows by itself.')}
    (HERE/'audit_compressed.json').write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps({key: value for key, value in output.items() if key not in ('smoke_certificates', 'exact_dual_certificate_smoke', 'linear_oracle_smoke')}, indent=2))


if __name__ == '__main__':
    main()
