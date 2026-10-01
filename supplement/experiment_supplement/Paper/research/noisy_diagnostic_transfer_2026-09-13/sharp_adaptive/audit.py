#!/usr/bin/env python3
"""Exact independent H4 native-repeat optimum and adaptive lower-witness audit.

Uses only rational arithmetic and a count-state Bellman recursion, with no
planner imports or new numerical LP solves. A fixed RRRL collector is certified
by explicit stochastic decoders and a matching prior-weighted guessing witness.
The Bellman certificate proves the global weighted-native-loss minimum; it does
not prove the worst adaptive deficiency over the entire optimal policy set.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from functools import lru_cache
import hashlib
from itertools import product
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
E = Q(1, 10)
WORLDS = tuple(product((0, 1), repeat=2))
WEIGHTS = {'L': Q(1, 5), 'R': Q(1, 5), 'tagged': Q(1, 10),
           'LR': Q(1, 10), 'LLL': Q(1, 10), 'RRR': Q(1, 10)}
EDGES = ((0, 0), (0, 1), (1, 0), (1, 1), (2, 0))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strings(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {key: strings(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [strings(item) for item in value]
    return value


def observations(length):
    return tuple(product((0, 1), repeat=length))


def sensor_probability(bit, observation):
    return 1-E if bit == observation else E


def word_kernel(word):
    result = []
    for world in WORLDS:
        row = []
        for obs in observations(len(word)):
            value = Q(1)
            for action, observation in zip(word, obs):
                value *= sensor_probability(world[action == 'R'], observation)
            row.append(value)
        result.append(row)
    return result


def target_kernel(name):
    if name == 'tagged':
        left, right = word_kernel('L'), word_kernel('R')
        return [[p/2 for p in l+r] for l, r in zip(left, right)]
    if name != 'adaptive_L':
        return word_kernel(name)
    rows = []
    for world in WORLDS:
        row = []
        for obs in observations(3):
            actions = (0, obs[0], obs[0])
            value = Q(1)
            for action, observation in zip(actions, obs):
                value *= sensor_probability(world[action], observation)
            row.append(value)
        rows.append(row)
    return rows


def matmul(left, right):
    return [[sum(a*b for a, b in zip(row, column)) for column in zip(*right)] for row in left]


def tv(left, right):
    return sum(abs(a-b) for a, b in zip(left, right))/2


def bit_guess_value(kernel, bit, prior=None):
    prior = prior or [Q(1, 4)]*4
    return sum(max(sum(prior[t]*kernel[t][x] for t in range(4) if WORLDS[t][bit] == answer)
                   for answer in (0, 1)) for x in range(len(kernel[0])))


def explicit_witness():
    source = word_kernel('RRRL')
    source_outputs = observations(4)
    triple_outputs = observations(3)
    # One noisy bit -> triple record: report xxx with probability .73;
    # otherwise flip one uniformly chosen position, probability .09 each.
    single_to_triple = []
    for value in (0, 1):
        row = []
        for triple in triple_outputs:
            mismatches = sum(bit != value for bit in triple)
            row.append(Q(73, 100) if mismatches == 0 else Q(9, 100) if mismatches == 1 else Q(0))
        assert sum(row) == 1
        single_to_triple.append(row)
    decoders, deficiencies, target_rows = {}, {}, {}
    for name in (*WEIGHTS, 'adaptive_L'):
        target = target_kernel(name)
        target_rows[name] = target
        rows = []
        for obs in source_outputs:
            row = [Q(0)]*len(target[0])
            if name == 'L':
                row[obs[3]] = 1
            elif name == 'R':
                row[obs[0]] = 1
            elif name == 'tagged':
                row[obs[3]] = Q(1, 2)
                row[2+obs[0]] = Q(1, 2)
            elif name == 'LR':
                row[2*obs[3]+obs[0]] = 1
            elif name == 'RRR':
                row[4*obs[0]+2*obs[1]+obs[2]] = 1
            elif name == 'LLL':
                row = list(single_to_triple[obs[3]])
            else:
                for triple, probability in zip(triple_outputs, single_to_triple[obs[3]]):
                    output = triple if triple[0] == 0 else (1, obs[0], obs[1])
                    row[4*output[0]+2*output[1]+output[2]] += probability
            assert min(row) >= 0 and sum(row) == 1
            rows.append(row)
        simulated = matmul(source, rows)
        deficiencies[name] = max(tv(a, b) for a, b in zip(simulated, target))
        decoders[name] = rows
    assert all(deficiencies[name] == 0 for name in ('L', 'R', 'tagged', 'LR', 'RRR'))
    assert deficiencies['LLL'] == deficiencies['adaptive_L'] == Q(9, 125)
    weighted_cost = sum(WEIGHTS[name]*deficiencies[name] for name in WEIGHTS)
    assert weighted_cost == Q(9, 1250)
    # A prior supported on V=1 with P(U=0)=.1. The source cannot improve
    # on always guessing U=1; the target gains by guessing U=0 at 000.
    prior = [Q(0), Q(1, 10), Q(0), Q(9, 10)]
    source_value = bit_guess_value(source, 0, prior)
    target = target_rows['adaptive_L']
    target_rule_value = sum(prior[t]*sum(target[t][x] for x in range(8)
                                        if (0 if x == 0 else 1) == WORLDS[t][0]) for t in range(4))
    assert source_value == Q(9, 10)
    assert target_rule_value == bit_guess_value(target, 0, prior) == Q(243, 250)
    assert target_rule_value-source_value == deficiencies['adaptive_L']
    assert bit_guess_value(target_rows['LLL'], 0)-bit_guess_value(source, 0) == deficiencies['LLL']
    return {'collector_word': 'RRRL', 'worlds': WORLDS, 'source_output_sequences': source_outputs,
            'source_kernel': source, 'target_kernels': target_rows, 'decoders': decoders,
            'decoder_upper_deficiencies': deficiencies, 'native_weighted_cost': weighted_cost,
            'single_to_triple_decoder': single_to_triple,
            'adaptive_matching_decision': {'prior': prior, 'target_guesses_zero_only_at': [0, 0, 0],
                                           'source_optimal_value': source_value,
                                           'target_rule_value': target_rule_value,
                                           'deficiency_lower_bound': target_rule_value-source_value},
            'exact_adaptive_deficiency': deficiencies['adaptive_L'],
            'source_uniform_bit_accuracies': [bit_guess_value(source, bit) for bit in (0, 1)]}


def posterior_one(reads, ones):
    likelihood_one = (1-E)**ones*E**(reads-ones)
    likelihood_zero = E**ones*(1-E)**(reads-ones)
    return likelihood_one/(likelihood_one+likelihood_zero)


def next_state(state, action, observation):
    if action == 2:
        assert observation == 0
        return state
    counts = list(state)
    counts[2*action] += 1
    counts[2*action+1] += observation
    return tuple(counts)


def predictive_probability(state, action, observation):
    if action == 2:
        return Q(int(observation == 0))
    belief = posterior_one(state[2*action], state[2*action+1])
    probability_one = belief*(1-E)+(1-belief)*E
    return probability_one if observation else 1-probability_one


@lru_cache(None)
def bellman(state, remaining):
    if remaining == 0:
        return sum(max(belief, 1-belief) for belief in
                   (posterior_one(state[0], state[1]), posterior_one(state[2], state[3])))
    return max(action_value(state, remaining, action) for action in range(3))


def action_value(state, remaining, action):
    return sum(predictive_probability(state, action, observation)
               *bellman(next_state(state, action, observation), remaining-1)
               for observation in ((0,) if action == 2 else (0, 1)))


def bellman_certificate():
    root = bellman((0, 0, 0, 0), 4)
    assert root == Q(234, 125)
    histories, rows = [()], []
    for depth in range(4):
        new_histories = []
        for history in histories:
            state = (0, 0, 0, 0)
            for action, observation in history:
                state = next_state(state, action, observation)
            value = bellman(state, 4-depth)
            choices = [action_value(state, 4-depth, action) for action in range(3)]
            allowed = [action for action in range(3) if choices[action] == value]
            advantages = [value-choice for choice in choices]
            assert allowed and min(advantages) >= 0
            rows.append({'history': history, 'count_state': state, 'remaining': 4-depth,
                         'value': value, 'action_values': choices,
                         'advantages': advantages, 'allowed_actions': allowed})
            new_histories.extend(history+(edge,) for edge in EDGES)
        histories = new_histories
    assert len(rows) == 156
    target_bit_value = bit_guess_value(word_kernel('LLL'), 0)
    assert target_bit_value == Q(243, 250)
    native_lower = (2*target_bit_value-root)/10
    assert native_lower == Q(9, 1250)
    return {'horizon': 4, 'noise': [E, E], 'root_maximum_uniform_bit_accuracy_sum': root,
            'triple_target_bit_accuracy': target_bit_value,
            'native_weighted_cost_lower_bound': native_lower,
            'history_rows': rows, 'count_state_cache': bellman.cache_info()._asdict(),
            'face_implication': ('Every exact native-repeat minimizer must attain this Bayes-sum maximum; '
                                 'hence its positive-probability actions have zero Bellman advantage. '
                                 'The converse is not asserted; retain native-cost constraints.')}


def history_likelihoods(history):
    likelihoods = []
    for world in WORLDS:
        probability = Q(1)
        for action, observation in history:
            probability *= Q(1) if action == 2 else sensor_probability(world[action], observation)
        likelihoods.append(probability)
    return likelihoods


def verify_bellman_table(path, independent):
    data = json.loads(path.read_text())
    assert data['H'] == 4 and Q(data['root_value']) == Q(234, 125)
    assert Q(data['native_lower_bound']) == Q(9, 1250)
    declared = {tuple(map(tuple, row['history'])): row for row in data['rows']}
    assert len(declared) == len(data['rows']) == len(independent['history_rows']) == 156
    for row in independent['history_rows']:
        history = tuple(map(tuple, row['history']))
        candidate = declared[history]
        # Their coefficients include the uniform-prior prefix mass; our
        # recursion conditions on the count posterior at this history.
        mass = sum(history_likelihoods(history))/4
        assert Q(candidate['value']) == mass*row['value']
        assert list(map(Q, candidate['action_values'])) == [mass*x for x in row['action_values']]
        assert list(map(Q, candidate['advantages'])) == [mass*x for x in row['advantages']]
        assert candidate['allowed_actions'] == row['allowed_actions']
    terminal = [()]
    for _ in range(4):
        terminal = [history+(edge,) for history in terminal for edge in EDGES]
    assert len(terminal) == len(data['terminal_coefficients']) == 625
    for history, coefficient in zip(terminal, data['terminal_coefficients']):
        likelihoods = history_likelihoods(history)
        value = sum(max(sum(likelihoods[t]/4 for t in range(4) if WORLDS[t][bit] == guess)
                        for guess in (0, 1)) for bit in (0, 1))
        assert Q(coefficient) == value
    return {'input_path': path.name, 'input_sha256': digest(path),
            'exact_action_history_checks': 156, 'exact_terminal_coefficient_checks': 625,
            'posterior_vs_prefix_mass_normalization_checked': True}


def verify_shared_upper(path, bellman_result):
    """Independently verify a full-history decoder over the exact optimal face.

    Uses normalized, world-conditional continuation recursion, whereas the
    search producer uses unnormalized prefix masses in a sparse LP.
    """
    certificate = json.loads(path.read_text())
    assert Q(certificate['noise']) == E and certificate['horizon'] == 4
    assert certificate['protocol_sha256'] == digest(HERE/'PROTOCOL.md')
    assert Q(certificate['root_value']) == bellman_result['root_maximum_uniform_bit_accuracy_sum']
    rows = {tuple(map(tuple, row['history'])): row for row in bellman_result['history_rows']}
    levels = [[()]]
    for _ in range(4):
        levels.append([history+((action, observation),) for history in levels[-1]
                       for action, observation in EDGES if action in rows[history]['allowed_actions']])
    terminal = tuple(tuple(map(tuple, history)) for history in certificate['terminal_histories'])
    assert terminal == tuple(levels[-1])
    assert list(map(len, levels)) == certificate['reachable_sizes']
    labels = tuple(product((0, 1), range(3)))
    assert tuple(map(tuple, certificate['target_labels'])) == labels
    full_sequences = observations(3)
    groups = [[index for index, obs in enumerate(full_sequences)
               if (obs[0], obs[1]+obs[2]) == label] for label in labels]
    full_target = target_kernel('adaptive_L')
    target = [[sum(row[index] for index in group) for group in groups] for row in full_target]
    assert [[Q(x) for x in row] for row in certificate['target_rows']] == target
    uniform_lift = [[Q(int(index in group), len(group)) for index in range(8)] for group in groups]
    assert matmul(target, uniform_lift) == full_target
    assert all(sum(row) == 1 for row in uniform_lift)
    assert all(sum(row[index] != 0 for row in uniform_lift) == 1 for index in range(8))
    decoder = [[Q(x) for x in row] for row in certificate['decoder']]
    assert len(decoder) == len(terminal)
    assert all(len(row) == 6 and sum(row) == 1 and min(row) >= 0 for row in decoder)
    by_history = dict(zip(terminal, decoder))
    stored_events = {(row['world'], row['event']): row for row in certificate['event_checks']}
    assert len(stored_events) == len(certificate['event_checks']) == 256
    results, worst = [], Q(0)
    for world_index, world in enumerate(WORLDS):
        for mask in range(64):
            @lru_cache(None)
            def continuation(history):
                if len(history) == 4:
                    return sum(probability for index, probability in enumerate(by_history[history])
                               if mask & (1 << index))
                return max(sum((Q(1) if action == 2 else sensor_probability(world[action], observation))
                               *continuation(history+((action, observation),))
                               for observation in ((0,) if action == 2 else (0, 1)))
                           for action in rows[history]['allowed_actions'])
            source_maximum = continuation(())
            target_event = sum(probability for index, probability in enumerate(target[world_index])
                               if mask & (1 << index))
            gap = source_maximum-target_event
            stored = stored_events[world_index, mask]
            assert Q(stored['source_max']) == source_maximum
            assert Q(stored['target']) == target_event and Q(stored['gap']) == gap
            worst = max(worst, gap)
            results.append({'world': world_index, 'event': mask, 'exact_gap': gap})
    assert worst == Q(certificate['exact_upper'])
    return {'input_path': str(path.name), 'input_sha256': digest(path),
            'producer_source_sha256': certificate['source_sha256'],
            'exact_target_compression_checked': True, 'exact_decoder_stochasticity_checked': True,
            'reachable_sizes': list(map(len, levels)), 'event_world_checks': len(results),
            'exact_shared_decoder_upper': worst, 'event_results': results,
            'scope': 'Uniform upper over every Bellman-optimal policy, hence every native-repeat minimizer.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upper', type=Path, help='Optional shared full-history decoder certificate to audit exactly.')
    parser.add_argument('--bellman', type=Path, help='Optional independent planner Bellman table to compare exactly.')
    args = parser.parse_args()
    witness = explicit_witness()
    bellman_result = bellman_certificate()
    assert witness['native_weighted_cost'] == bellman_result['native_weighted_cost_lower_bound']
    output = {'status': 'passed', 'audit_source_sha256': digest(Path(__file__)),
              'protocol_sha256': digest(HERE/'PROTOCOL.md'),
              'scope': ('Exact H4 native weighted-loss minimum, exact RRRL adaptive lower witness, '
                        'and necessary Bellman support restriction; no all-optimal-policy upper bound.'),
              'witness': witness, 'bellman': bellman_result}
    if args.bellman:
        output['planner_bellman_audit'] = verify_bellman_table(args.bellman.resolve(), bellman_result)
    if args.upper:
        output['shared_upper_audit'] = verify_shared_upper(args.upper.resolve(), bellman_result)
        output['scope'] += ' Exact supplied common-decoder upper is independently verified.'
    for filename, data in (('audit_results.json', output), ('audit_bellman.json', dict(status='passed', audit_source_sha256=output['audit_source_sha256'], protocol_sha256=output['protocol_sha256'], **bellman_result))):
        (HERE/filename).write_text(json.dumps(strings(data), indent=2)+'\n')
    print(json.dumps(strings({'status': output['status'], 'audit_source_sha256': output['audit_source_sha256'],
                            'native_minimum': witness['native_weighted_cost'],
                            'exact_adaptive_witness': witness['exact_adaptive_deficiency'],
                            'bayes_sum_maximum': bellman_result['root_maximum_uniform_bit_accuracy_sum'],
                            'bellman_history_count': len(bellman_result['history_rows'])}), indent=2))


if __name__ == '__main__':
    main()
