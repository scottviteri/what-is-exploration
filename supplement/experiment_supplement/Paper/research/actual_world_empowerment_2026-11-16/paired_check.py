#!/usr/bin/env python3
"""Exact bounded channels for the selected paired alarm; no training or infinite-policy enumeration."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import hashlib
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def response(world, history, action):
    if not history:
        if action == 0:
            return {(2*int(world is not None), 0): F(1)}
        return {(0, 0): F(1)}
    monitor = int(world == len(history)-1)
    if history[0][0] == 0:
        return {(0, monitor): F(1)}
    return {(2*int(action == 2)+color, monitor): F(1, 2) for color in (0, 1)}

def sequence_row(world, history, word):
    law = {(): F(1)}
    for action in word:
        nxt = defaultdict(F)
        for outputs, mass in law.items():
            past = history + tuple(zip(word[:len(outputs)], outputs))
            for obs, p in response(world, past, action).items():
                nxt[outputs+(obs,)] += mass*p
        law = nxt
    return dict(law)

def prefix(world, length, inspection):
    h = ()
    for t in range(length):
        a = 0 if t == 0 and inspection else 1
        h += ((a, next(iter(response(world, h, a)))),)
    return h

def entropy(law):
    return -sum(float(p)*math.log2(float(p)) for p in law if p)

def main():
    counts = defaultdict(int)
    for world, t, inspection, n in product((None, *range(7)), range(1, 7), (False, True), range(1, 5)):
        h = prefix(world, t, inspection)
        digit_rows = {}
        for word in product(range(3), repeat=n):
            row = sequence_row(world, h, word)
            assert sum(row.values()) == 1
            digits = () if inspection else tuple(int(a == 2) for a in word)
            if digits in digit_rows:
                assert digit_rows[digits] == row  # no further information in action aliases
            digit_rows[digits] = row
            for outputs, p in row.items():
                expected = F(1)
                for j, (a, o) in enumerate(zip(word, outputs)):
                    expected *= response(world, h+tuple(zip(word[:j], outputs[:j])), a).get(o, F(0))
                assert p == expected
                assert tuple(o[1] for o in outputs) == tuple(int(world == t+j-1) for j in range(n))
                if not inspection:
                    assert tuple(o[0]//2 for o in outputs) == digits
            counts['actual_world_action_rows'] += 1
        # Upper bound: row depends only on n digit bits; lower bound: output decodes them.
        # Distinct row supports are disjoint, so the channel transmits precisely these bits.
        assert len(digit_rows) == (1 if inspection else 2**n)
        seen = set()
        for row in digit_rows.values():
            assert not seen.intersection(row)
            seen.update(row)
        counts['exact_full_block_capacity_certificates'] += 1
    for world in (None, *range(7)):
        rows = [sequence_row(world, (), (a,)) for a in range(3)]
        nu = (F(1,2), F(1,2), F(0))
        out = defaultdict(F)
        for w, row in zip(nu, rows):
            for y, p in row.items():
                out[y] += w*p
        mi = entropy(out.values()) - sum(float(w)*entropy(row.values()) for w,row in zip(nu,rows))
        expected = 0 if world is None else 1
        # Identical deterministic rows give capacity zero. Otherwise two distinct
        # deterministic outputs give capacity one, attained by the fair input.
        assert len({tuple(row) for row in rows}) == 2**expected
        assert mi == expected
        counts['exact_root_capacity_certificates'] += 1
    for n,T,s in product(range(1,17),range(1,65),(F(0),F(1,5),F(3,5),F(1))):
        direct = sum(sum(1 for _ in range(n)) for _ in range(1,T))
        assert direct == n*(T-1)
        if T >= 2:
            assert ((1-s)*direct == direct) == (s == 0)
        counts['finite_return_identities'] += 1
    inputs = [Path(__file__), ROOT/'Formal/Formal/PairedAlarm.lean', ROOT/'Formal/Formal/PairedAlarmBlockComplete.lean', ROOT/'Formal/Formal/PairedAlarmBlockChannel.lean', ROOT/'Paper/draft/intrinsic_rewards/next_alarm_proofs.tex']
    result = {'status':'passed', 'scope':'Exact rational actual-world rows for n=1..4, t=1..6, eight worlds, both modes. Capacity certified by input-digit factorization and disjoint output supports. Startup capacities certified by deterministic output classes; fair-input MI agrees exactly. Finite sum identities; no all-policy/infinite-sum enumeration.', 'counts':dict(counts), 'root_one_step_capacity_bits':{'never_alarm':0,'finite_alarm':1,'prior_expectation':0.5}, 'inputs_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}, 'training_performed':False}
    (HERE/'paired_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result['counts'],indent=2))

if __name__ == '__main__':
    main()
