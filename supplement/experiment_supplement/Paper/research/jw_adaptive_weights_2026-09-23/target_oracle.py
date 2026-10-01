"""Exact fixed-dual native-target dynamic program; NOT a global hardest-target oracle.

Uses full action/observation histories, finite worlds, and supplied valid causal
controlled masses. The recursion avoids enumeration of contingent policy trees.
The remaining outer maximization is nonconcave (THEORY.md). A returned target is
only a lower witness for a global worst-target search.
"""
from fractions import Fraction as F
from adaptive_weights import rational


def fixed_dual_target(raw, alpha, b, *, actions, observations, depth, max_columns=4096):
    if any(type(x) is not int for x in (actions,observations,depth)):
        raise TypeError('Integer finite alphabets and depth required')
    if not 1 <= actions <= 8 or not 1 <= observations <= 8 or not 0 <= depth <= 8:
        raise ValueError('Prepared interface/depth cap exceeded')
    columns=(actions*observations)**depth
    if columns>max_columns: raise ValueError('Explicit history cap exceeded')
    raw=tuple(tuple(map(rational,r)) for r in raw)
    alpha=tuple(map(rational,alpha));b=tuple(tuple(map(rational,r)) for r in b)
    if not raw or len(raw)!=len(alpha) or len(b)!=len(alpha): raise ValueError('World mismatch')
    if any(len(row)!=columns for row in raw+b): raise ValueError('Use common complete target alphabet')
    if sum(alpha)!=1 or any(a<0 for a in alpha): raise ValueError('Invalid dual world weights')
    if any(not 0<=value<=1 for row in raw for value in row): raise ValueError('Invalid controlled masses')
    if any(not 0<=b[q][j]<=alpha[q] for q in range(len(alpha)) for j in range(columns)):
        raise ValueError('Infeasible dual')
    layers=[[()]]
    for _ in range(depth):
        layers.append([h+((a,o),) for h in layers[-1] for a in range(actions) for o in range(observations)])
    values={h:sum((raw[q][j]*b[q][j] for q in range(len(alpha))),F(0))
            for j,h in enumerate(layers[-1])}
    selected={}
    for layer in reversed(layers[:-1]):
        for h in layer:
            choices=[sum((values[h+((a,o),)] for o in range(observations)),F(0)) for a in range(actions)]
            a=max(range(actions),key=lambda action: choices[action])
            values[h]=choices[a]; selected[h]=a
    weights=[int(all(selected[h[:i]]==a for i,(a,_) in enumerate(h))) for h in layers[-1]]
    target=tuple(tuple(p*w for p,w in zip(row,weights)) for row in raw)
    if any(sum(row)!=1 for row in target): raise ValueError('Input masses failed resulting native-law check')
    return {'linear_value':values[()], 'target_kernel':target,
        'policy_actions':[(h,selected[h]) for layer in layers[:-1] for h in layer],
        'global_hardest_target_upper':None,
        'scope':'exact fixed-dual linear best response; causal input validity assumed'}


def source_penalty(source,b):
    source=tuple(tuple(map(rational,row)) for row in source)
    b=tuple(tuple(map(rational,row)) for row in b)
    if not source or len(source)!=len(b) or not b[0] or not source[0]: raise ValueError('Empty/mismatched matrices')
    if any(len(r)!=len(source[0]) or sum(r)!=1 or any(p<0 for p in r) for r in source):
        raise ValueError('Source must be row stochastic')
    if any(len(row)!=len(b[0]) for row in b): raise ValueError('Dual shape mismatch')
    return sum((max(sum((source[q][x]*b[q][y] for q in range(len(source))),F(0))
                    for y in range(len(b[0]))) for x in range(len(source[0]))),F(0))
