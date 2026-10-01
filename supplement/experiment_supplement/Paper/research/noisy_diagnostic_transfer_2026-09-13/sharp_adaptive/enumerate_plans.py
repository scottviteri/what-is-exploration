#!/usr/bin/env python3
"""Exhaustive pure Bellman-optimal plans, canonical experiments and decoders.

Enumeration covers a larger family than native optima. The coverage theorem and
independent replay are separate obligations; an optimizer representative alone
is never substituted for the whole near-optimal set.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
from functools import lru_cache
from math import gcd,lcm
import argparse,hashlib,importlib.util,json,time,sys
import numpy as np
from bellman_bound import exact_model,target,EDGES
HERE=Path(__file__).resolve().parent;PARENT=HERE.parent
spec=importlib.util.spec_from_file_location('parent_planner',PARENT/'compute.py');old=importlib.util.module_from_spec(spec);sys.modules[spec.name]=old;spec.loader.exec_module(old)

def canonical(experiment):
    groups={}
    for col in zip(*experiment):
        den=lcm(*(x.denominator for x in col));nums=tuple(int(x*den) for x in col);g=gcd(*nums)
        primitive=tuple(x//g for x in nums);groups[primitive]=groups.get(primitive,Q(0))+Q(g,den)
    keys=sorted(groups)
    E=[[Q(k[t])*groups[k] for k in keys] for t in range(4)]
    return tuple(tuple(x for x in row) for row in E)

def rounded_decoder(arr,den):
    out=[]
    for row in arr:
        rr=[Q(max(0,float(x))).limit_denominator(den) for x in row];j=max(range(len(rr)),key=lambda j:rr[j]);rr[j]=1-sum(x for k,x in enumerate(rr) if k!=j)
        if min(rr)<0:return None
        out.append(rr)
    return out

def error(E,D,T):
    return max(sum(abs(sum(E[t][x]*D[x][y] for x in range(len(D)))-T[t][y]) for y in range(len(T[t])))/2 for t in range(4))

def main(args):
    start=time.monotonic();levels,p,v,actions,reached=exact_model();T,labels=target(Q(1,10))
    leaf=reached[-1];li={h:i for i,h in enumerate(leaf)}
    @lru_cache(None)
    def plans(h):
        if len(h)==4:return ((li[h],),)
        out=[]
        for a in actions[h]:
            kids=[h+((aa,o),) for aa,o in EDGES if aa==a]
            for choice in product(*(plans(k) for k in kids)):out.append(tuple(x for branch in choice for x in branch))
        return tuple(out)
    raw=plans(());groups={};mapping=[]
    for leafset in raw:
        E=canonical([[p[leaf[k]][t] for k in leafset] for t in range(4)])
        assert all(sum(row)==1 for row in E)
        if E not in groups:groups[E]=dict(id=len(groups),representative=list(leafset),count=0)
        groups[E]['count']+=1;mapping.append(groups[E]['id'])
    print(json.dumps(dict(pure_plans=len(raw),canonical_experiments=len(groups))),flush=True)
    out=dict(status='running',scope='All deterministic Bellman-optimal plans; canonical merging of proportional experiment columns preserves Blackwell equivalence.',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),dependency_sha256=hashlib.sha256((HERE/'bellman_bound.py').read_bytes()).hexdigest(),parent_planner_sha256=hashlib.sha256((PARENT/'compute.py').read_bytes()).hexdigest(),protocol_sha256=hashlib.sha256((HERE/'PROTOCOL.md').read_bytes()).hexdigest(),pure_plans=len(raw),canonical_experiments=len(groups),terminal_histories=[[[a,o] for a,o in h] for h in leaf],plan_leafsets=[list(x) for x in raw],plan_to_experiment=mapping,experiments=[],failures=[])
    path=HERE/args.output
    for E,info in groups.items():
        value,wit=old.fixed_deficiency(np.array(E,float),np.array(T,float));candidates=[]
        for den in (100,1000,10000,1000000,1000000000):
            D=rounded_decoder(wit['decoder'],den)
            if D is not None:candidates.append((error(E,D,T),den,D))
        upper,den,D=min(candidates,key=lambda z:z[0])
        out['experiments'].append(dict(**info,kernel=[[str(x) for x in row] for row in E],numerical_deficiency=value,exact_upper=str(upper),exact_upper_float=float(upper),decoder=[[str(x) for x in row] for row in D],denominator_limit=den,dual_alpha=wit['dual_alpha'].tolist(),dual_b=wit['dual_b'].tolist()))
        if info['id']%50==0:print(json.dumps(dict(done=info['id']+1,max_deficiency=max(r['numerical_deficiency'] for r in out['experiments']),max_exact_upper=max(r['exact_upper_float'] for r in out['experiments']),seconds=time.monotonic()-start)),flush=True)
    out['status']='passed_enumeration_and_exact_feasibility';out['elapsed_seconds']=time.monotonic()-start
    out['maximum_numerical_deficiency']=max(x['numerical_deficiency'] for x in out['experiments'])
    out['maximum_exact_upper']=str(max(Q(x['exact_upper']) for x in out['experiments']))
    out['above_candidate']=[x['id'] for x in out['experiments'] if Q(x['exact_upper'])>Q(9,125)]
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('terminal_histories','plan_leafsets','plan_to_experiment','experiments','failures')}))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',default='enumerated_plans.json');main(ap.parse_args())
