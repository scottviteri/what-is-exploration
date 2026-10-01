#!/usr/bin/env python3
"""Emit one illustrative objective/cut plan and a future protocol manifest. Never solve."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import sys
from adaptive_weights import (Context, RationalTarget, TargetBinding, Objective,
    CutCache, digest, canonical, background_id)
from frozen_adapter import verify_lock, prepare_master
from weight_updates import tractability_weights, hard_target_update

HERE = Path(__file__).resolve().parent


def make_plan():
    lock = verify_lock()
    # Synthetic hashes are labels only. No empirical model or native loss is asserted.
    context = Context(digest('synthetic-model'),digest('synthetic-geometry'),
                      digest(['world-0','world-1']),1,2)
    encodings = [RationalTarget(2,2,1,1,r) for r in range(2)]
    encodings += [RationalTarget(2,2,1,2,1)]
    targets = [TargetBinding(e.key,digest({'synthetic-kernel':e.key})) for e in encodings]
    start = [F(1,3)]*3
    cheap = tractability_weights(start,[1,3,8],2)
    hard, update_note = hard_target_update(start,[(F(1,10),F(1,5)),(F(2,5),F(1,2)),(F(0),F(1,10))],F(1,2))
    objectives = {}
    cache = CutCache(context)
    for label, v in [('fixed',start),('tractability',cheap),('hard-target',hard)]:
        objective = Objective.rich(context,targets,encodings,
            {e.key:p for e,p in zip(encodings,v)},F(1,20))
        objectives[label] = {'objective':objective.manifest(),'master':prepare_master(cache,objective)}
    # Unseen candidate seeds are a proposal, not a claim of audit against every archive.
    models = [{'worlds':q,'hidden_states':3,'concentration':a,'model_seed':seed}
              for q in (4,8) for a in ('0.2','1','5') for seed in (926101,926102)]
    return {'schema':'jw-adaptive-dry-run-v1','execution_enabled':False,
        'synthetic_only':True,'solver_modules_loaded':[],
        'backend_lock':lock,'background_id':background_id(2,2),
        'illustrative_objectives':objectives,'hard_update_arithmetic':update_note,
        'future_model_specifications':models,
        'future_design':{'status':'proposed; not launched or preregistered',
            'train_target_depth':3,'independent_audit_depth':4,
            'collection_horizons':[3,4],'budget_seconds':[2,10,40],
            'emphasis_seeds':[926201,926202,926203],
            'primary_epsilon':'1/20','initial_library_size':16,
            'arms':['fixed','tractability','hard-target','direct-minimax'],
            'baseline_arms':['information','posterior-brier'],
            'favorable_return_regret':['0 with <=1e-10 slack','1 percent','5 percent'],
            'required_before_launch':['resource allocation','new-bridge equivalence checks',
                'randomized native-target compiler checks','reward-face implementation or pinned existing planner',
                'audit-cost feasibility pilot','seed nonoverlap check','freeze source and exact queue'],
            'gates':'Budget tiers or horizon tiers may be reduced by pre-outcome feasibility only'},
        'unsupported':['online trajectory adaptation','reward-face constraints in new bridge',
            'robust background epigraph in new bridge','certified floating MW update error',
            'efficient global hardest-target oracle','eventual regret from a finite gap alone']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    plan = make_plan()
    if any(name in sys.modules for name in ('numpy','scipy','highspy','torch','cupy')):
        raise RuntimeError('Dry run imported a numerical/solver package')
    content = json.dumps(canonical(plan),indent=2,allow_nan=False)+'\n'
    if args.output:
        output = args.output.resolve()
        if output.parent != HERE:
            raise ValueError('Dry-run artifacts must stay in the isolated research directory')
        output.write_text(content)
    else:
        print(content,end='')


if __name__ == '__main__':
    main()
