"""Replay saved pilot evidence without solving an optimization problem."""
import hashlib,json,os,sys,time
from collections import Counter
from datetime import datetime,timezone
from pathlib import Path
from types import SimpleNamespace
import numpy as np
import scaling_core as c
from scale_one import action_weights
from extra_objectives import fixed_history_scores
HERE=Path(__file__).resolve().parent
ROOT=HERE/'pilot_results'
checks=[]
def check(name,value,tolerance=c.TOL):
    value=float(value)
    if not np.isfinite(value) or value>tolerance:raise AssertionError((name,value,tolerance))
    checks.append(dict(name=name,error=value,tolerance=tolerance))
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
manifest=json.loads((HERE/'pilot_manifest.json').read_text())
queue=json.loads((ROOT/'queue.json').read_text())
assert queue['status']=='finished' and len(queue['jobs'])==len(manifest['jobs'])==8
for name,digest in manifest['source_sha256'].items():
    assert sha(ROOT/'source'/(digest+'_'+Path(name).name))==digest
rows=[];profiles=0;certificates=0;witnesses=0

def replay_audit(folder,prefix,E,T,Z,n,report):
    global profiles,witnesses
    targets=c.Targets(T,Z,n)
    with np.load(folder/(prefix+'_profile.npz')) as data:
        ids=data['indices'];lower=data['lower'];upper=data['upper']
        assert np.array_equal(ids,np.arange(targets.count))
        assert report['exhaustive'] and report['evaluated']==targets.count
        assert np.isfinite(lower).all() and np.isfinite(upper).all()
        check('per-target bracket',np.max(upper-lower));check('per-target ordering',np.max(lower-upper))
        check('aggregate upper',abs(upper.max()-report['upper']),1e-14)
        check('aggregate lower',abs(lower.max()-report['lower']),1e-14)
        check('aggregate mean',abs(upper.mean()-report['mean_upper']),1e-14)
        profiles+=len(ids)
    with np.load(folder/(prefix+'_witness.npz')) as w:
        assert str(w['source_sha256'])==hashlib.sha256(np.ascontiguousarray(E).tobytes()).hexdigest()
        target=int(w['target_index']);F=targets.get(target)['kernel']
        check('literal hardest target',abs(F-w['target_kernel']).max(),1e-14)
        for stem,target_kernel,expected in [('',F,report['upper']),('revelation_',np.eye(E.shape[0]),report['full_revelation_upper'])]:
            indices=w[stem+'source_indices'];G=w[stem+'decoder'];a=w[stem+'alpha'];b=w[stem+'b'];source=E[:,indices]
            assert np.array_equal(indices,np.flatnonzero(E.max(axis=0)>0))
            check('decoder normalization',abs(G.sum(1)-1).max());check('decoder nonnegative',max(0.,-G.min()),0.)
            check('dual prior normalization',abs(a.sum()-1));check('dual nonnegative',max(0.,-a.min(),-b.min()),0.)
            check('dual bounded loss',max(0.,(b-a[:,None]).max()),1e-15)
            upper=float(abs(source@G-target_kernel).sum(1).max()/2)
            lower=float(np.sum(target_kernel*b)-np.max(source.T@b,axis=1).sum())
            check('witness upper replay',abs(upper-expected),1e-12)
            check('witness bracket',upper-lower);check('witness lower ordering',lower-upper)
            witnesses+=1

for job in manifest['jobs']:
    cell=ROOT/job['id'];r=json.loads((cell/'result.json').read_text());args=r['arguments']
    assert r['manifest_sha256']==sha(HERE/'pilot_manifest.json')
    assert r['job_sha256']==hashlib.sha256(json.dumps(job,sort_keys=True).encode()).hexdigest()
    with np.load(cell/'model.npz') as m:T=m['T'].copy();Z=m['Z'].copy()
    g=c.geometry(T,Z,args['t']);targets=c.Targets(T,Z,args['n'])
    for cp in r['checkpoints']:
        assert cp['status']=='complete'
        folder=cell/f"checkpoint_{cp['k']:03d}"
        with np.load(folder/'policy.npz') as data:E=data['E'].copy();policy=data['rows'].copy();leaf=data['leaf'].copy()
        Er,pr,lr=c.replay(g,action_weights(g,policy))
        # Action rows at unreachable histories may differ without changing the policy experiment.
        check('collector realization replay',max(abs(E-Er).max(),abs(leaf-lr).max()))
        check('collector action rows normalized',abs(policy.sum(1)-1).max())
        check('collector action rows nonnegative',max(0.,-policy.min()),0.)
        check('raw controlled law to experiment',abs(E-g.raw*leaf).max(),1e-12)
        constraint=None
        if cp['reward_face']:
            face=cp['reward_face'];coeff=g.raw.mean(0)*fixed_history_scores(g)[face['objective']]
            value=float(leaf@coeff);constraint=(coeff,face['threshold'])
            check('actual reward constraint',max(0.,face['threshold']-value),0.)
            check('actual objective regret',abs(face['optimum']-value-cp['actual_reward_gap']),1e-14)
        replay_audit(folder,'audit',E,T,Z,args['n'],cp['audit'])
        certificate=folder/'master_certificate.npz'
        if certificate.exists():
            with np.load(certificate) as data:saved={k:data[k].copy() for k in data.files}
            original=c.solve_arrays
            def verify(cost,Ae,be,Au,bu,bounds,method,time_limit):
                for key,matrix in [('A_eq',Ae),('A_ub',Au)]:
                    assert hashlib.sha256(matrix.data.tobytes()+matrix.indices.tobytes()+matrix.indptr.tobytes()).hexdigest()==str(saved[key+'_sha256'])
                check('master objective reconstruction',np.max(abs(cost-saved['cost'])),0.)
                check('master bounds reconstruction',np.max(abs(np.asarray(bounds)-saved['bounds'])),0.)
                sol=SimpleNamespace(x=saved['solution'],fun=float(saved['objective']),nit=0,
                    eqlin=SimpleNamespace(marginals=saved['eq_dual']),ineqlin=SimpleNamespace(marginals=saved['ub_dual']),
                    lower=SimpleNamespace(marginals=saved['lower_dual']),upper=SimpleNamespace(marginals=saved['upper_dual']))
                checked=c.check_solution(np.asarray(cost),Ae,np.asarray(be),Au,np.asarray(bu),saved['bounds'][:,0],saved['bounds'][:,1],sol)
                check('master KKT replay',max(checked['residuals'].values()))
                return sol,checked
            library=c.target_library(T,Z) if args['strategy']=='baseline' else [dict(targets.get(j),weight=1/cp['k']) for j in cp['selected_targets']]
            c.solve_arrays=verify
            try:c.native_plan(g,library,args['objective'],'highs-ipm',1,reward_constraint=constraint,compact_certificate=True)
            finally:c.solve_arrays=original
            certificates+=1
    if 'held_out_horizon' in r:
        held=r['held_out_horizon'];assert not held['selection_used']
        replay_audit(cell/held['policy_checkpoint'],'held_out',E,T,Z,held['n'],held['audit'])
    process=json.loads((cell/'process.json').read_text())
    rows.append(dict(cell=job['id'],status=r['status'],completed_k=[x['k'] for x in r['checkpoints']],
                     wall_seconds=process['seconds'],peak_rss_kib=process['sampled_peak_rss_kib'],
                     failure=r.get('error'),training_seconds=r.get('training_seconds')))

cpu=json.loads((ROOT/'cell_0000/result.json').read_text())
gpu=json.loads((ROOT/'cell_0001/result.json').read_text());parity=[]
for left,right in zip(cpu['checkpoints'],gpu['checkpoints'],strict=True):
    assert left['selected_targets']==right['selected_targets']
    l=left['planning'];r=right['planning']
    difference=abs(l['primal']-r['primal']);check('CPU/GPU selected-objective parity',difference)
    check('CPU/GPU objective interval compatibility',max(l['dual'],r['dual'])-min(l['primal'],r['primal']))
    parity.append(dict(k=left['k'],cpu_primal=l['primal'],gpu_primal=r['primal'],absolute_difference=difference))
assert Counter(x['status'] for x in rows)=={'complete':7,'failed':1}
assert rows[2]['completed_k']==[8,16,32,64]
assert json.loads((HERE/'VALIDATION.json').read_text())['status']=='passed'
report=dict(reviewed_utc=datetime.now(timezone.utc).isoformat(),launch_authorized_by_checks=True,
            scope='Numerical source snapshot, all accepted policies, complete profile aggregates, hardest/revelation original-source witnesses, reconstructed compact master KKT and paired CPU/GPU objective checks. Not exact arithmetic or a theorem.',
            pilot_manifest_sha256=sha(HERE/'pilot_manifest.json'),pilot_rows=rows,checks=len(checks),
            reconstructed_master_certificates=certificates,original_source_witnesses=witnesses,
            checked_profile_entries=profiles,cpu_gpu_parity=parity,max_check_error=max(x['error'] for x in checks),
            bounds_tolerance=c.TOL,main_grid=dict(jobs=1368,primary_jobs=1188,cases=22,hours=8,t3_n3_max_targets=128,t4_n3_max_targets=64,t5_n3_max_targets=16,t3_n4_max_targets=128),
            feasibility_decision='Preserve K128/t4 timeout; cap t4 at64 and t5 at16 by master-size growth, keep n4 and six-step bounded extensions. No ranking-dependent model selection.',
            post_pilot_changes='Original-source validity guards; expanded bounded validation; coverage metadata; timing-based tier caps. Pilot source snapshots unchanged.',
            check_details=checks)
(HERE/'PILOT_REVIEW.json').write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['check_details','pilot_rows','cpu_gpu_parity']},indent=2))
