"""Combine separately provenanced follow-up results; never rewrite the archive."""
from common import *
from collections import Counter,defaultdict
from datetime import datetime,timezone
import copy,csv
TOL=1e-6

def read(p):return json.loads(p.read_text()) if p.exists() else None

def summarize():
    rows={};provenance={};unverified=[]
    original_summary=read(HERE/'original_audit/SUMMARY.json')
    for job in MANIFEST['jobs']:
        cell=job['id'];p=ORIGINAL/'main_results'/cell/'result.json'
        if not p.exists():continue
        r=read(p);cert=read(HERE/'original_audit'/(cell+'.json'))
        if r['status']=='complete' and cert and cert['status']=='passed':
            assert cert['result_sha256']==digest(p)
            rows[cell]=r;provenance[cell]=dict(kind='original_completed',result_path=str(p),result_sha256=digest(p),verification_path=str(HERE/'original_audit'/(cell+'.json')))
    cm=read(HERE/'completion_manifest.json')
    for job in cm['jobs']:
        cell=job['id'];p=HERE/'completion_results'/cell/'result.json';r=read(p)
        if not r or r['status']!='complete':continue
        cert=read(HERE/'completion_audit'/(cell+'.json'))
        if not cert or cert['status']!='passed':unverified.append(cell);continue
        assert cert['result_sha256']==digest(p)
        rows[cell]=r;provenance[cell]=dict(kind='new_registered_completion',result_path=str(p),result_sha256=digest(p),verification_path=str(HERE/'completion_audit'/(cell+'.json')))
    for manifest_name,root_name,kind in [('recovery_manifest.json','recovery_results','recovered_original_policy'),('near_optimal_manifest.json','near_optimal_results','new_heldout_evaluation')]:
        manifest=read(HERE/manifest_name)
        if not manifest:continue
        for job in manifest['jobs']:
            folder=HERE/root_name/job['cell'];r=read(folder/'result.json');check=read(folder/'INDEPENDENT_CHECK.json')
            if not r or r['status']!='complete' or not check or check['status']!='passed':continue
            assert check['result_sha256']==digest(folder/'result.json')
            for item in [job]+job['aliases']:
                cell=item['cell'];original=ORIGINAL/'main_results'/cell
                assert digest(original/'result.json')==item['result_sha256']
                assert digest(original/item['checkpoint']/'policy.npz')==item['policy_sha256']
                with np.load(original/item['checkpoint']/'policy.npz',allow_pickle=False) as z:eh=hashlib.sha256(z['E'].tobytes()).hexdigest()
                assert eh==job['source_array_sha256'] and digest(original/'model.npz')==job['model_sha256']
                rr=read(original/'result.json')
                assert rr['checkpoints'][-1]['status']=='complete'
                rr['held_out_horizon']=dict(n=r['target_horizon'],selection_used=False,policy_checkpoint=item['checkpoint'],audit=r['audit'])
                # This is a derived comparison row. Its original status and the
                # new evaluation/verification sources remain explicit.
                prior=rr['status'];rr['status']='complete'
                rows[cell]=rr;provenance[cell]=dict(kind=kind,original_status=prior,original_result_path=str(original/'result.json'),original_result_sha256=item['result_sha256'],evaluation_path=str(folder/'result.json'),evaluation_sha256=digest(folder/'result.json'),verification_path=str(folder/'INDEPENDENT_CHECK.json'),exact_experiment_alias=cell!=job['cell'])
    groups=defaultdict(list)
    for cell,r in rows.items():
        a=r['arguments'];cp=r['checkpoints'][-1];held=r.get('held_out_horizon',{})
        if a['t']!=3 or a['n']!=3 or held.get('n')!=4 or not held.get('audit',{}).get('exhaustive'):continue
        face=a.get('face_objective','none')
        if face!='none':
            if not cp.get('full_minimax_certified'):continue
            lab=f"face_{face}_{a['regret']:g}"
        elif a['strategy']=='baseline':lab='legacy_'+a['objective'] if a['objective'].startswith('native_') else a['objective']
        elif a['objective']=='native_weighted' and cp['k']==128 and cp.get('full_uniform_mean_certified'):lab='weighted128'
        elif a['objective']=='native_minimax' and cp.get('full_minimax_certified'):lab='minimax'
        else:continue
        au=held['audit'];groups[(r['model_name'],lab)].append(dict(cell=cell,lower=au['lower'],upper=au['upper'],provenance=provenance[cell]))
    cases=[a['case'] if a['case']!='fresh' else f"fresh_hmm_{a['seed']}_q{a['worlds']}_s3_c{a['concentration']}" for a in MANIFEST['cases']]
    methods=['uniform','information','brier','pseudo_count','weighted128','minimax']
    def env(rs):return [min(x['lower'] for x in rs),max(x['upper'] for x in rs)]
    coverage=[];points=[]
    for case in cases:
        coverage.append(dict(case=case,**{m:len(groups.get((case,m),[])) for m in methods}))
        for m in methods:
            if (case,m) in groups:
                rr=groups[(case,m)];lo,hi=env(rr);points.append(dict(case=case,method=m,lower=lo,upper=hi,cells=';'.join(x['cell'] for x in rr)))
    comparisons=[]
    for arm in ['minimax','weighted128']:
        for base in ['information','brier','pseudo_count','legacy_native_weighted']+[f'face_{name}_{regret:g}' for name in ['information','brier'] for regret in [0,.01,.05]]:
            pairs=[]
            for case in cases:
                aa=groups.get((case,arm));bb=groups.get((case,base))
                if not aa or not bb:continue
                x,y=env(aa),env(bb)
                outcome='win' if x[1]<y[0]-TOL else 'loss' if x[0]>y[1]+TOL else 'tie' if max(abs(x[0]-y[1]),abs(x[1]-y[0]))<=TOL else 'mixed'
                pairs.append(dict(case=case,arm_interval=x,baseline_interval=y,outcome=outcome,arm_cells=[r['cell'] for r in aa],baseline_cells=[r['cell'] for r in bb]))
            comparisons.append(dict(arm=arm,baseline=base,cases=len(pairs),counts=dict(Counter(p['outcome'] for p in pairs)),pairs=pairs))
    queues={name:read(HERE/name/'queue.json') for name in ['completion_results','recovery_results','near_optimal_results']}
    queues={name:None if q is None else dict(status=q['status'],counts=dict(Counter(x['status'] for x in q['jobs'])),started_utc=q.get('started_utc'),finished_utc=q.get('finished_utc')) for name,q in queues.items()}
    out=dict(updated_utc=datetime.now(timezone.utc).isoformat(),original_audit=original_summary,completion_audit=read(HERE/'completion_audit/SUMMARY.json'),queues=queues,unverified_completed_jobs=unverified,coverage=coverage,figure_points=points,comparisons=comparisons,provenance=provenance,case_order=cases,methods=methods,interpretation='Numerically checked finite objectives and recorded optimizer representatives; comparisons retain partial coverage, losses and per-result provenance. No eventual J_w or source-fidelity claim for omitted predictive/entropy archives.')
    write(HERE/'COMBINED_STATUS.json',out)
    with (HERE/'combined_figure_data.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=['case','method','lower','upper','cells']);w.writeheader();w.writerows(points)
    lines=['# Follow-up status','',f"Updated {out['updated_utc']}.",'','The original run remains unchanged. This report combines only results with completed saved-certificate or explicit-witness checks.','', '## Execution','']
    for name,q in queues.items():lines.append(f'- {name}: {q}')
    lines+=['',f'Completed jobs awaiting their separate certificate audit: {unverified}.','','## Held-out n=4 comparison (collector t=3)','', '| Native method | Comparator | Cases | Wins / ties / losses / mixed |','|---|---|---:|---|']
    for c in comparisons:
        if c['cases']:lines.append(f"| {c['arm']} | {c['baseline']} | {c['cases']} | "+' / '.join(str(c['counts'].get(x,0)) for x in ['win','tie','loss','mixed'])+' |')
    lines+=['','These are descriptive case counts, with numerical envelopes across available policy representatives. Missing cases are not wins or zero errors. The fixed weighted objective and minimax are finite; changes of selected optimum can affect held-out performance.','', 'COMBINED_STATUS.json retains exact comparison intervals and source/verification paths. Historical predictive/label-entropy results remain in the original archive, outside the current source-aligned figure methods.']
    (HERE/'STATUS.md').write_text('\n'.join(lines)+'\n')
    return out
if __name__=='__main__':
    s=summarize();print(json.dumps(dict(queues=s['queues'],unverified_completed_jobs=s['unverified_completed_jobs'])))
