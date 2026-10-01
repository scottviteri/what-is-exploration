"""Freeze references and the complete staged job list before new optimization."""
from io_utils import *
import shutil
ROOT=HERE.parents[3]
INPUT=ROOT/'Paper/research/empirical_ending_checks_2026-09-23/COMPLETE_REWARDS.json'
PILOT=['sensors_0.1_0.1','delayed_0.1_0.1','irreversible_0.1_0.1','fresh_hmm_2026096800_q4_s3_c0.2']

def prepare():
    assert not (HERE/'REFERENCES.json').exists(),'References are immutable after preparation'
    d=json.loads(INPUT.read_text());bindings=d['input_sha256']|d.get('additional_input_sha256',{})
    selected={}
    for r in sorted(d['records'],key=lambda r:r['cell']):
        if r['method'] in METHODS:selected.setdefault((r['case'],r['method']),r)
    cases=PILOT+sorted(set(d['ranges'])-set(PILOT));refs=[]
    for i,case in enumerate(cases):
        case_id=f'case_{i:02d}';folder=HERE/'references'/case_id;folder.mkdir(parents=True,exist_ok=False)
        arrays=None
        for method in METHODS:
            r=selected[case,method];pp=Path(r['policy']);mp=Path(r['model'])
            assert sha(pp)==bindings[str(pp)] and sha(mp)==bindings[str(mp)]
            with np.load(mp) as z:T=z['T'].copy();Z=z['Z'].copy()
            if arrays is None:arrays=(T,Z);shutil.copy2(mp,folder/'model.npz')
            else:assert np.array_equal(T,arrays[0]) and np.array_equal(Z,arrays[1])
            with np.load(pp) as z:E=z['E'].copy();rows=z['rows'].copy();leaf=z['leaf'].copy()
            actual,w,raw,res=replay(T,Z,3,rows,E,leaf)
            dest=folder/(method+'.npz');shutil.copy2(pp,dest)
            refs.append(dict(case=case,case_id=case_id,method=method,cell=r['cell'],path=str(dest.relative_to(HERE)),sha256=sha(dest),model=str((folder/'model.npz').relative_to(HERE)),model_sha256=sha(folder/'model.npz'),original_policy=str(pp),original_model=str(mp),source_verification=r.get('source_verification'),replay_residual=res,rewards=rewards(E,levels(3)[-1])))
    write(HERE/'REFERENCES.json',dict(status='frozen',created_utc=now(),selection='Lexically first already verified cell per case/method; selection ignores new directed results.',input=str(INPUT),input_sha256=sha(INPUT),cases=cases,methods=METHODS,records=refs))
    jobs=[]
    for phase,cids,ts in [('reference_replay',range(22),[3]),('pilot_h4',range(4),[4]),('pilot_h5',range(4),[5]),('expanded_h4',range(4,22),[4]),('expanded_h5',range(4,22),[5])]:
        for t in ts:
            for i in cids:
                for method in METHODS:
                    jobs.append(dict(id=f'{phase}__case_{i:02d}__{method}',phase=phase,case=cases[i],case_id=f'case_{i:02d}',t=t,method=method,mode='replay' if t==3 else 'plan',planning_seconds=300 if t==4 else 600,job_seconds=1500 if t==4 else 2400))
    write(HERE/'MANIFEST.json',dict(created_utc=now(),authority='the lead author explicitly requested starting the preferred experiments.',references_sha256=sha(HERE/'REFERENCES.json'),methods=METHODS,target_horizon=3,native_target_ids=list(range(128)),epsilons=[.05,.02,.01],planning_gap=2e-7,classification_margin=1e-9,source_budgets=[3,4,5],worker_count=1,cpu=10,address_space_gib=8,wall_seconds=8*3600,disk_reserve_gib=15,output_cap_gib=4,expansion_gate='First complete all reference replays and the four-case h4 pilot. Expand a method to h5 only if all its pilot h4 planning certificates passed. Expanded h4 requires at least one accepted pilot h4 cell for that method; numerical failures remain failures. Expanded h5 requires all four pilot h5 cells certified for that method. Decisions use feasibility/certificates, never relative performance.',compatibility=dict(methods=['information','brier'],epsilon=.02,trigger='Run after the main grid for each pilot case at t=3,4,5 whose selected policy has a checked lower error above .02+1e-9 for a reference; order by case, budget, method, reference. Maximize original reward subject to deficiency <= .02. Never use these favorable policies as primary collectors.',max_jobs=60,seconds_per_job=180),jobs=jobs))
    print('Frozen',len(refs),'references and',len(jobs),'primary jobs')
if __name__=='__main__':prepare()
