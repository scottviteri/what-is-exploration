"""Recover only frozen uniform audit failures; never replan or edit the campaign."""
import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
import sys,json,hashlib,shutil,time,resource,traceback,csv
from pathlib import Path
import numpy as np
HERE=Path(__file__).resolve().parent
P=HERE.parent/'budget_campaign';ROOT=HERE.parents[2]
sys.dont_write_bytecode=True
sys.path.insert(0,str(P));sys.path.insert(0,str(P/'deps'))
import io_utils as io
import check as independent
from recovery_decoder import RecoveryDecoder
from known_decoder import KnownDecoderFirst


def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def verify_source():
    d=read(HERE/'SOURCES.json')
    assert io.verify_sources()==d['parent_sources_sha256']
    for name,h in d['files'].items():assert sha(HERE/name)==h,name
    return sha(HERE/'SOURCES.json')


def main():
    os.sched_setaffinity(0,{0});resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,)*2)
    source=verify_source();checkpoint=HERE.parent/'release_checkpoints/2026-09-24_040036'
    status=read(checkpoint/'PRIMARY_STATUS.json');refs=read(P/'REFERENCES.json')['records']
    failed=[r for r in status['records'] if r['status']!='passed']
    assert len(failed)==4 and all(r['method']=='uniform' for r in failed)
    records=[];bindings={};start=time.perf_counter()
    for rr in failed:
        old=P/'results'/rr['id'];out=HERE/'results'/rr['id'];out.mkdir(parents=True,exist_ok=False)
        original=read(old/'result.json');assert original['status']=='failed';r=dict(original)
        r.pop('error',None);r.pop('traceback',None)
        r.update(status='recovering',phase='explicit_decoder_recovery',audits=[],audit_source_sha256=source,
                 recovery_started_utc=io.now(),historical_failure=dict(path=str(old.relative_to(ROOT)),result_sha256=sha(old/'result.json')))
        allrefs=[x for x in refs if x['case_id']==r['spec']['case_id']]
        inputs=[old/'result.json',old/'policy.npz',P/allrefs[0]['model'],P/'REFERENCES.json']+[P/x['path'] for x in allrefs]+[old/a['witness'] for a in original['audits']]
        for path in inputs:bindings[str(path.relative_to(ROOT))]=sha(path)
        shutil.copyfile(old/'policy.npz',out/'policy.npz');assert sha(out/'policy.npz')==original['policy_sha256']
        with np.load(out/'policy.npz') as z:E=z['E'].copy();assert np.max(abs(z['rows']-.5))==0
        t=r['spec']['t'];prefix=np.arange(4**t,dtype=int)//4**(t-3);assert E.shape[1]==len(prefix)
        backend=KnownDecoderFirst(E,64,lambda E,Y:RecoveryDecoder(E,Y,'native-ipm',60.))
        io.write(out/'result.json',r)
        try:
            for ref in allrefs:
                assert sha(P/ref['path'])==ref['sha256']
                prev=next((a for a in original['audits'] if a['reference']==ref['method']),None)
                if prev is not None:
                    path=old/prev['witness'];assert sha(path)==prev['witness_sha256'];shutil.copyfile(path,out/prev['witness'])
                    audit=dict(prev,recovery_method='preserved_original_witness',optimizer_called=False)
                else:
                    with np.load(P/ref['path']) as z:F=z['E'].copy()
                    ts=time.perf_counter();report,w=backend.solve(F,source_to_target=prefix)
                    lo,hi=io.check_witness(E,F,w);path=out/('reference_'+ref['method']+'.npz')
                    io.save(path,E=E,F=F,**w,lower=lo,upper=hi)
                    io.write(out/('decoder_'+ref['method']+'.json'),report)
                    audit=dict(reference=ref['method'],reference_cell=ref['cell'],lower=lo,upper=hi,bracket=hi-lo,
                               classification={str(e):io.classify(lo,hi,e) for e in [.05,.02,.01]},witness=path.name,
                               witness_sha256=sha(path),seconds=time.perf_counter()-ts,coarsening_bound=report.get('coarsening_bound',0.),
                               recovery_method=report['method'],optimizer_called=report['optimizer_called'])
                r['audits'].append(audit);io.write(out/'result.json',r)
                print(rr['id'],ref['method'],audit['recovery_method'],audit['upper'],flush=True)
            assert len(r['audits'])==6
            r.update(status='complete',phase='recovery_awaiting_check',recovery_finished_utc=io.now())
            io.write(out/'result.json',r)
            checked=independent.check(out)
            assert checked['status']=='passed'
            records.append(dict(id=rr['id'],status='passed',case=r['spec']['case'],t=t,method='uniform',
                                path=str(out.relative_to(ROOT)),result_sha256=sha(out/'result.json'),check_sha256=sha(out/'CHECK.json'),
                                original_result_sha256=sha(old/'result.json'),audits=r['audits']))
        except Exception as exc:
            r.update(status='failed',recovery_error=repr(exc),recovery_traceback=traceback.format_exc());io.write(out/'result.json',r)
            records.append(dict(id=rr['id'],status='failed',error=repr(exc),path=str(out.relative_to(ROOT))))
        assert verify_source()==source
        io.write(HERE/'STATUS.json',dict(status='running',completed=len(records),planned=4,records=records))
    for name,h in bindings.items():assert sha(ROOT/name)==h
    successes=sum(r['status']=='passed' for r in records)
    summary=dict(status='complete' if successes==4 else 'incomplete_recovery',source_sha256=source,finished_utc=io.now(),
                 original_passed=392,original_failed=4,recovered=successes,combined_passed=392+successes,
                 combined_comparisons=(392+successes)*6,historical_failures_preserved=4,records=records,
                 seconds=time.perf_counter()-start,scope='Existing uniform policies; explicit decoder shortcut plus unchanged LP fallback and independent full six-reference checks.')
    io.write(HERE/'SUMMARY.json',summary);io.write(HERE/'INPUT_BINDINGS.json',bindings)
    rows=list(csv.DictReader((P/'comparisons.csv').open()))
    for rr in records:
        if rr['status']!='passed':continue
        r=read(ROOT/rr['path']/'result.json')
        for a in r['audits']:
            rows.append(dict(case=r['spec']['case'],method='uniform',t=r['spec']['t'],reference=a['reference'],lower=a['lower'],upper=a['upper'],
                             planning_certified=True,planning_seconds=r['planning_elapsed_seconds'],**{'at_'+k:v for k,v in a['classification'].items()}))
    with (HERE/'comparisons_with_recovery.csv').open('w') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    io.write(HERE/'STATUS.json',summary)
    print(json.dumps({k:v for k,v in summary.items() if k!='records'},indent=2),flush=True)
    if successes!=4:raise SystemExit(1)

if __name__=='__main__':main()
