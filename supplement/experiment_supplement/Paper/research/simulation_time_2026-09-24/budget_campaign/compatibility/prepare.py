from common import *

def main():
    assert not (HERE/'JOBS.json').exists() and not (HERE/'SOURCES.json').exists()
    from io_utils import verify_sources as vp
    parenthash=vp();manifest=json.loads((PARENT/'MANIFEST.json').read_text());refs=json.loads((PARENT/'REFERENCES.json').read_text())
    eligibility=[];jobs=[]
    for cid in range(4):
        case_id=f'case_{cid:02}'
        for t in (3,4,5):
            for method in ('brier','information'):
                phase='reference_replay' if t==3 else f'pilot_h{t}'
                source_id=f'{phase}__{case_id}__{method}';base=PARENT/'results'/source_id
                r=json.loads((base/'result.json').read_text());c=json.loads((base/'CHECK.json').read_text())
                assert c['status']=='passed' and c['result_sha256']==sha(base/'result.json') and r['planning_certified']
                for audit in sorted(r['audits'],key=lambda x:x['reference']):
                    ref=next(x for x in refs['records'] if x['case_id']==case_id and x['method']==audit['reference'])
                    eligible=audit['lower']>.02+1e-9
                    record=dict(primary_id=source_id,reference=audit['reference'],lower=audit['lower'],upper=audit['upper'],eligible=eligible)
                    eligibility.append(record)
                    if not eligible:continue
                    paths=[str((base/'result.json').relative_to(PARENT)),str((base/'CHECK.json').relative_to(PARENT)),str((base/audit['witness']).relative_to(PARENT)),ref['model'],ref['path'],'REFERENCES.json','MANIFEST.json']
                    jobs.append(dict(id=f'{case_id}__t{t}__{method}__to_{audit["reference"]}',case_id=case_id,case=r['spec']['case'],t=t,method=method,epsilon=.02,reference=audit['reference'],reference_path=ref['path'],model=ref['model'],primary_id=source_id,trigger_lower=audit['lower'],input_sha256={p:sha(PARENT/p) for p in paths}))
    assert len(eligibility)==144
    report=dict(created_utc=now(),parent_sources_sha256=parenthash,eligible=len(jobs),included=min(60,len(jobs)),jobs=jobs[:60],excluded_by_cap=jobs[60:],eligibility=eligibility)
    write(HERE/'JOBS.json',report)
    files=['common.py','worker.py','verify.py','prepare.py','validate.py','run.py','PROTOCOL.md','JOBS.json','VALIDATION.json']
    write(HERE/'SOURCES.json',dict(parent_sources_sha256=parenthash,files={p:sha(HERE/p) for p in files}))
    print(json.dumps({k:v for k,v in report.items() if k not in ('jobs','eligibility','excluded_by_cap')}))

if __name__=='__main__':main()
