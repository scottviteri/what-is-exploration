"""Bind completed saved results for paper presentation. No optimization or writes to evidence."""
from pathlib import Path
import json,hashlib,collections
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
B=ROOT/'Paper/research/simulation_time_2026-09-24/budget_campaign'
C=B/'compatibility';bindings={}
def read(path):
    blob=path.read_bytes();bindings[str(path.relative_to(ROOT))]=hashlib.sha256(blob).hexdigest();return json.loads(blob)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def bind(path,expected):
    h=sha(path);assert h==expected,(path,h,expected);bindings[str(path.relative_to(ROOT))]=h
for base in [B,C]:
    s=read(base/'SOURCES.json')
    for name,h in (s if base==B else s['files']).items():bind(base/name,h)
refs=read(B/'REFERENCES.json');old=read(ROOT/'Paper/research/empirical_ending_checks_2026-09-23/COMPLETE_COMPARISON.json')
assert set(refs['cases'])==set(old['cases']);cases=old['cases'];methods=refs['methods'];records=[];failures=[];compat=[]
ps=read(B/'STATUS.json');cs=read(C/'STATUS.json');assert ps['status']==cs['status']=='complete'
for rr in ps['records']:
    folder=B/'results'/rr['id'];r=read(folder/'result.json')
    if rr['status']!='passed':
        assert rr['status']==r['status']=='failed';failures.append(dict(id=rr['id'],case=r['spec']['case'],method=r['spec']['method'],t=r['spec']['t'],error=r['error']));continue
    ck=read(folder/'CHECK.json');assert ck['status']=='passed' and ck['result_sha256']==sha(folder/'result.json')
    assert r['status']=='complete' and r['planning_certified'];bind(folder/'policy.npz',r['policy_sha256'])
    for a in r['audits']:bind(folder/a['witness'],a['witness_sha256'])
    records.append(dict(case=r['spec']['case'],method=r['spec']['method'],t=r['spec']['t'],source=str(folder.relative_to(ROOT)),rewards=r['rewards'],planning=ck['planning'],audits=r['audits']))
assert len(records)==392 and len(failures)==4 and all(x['method']=='uniform' for x in failures)
# The completed correction is an overlay; original timeout records stay intact.
U=B.parent/'uniform_decoder_recovery'
delivery=read(U/'DELIVERY.json');assert delivery['status']=='passed'
for name,item in delivery['files'].items():
    bind(U/name,item['sha256']);assert (U/name).stat().st_size==item['bytes']
us=read(U/'SOURCES.json');assert us['parent_sources_sha256']==sha(B/'SOURCES.json')
for name,h in us['files'].items():bind(U/name,h)
for name,h in read(U/'INPUT_BINDINGS.json').items():bind(ROOT/'Paper'/name,h)
overlay=read(U/'INTEGRATION.json');assert overlay['status']=='passed' and overlay['path_base']=='repository root'
assert len(overlay['records'])==4
assert {(r['case'],r['method'],r['t']) for r in overlay['records']}=={(r['case'],r['method'],r['t']) for r in failures}
for rr in overlay['records']:
    folder=ROOT/rr['source'];r=read(folder/'result.json');ck=read(folder/'CHECK.json')
    bind(folder/'result.json',rr['result_sha256']);bind(folder/'CHECK.json',rr['check_sha256'])
    assert ck['status']=='passed' and ck['result_sha256']==sha(folder/'result.json')
    assert r['status']=='complete' and len(r['audits'])==ck['reference_comparisons']==6
    assert rr['audits']==r['audits'] and rr['rewards']==r['rewards']
    original=B/'results'/folder.name/'result.json';original_result=read(original)
    assert r['policy_sha256']==original_result['policy_sha256']
    bind(folder/'policy.npz',r['policy_sha256'])
    for a in r['audits']:bind(folder/a['witness'],a['witness_sha256'])
    records.append(dict(case=r['spec']['case'],method=r['spec']['method'],t=r['spec']['t'],source=str(folder.relative_to(ROOT)),rewards=r['rewards'],planning=ck['planning'],audits=r['audits']))
lookup={(r['case'],r['method'],r['t']):r for r in records};assert len(lookup)==396
for rr in cs['records']:
    assert rr['status']=='passed';folder=C/'results'/rr['id'];r=read(folder/'result.json');ck=read(folder/'CHECK.json');assert ck['status']=='passed' and ck['result_sha256']==sha(folder/'result.json')
    for name,h in r['files'].items():bind(folder/name,h)
    for name,h in r['job']['input_sha256'].items():bind(B/name,h)
    compat.append(dict(id=rr['id'],case=r['job']['case'],method=r['method'],t=r['t'],reference=r['job']['reference'],source=str(folder.relative_to(ROOT)),**{k:ck[k] for k in ['classification','unconstrained_optimum','constrained_reward_lower','constrained_reward_upper','reward_regret_lower','reward_regret_upper','cap_upper','epsilon']}))
assert len(compat)==34
counts=collections.Counter(x['classification'] for x in compat);assert counts=={'positive_reward_cost':22,'compatible_within_numerical_tolerance':12}
thresholds={}
for eps in [.01,.02,.05]:
    thresholds[str(eps)]={}
    for m in methods:
        thresholds[str(eps)][m]={}
        for t in [3,4,5]:
            rs=[r for r in records if r['method']==m and r['t']==t];success=sum(max(a['upper'] for a in r['audits'])<=eps-1e-9 for r in rs)
            failure=sum(max(a['lower'] for a in r['audits'])>eps+1e-9 for r in rs)
            thresholds[str(eps)][m][str(t)]=dict(success=success,failure=failure,unresolved_boundary=len(rs)-success-failure,checked=len(rs),missing=22-len(rs))
assert all(thresholds[e]['uniform']==overlay['uniform_thresholds'][e] for e in thresholds)
result=dict(status='passed',coverage=overlay['combined_coverage'],original_coverage=overlay['original_coverage'],recovery=str(U.relative_to(ROOT)),scope='Completed budget-specific collectors and separate per-reference reward compatibility. Float64 numerical evidence, not all-optima/exact arithmetic/eventual J_w.',cases=cases,methods=methods,records=records,historical_failures=failures,compatibility=compat,compatibility_counts=dict(counts),thresholds=thresholds)
(HERE/'RESULTS.json').write_text(json.dumps(result,indent=2)+'\n');(HERE/'BINDINGS.json').write_text(json.dumps(bindings,indent=2)+'\n')
print('bound',len(bindings),'files; result SHA256',sha(HERE/'RESULTS.json'))
