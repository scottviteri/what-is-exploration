#!/usr/bin/env python3
"""Compare complete purpose envelopes and explicit native transfer certificates.

A pooled saved-policy error is a lower bound on a numerically enlarged worst-target envelope. It is
never labeled its optimum. The affine coupling bounds are exact-feasible
certificates; triangle-baseline constants below use independently checked
float64 decoder LPs. No source-global sharpness is asserted.
"""
from pathlib import Path
from fractions import Fraction
from itertools import product
import argparse, csv, hashlib, json
import numpy as np
import audit

HERE=Path(__file__).resolve().parent
NOISES=((.1,.1),(.25,.25),(.1,.3))
WORDS=('LR','LLL','RRR','LLR','LRR','adaptive_L')
SUMS=tuple(k for k in audit.LIBRARIES if k!='native_minimax')

def digest(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def key_noise(noise): return ','.join(str(float(e)) for e in noise)
def exact_float(s): return float(Fraction(s))

def geometry():
    checks=audit.Checks(); rows={}
    for noise in NOISES:
        targets={k:audit.target_kernel(k,noise) for k in audit.TARGETS}
        null=np.ones((4,1))
        constants={t:audit.decoder_deficiency(null,targets[t],checks) for t in WORDS}
        contraction={t:max(float(np.abs(a-b).sum()/2) for a in targets[t] for b in targets[t]) for t in WORDS}
        single={j:{t:audit.decoder_deficiency(targets[j],targets[t],checks) for t in WORDS}
                for j in audit.WEIGHTS}
        mixture={}
        for name,library in audit.LIBRARIES.items():
            weights=np.array([audit.WEIGHTS[j] for j in library]); W=float(sum(weights))
            E=np.concatenate([targets[j]*(w/W) for j,w in zip(library,weights)],axis=1)
            mixture[name]={t:audit.decoder_deficiency(E,targets[t],checks) for t in WORDS}
        rows[key_noise(noise)]=dict(null=constants,single=single,mixture=mixture,contraction=contraction)
    out=dict(scope='Classical source-to-target triangle baselines, independent float64 decoder LPs.',
             rows=rows,decoder_lps=checks.decoder_lps,max_residuals=checks.errors,
             audit_source_sha256=digest(HERE/'audit.py'))
    (HERE/'transfer_geometry.json').write_text(json.dumps(out,indent=2)+'\n')
    return out

def native_cost(row,objective):
    d=row['target_deficiencies']; keys=audit.LIBRARIES[objective]
    return max(d[k] for k in keys) if objective=='native_minimax' else sum(audit.WEIGHTS[k]*d[k] for k in keys)

def guarantee(noise,objective,budget,word,geo,certs):
    g=geo['rows'][key_noise(noise)]; library=audit.LIBRARIES[objective]
    maxloss=objective=='native_minimax'; W=sum(audit.WEIGHTS[k] for k in library)
    singles=min((budget if maxloss else budget/audit.WEIGHTS[j])+g['single'][j][word] for j in library)
    mix=(budget if maxloss else budget/W)+g['mixture'][objective][word]
    triangle=min(g['null'][word],singles,mix)
    candidates=[]
    for cert in certs:
        if tuple(exact_float(e) for e in cert['eps'])!=tuple(noise): continue
        if cert['word']!=('adaptive' if word=='adaptive_L' else word): continue
        source=cert['diagnostic_source']
        if source=='majority3' and not all(k in library for k in ('LLL','RRR')): continue
        denominator=.4 if source=='singles' else .2
        s=budget if maxloss else budget/denominator
        v=exact_float(cert['intercept'])+exact_float(cert['slope'])*s
        candidates.append((v,source,cert['intercept'],cert['slope'],s))
    coupling=min(candidates)
    union_candidates=[sum(noise)+(2*budget if maxloss else 5*budget)]
    if all(k in library for k in ('LLL','RRR')):
        e3=sum(3*e*e-2*e**3 for e in noise)
        union_candidates.append(e3+(2*budget if maxloss else 10*budget))
    union=min(g['null'][word],g['contraction'][word]*min(1.,*union_candidates))
    options={'ignore_record':g['null'][word],'triangle':triangle,'world_reconstruction':union,'coupling':coupling[0]}
    method=min(options,key=options.get)
    return dict(guaranteed_upper=min(options.values()),best_method=method,
                null_error=g['null'][word],triangle_upper=triangle,world_reconstruction_upper=union,
                coupling_upper=coupling[0],coupling_diagnostics=coupling[1],
                coupling_intercept=coupling[2],coupling_slope=coupling[3],
                diagnostic_average_bound=coupling[4],native_loss_bound=budget)

def coverage(data):
    actual_opt={(r['H'],tuple(r['noise']),r['objective'],r['planning_q']) for r in data['optima']}
    actual=set()
    for r in data['rows']:
        token=('absolute',round(r['eta'],10)) if r['fraction'] is None else ('fraction',r['fraction'])
        actual.add((r['H'],tuple(r['noise']),r['objective'],r['planning_q'],r['purpose'],token))
    expected_opt=set();expected=set()
    specs=[(name,q) for name in ('information','quadratic') for q in (.5,.01)]
    specs += [(name,None) for name in audit.LIBRARIES]
    for H,noise,(name,q) in product((3,4),NOISES,specs):
        expected_opt.add((H,noise,name,q))
        for purpose,f in product(('U','V','world','U_asymmetric','parity'),(0.,.01,.05)):
            expected.add((H,noise,name,q,purpose,('fraction',f)))
        if name in SUMS:
            for purpose in ('U','V','world','U_asymmetric','parity'):
                expected.add((H,noise,name,q,purpose,('absolute',.005)))
    return dict(expected_optima=len(expected_opt),actual_optima=len(actual_opt),
                expected_envelopes=len(expected),actual_envelopes=len(actual),
                missing_optima=len(expected_opt-actual_opt),missing_envelopes=len(expected-actual),
                unexpected_optima=len(actual_opt-expected_opt),unexpected_envelopes=len(actual-expected),
                full_protocol_coverage=(actual_opt==expected_opt and actual==expected))

def run(paths):
    certpath=HERE/'theory/certificates.json'; certdata=json.loads(certpath.read_text())
    assert certdata['all_exact_checks_pass']
    geo=geometry(); data={'optima':[],'rows':[]}; inputs=[]
    for path in paths:
        d=json.loads(path.read_text())
        if d['status']!='passed_requested_stage': raise ValueError((path,d['status']))
        assert d['protocol_sha256']==digest(HERE/'PROTOCOL.md')
        assert d['source_sha256']==digest(HERE/'compute.py')
        assert not d['failures']
        for kind in data:
            for old in d[kind]:
                r=dict(old);r['results_path']=str(path.relative_to(HERE));data[kind].append(r)
        inputs.append(dict(path=str(path.relative_to(HERE)),sha256=digest(path),
                           status=d['status'],run_seconds=d['run_seconds'],counts=d['counts']))
    assert len({r['id'] for r in data['rows']})==len(data['rows'])
    opts={r['id']:r for r in data['optima']}
    allpol=data['optima']+data['rows']; pools={}
    for r in allpol: pools.setdefault((r['H'],tuple(r['noise'])),[]).append(r)
    bound_rows=[]; seen=set()
    for r in data['rows']:
        if not r['objective'].startswith('native_'): continue
        tag=(r['optimum_id'],r['fraction'],r['eta'])
        if tag in seen: continue
        seen.add(tag);opt=opts[r['optimum_id']]
        # Use the feasible primal optimum value as an upper bound on the true
        # loss optimum; LP endpoint errors remain separately reported numerical evidence.
        base_budget=max(0.,opt['actual_cost'])+r['eta']
        # The same explicitly enlarged set is used for lower witnesses and
        # upper guarantees. At eta=0 its membership is numerical, not an
        # exact mathematical optimum certificate.
        eligibility_tolerance=5e-8
        budget=base_budget+eligibility_tolerance
        eligible=[p for p in pools[(r['H'],tuple(r['noise']))]
                  if native_cost(p,r['objective'])<=budget]
        assert eligible
        for word in WORDS:
            bound=guarantee(tuple(r['noise']),r['objective'],budget,word,geo,certdata['certificates'])
            worst=max(eligible,key=lambda p:p['target_deficiencies'][word])
            observed=worst['target_deficiencies'][word]
            assert observed<=bound['guaranteed_upper']+2e-7,(r['id'],word,observed,bound)
            bound_rows.append(dict(H=r['H'],noise=r['noise'],objective=r['objective'],
                fraction=r['fraction'],eta=r['eta'],normalization=r['normalization_name'],
                target=word,held_out=word in ('LLR','LRR','adaptive_L'),
                witnessed_lower=observed,witness_id=worst['id'],eligible_saved_policies=len(eligible),
                lower_witness_scope='numerically enlarged cost sublevel; not an exact eta-optimality assertion',
                optimum_lower=opt['dual_value'],optimum_upper=opt['actual_cost'],
                eligibility_tolerance=eligibility_tolerance,witness_native_cost=native_cost(worst,r['objective']),
                witness_gap_upper=native_cost(worst,r['objective'])-opt['dual_value'],**bound))
    fields=['H','e_L','e_R','objective','planning_q','purpose','fraction','eta',
            'normalization','guaranteed_value','purpose_best','purpose_loss','id']
    with (HERE/'envelopes.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=fields);writer.writeheader()
        for r in data['rows']:
            writer.writerow(dict(H=r['H'],e_L=r['noise'][0],e_R=r['noise'][1],
                objective=r['objective'],planning_q=r['planning_q'],purpose=r['purpose'],
                fraction=r['fraction'],eta=r['eta'],normalization=r['normalization_name'],
                guaranteed_value=r['purpose_value'],purpose_best=r['purpose_benchmarks'][r['purpose']],
                purpose_loss=r['purpose_loss'],id=r['id']))
    with (HERE/'transfer_bounds.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(bound_rows[0]));writer.writeheader();writer.writerows(bound_rows)
    cov=coverage(data)
    assert cov['full_protocol_coverage'],cov
    summary=dict(scope='Complete finite-purpose envelopes; certified transfer upper bounds; pooled saved-policy target errors are lower witnesses for the explicitly numerically enlarged cost sublevel only.',
        coverage=cov,inputs=inputs,protocol_sha256=digest(HERE/'PROTOCOL.md'),
        exact_certificate_sha256=digest(certpath),transfer_entries=len(bound_rows),
        heldout_nonvacuous=sum(r['held_out'] and r['guaranteed_upper']<r['null_error']-1e-8 for r in bound_rows),
        coupling_beats_triangle=sum(r['held_out'] and r['coupling_upper']<r['triangle_upper']-1e-8 for r in bound_rows),
        minimum_bound_slack=min(r['guaranteed_upper']-r['witnessed_lower'] for r in bound_rows),
        headline_purposes=[r for r in data['rows'] if r['H']==4 and r['noise']==[.1,.1]
                          and r['fraction'] in (0.,.01) and r['purpose'] in ('U','V','world','parity')],
        headline_bounds=[r for r in bound_rows if r['H']==4 and r['noise']==[.1,.1]
                         and r['fraction'] in (0.,.01) and r['target'] in ('LR','LLR','adaptive_L')])
    (HERE/'analysis.json').write_text(json.dumps(summary,indent=2)+'\n')
    plot(data['rows'])
    print(json.dumps({k:v for k,v in summary.items() if not k.startswith('headline')},indent=2))

def plot(rows):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    names={'information':'Information','quadratic':'Quadratic','native_singles':'Singles',
           'native_joint':'+ joint','native_repeats':'+ repeats','native_minimax':'Minimax'}
    colors=['#222222','#777777','#ae523c','#2d7991','#5e853f','#9573a6']
    fig,axs=plt.subplots(2,3,figsize=(10.2,6),sharex=True)
    for i,q in enumerate((.5,.01)):
        for j,purpose in enumerate(('U','world','parity')):
            ax=axs[i,j]
            for (objective,label),color in zip(names.items(),colors):
                rr=sorted([r for r in rows if r['H']==4 and r['noise']==[.1,.1]
                           and r['objective']==objective and r['purpose']==purpose and r['fraction'] is not None
                           and (r['planning_q']==q or r['planning_q'] is None)],key=lambda r:r['fraction'])
                if rr: ax.plot([100*r['fraction'] for r in rr],[r['purpose_value'] for r in rr],
                               marker='o',markersize=3,lw=1.3,label=label,color=color)
            ax.set_title({'U':'Guess U','world':'Guess both bits','parity':'Guess parity'}[purpose],fontsize=10)
            if j==0:ax.set_ylabel('Guaranteed accuracy\nPlanning q='+str(q))
            if i==1:ax.set_xlabel('Allowed return gap (% of range)')
            ax.grid(axis='y',alpha=.18);ax.spines[['top','right']].set_visible(False)
            ax.set_xticks([0,1,5])
    handles,labels=axs[0,0].get_legend_handles_labels()
    fig.legend(handles,labels,loc='upper center',ncol=6,frameon=False,fontsize=9)
    fig.subplots_adjust(top=.9,bottom=.13,hspace=.42,wspace=.27)
    fig.savefig(HERE/'purpose_envelopes.pdf',bbox_inches='tight')
    fig.savefig(HERE/'purpose_envelopes.png',dpi=160,bbox_inches='tight')
    plt.close(fig)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--geometry-only',action='store_true')
    ap.add_argument('--inputs',type=Path,nargs='+',default=[HERE/'results/results.json',HERE/'results_h4/results.json'])
    args=ap.parse_args()
    if args.geometry_only:
        g=geometry();print(json.dumps({'decoder_lps':g['decoder_lps'],'max_residuals':g['max_residuals']},indent=2))
    else:run([p.resolve() for p in args.inputs])
