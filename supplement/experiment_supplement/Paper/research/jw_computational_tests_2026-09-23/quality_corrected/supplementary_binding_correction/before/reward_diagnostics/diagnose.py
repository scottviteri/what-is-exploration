#!/usr/bin/env python3
"""Post-design scalar diagnostics; no optimizer or new primary selection rule."""
from __future__ import annotations
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[key]='1'
import argparse,collections,csv,datetime,hashlib,json,math,sys
from pathlib import Path
import numpy as np
HERE=Path(__file__).resolve().parent
TOL=2e-7
WEIGHTED=('fixed','tractability','hard')
LABELS={'fixed':'Fixed weights','tractability':'Cost-adaptive weights','hard':'Hard-target weights'}

def require(condition,message):
    if not condition:raise ValueError(message)
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):return json.loads(Path(path).read_text())
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def write_json(path,value):Path(path).write_text(json.dumps(value,indent=2,allow_nan=False)+'\n')
def finite(value):
    try:
      x=float(value);return x if math.isfinite(x) else None
    except (TypeError,ValueError):return None

def exact_E_hash(E):
    E=np.ascontiguousarray(E);h=hashlib.sha256()
    h.update(json.dumps({'shape':E.shape,'dtype':E.dtype.str},sort_keys=True).encode());h.update(b'\0');h.update(E.tobytes());return h.hexdigest()

def rewards(E):
    E=np.asarray(E,dtype=float)
    require(E.ndim==2 and min(E.shape)>0,'Experiment must be a nonempty matrix')
    require(np.isfinite(E).all() and np.min(E)>=0,'Experiment entries must be finite and nonnegative')
    residual=float(np.max(abs(E.sum(1)-1)))
    require(residual<=1e-10,'Experiment rows are not normalized')
    Q=E.shape[0];m=E.mean(0);positive=m>0;active=E[:,positive];mass=m[positive]
    ratio=active/mass;logs=np.zeros_like(ratio);np.log2(ratio,out=logs,where=ratio>0)
    information=float(np.sum(active*logs)/Q)
    posterior=active/(Q*mass);brier=float(np.sum(mass*np.sum(posterior**2,axis=0))-1/Q)
    # Algebraically different posterior/entropy checks are numerical diagnostics.
    posterior_logs=np.zeros_like(posterior);np.log2(posterior,out=posterior_logs,where=posterior>0)
    entropy_information=float(math.log2(Q)+np.sum(mass*np.sum(posterior*posterior_logs,axis=0)))
    joint=active/Q;quadratic_brier=float(np.sum(np.sum(joint**2,axis=0)/mass)-1/Q)
    disagreement=max(abs(information-entropy_information),abs(brier-quadratic_brier))
    require(disagreement<=1e-12,'Independent scalar formulas disagree')
    require(-1e-12<=information<=math.log2(Q)+1e-12 and -1e-12<=brier<=1-1/Q+1e-12,'Scalar reward outside theoretical range')
    return {'information_bits':information,'brier_improvement':brier,'experiment_row_residual':residual,'formula_disagreement':disagreement,'zero_record_columns':int(np.sum(~positive))}

def replay(model,policy):
    """Literal controlled-history replay, without importing planning/audit code."""
    T=np.asarray(model['T']);Z=np.asarray(model['Z']);rows=np.asarray(policy['rows']);E=np.asarray(policy['E']);leaf=np.asarray(policy['leaf'])
    Q,actions,S,S2=T.shape
    require(actions==2 and S==S2 and Z.shape==(Q,2,S,2),'Unexpected physical model shape')
    require(rows.shape==(21,2) and E.shape==(Q,64) and leaf.shape==(64,),'Unexpected length-three policy shape')
    for name,array in [('T',T),('Z',Z),('rows',rows),('E',E),('leaf',leaf)]:
      require(np.isfinite(array).all() and np.min(array)>=0,'Invalid '+name)
    for name,array in [('T',T),('Z',Z),('rows',rows),('E',E)]:require(np.max(abs(array.sum(-1)-1))<=1e-10,'Nonstochastic '+name)
    acquired=np.zeros_like(E,dtype=float);weights=np.zeros(64)
    for column in range(64):
      state=np.zeros((Q,S));state[:,0]=1.;weight=1.;prefix=0
      for depth in range(3):
        digit=(column//4**(2-depth))%4;action,observation=divmod(digit,2)
        weight*=rows[(4**depth-1)//3+prefix,action]
        state=np.asarray([(state[q]@T[q,action])*Z[q,action,:,observation] for q in range(Q)])
        prefix=4*prefix+digit
      acquired[:,column]=weight*state.sum(1);weights[column]=weight
    residual=max(float(np.max(abs(acquired-E))),float(np.max(abs(weights-leaf))))
    require(residual<=1e-10,'Saved E/leaf does not replay from the policy')
    return residual

class Inputs:
    def __init__(self,expected):self.expected=expected;self.used={}
    def checked(self,path):
      path=Path(path).resolve();expected=self.expected.get(str(path))
      require(expected is not None,'Input is not bound by the final primary summary: '+str(path))
      require(path.is_file() and sha(path)==expected,'Frozen input hash mismatch: '+str(path))
      self.used[str(path)]=expected;return path
    def json(self,path):return read(self.checked(path))

def references(study,models,inputs):
    """Use every passing face range consistently; never recompute an optimum."""
    result={};records=[]
    for model in models:
      mid=model['id'];base=study/'runs'/mid/'baseline';checked=inputs.json(base/'PLANNING_CHECK.json')
      for reward in ('information','brier'):
        record={'model':mid,'reward':reward,'status':'unavailable','maximum':None,'minimum':None,'range':None,'sources':[],'issues':[]}
        try:
          require(checked.get('status')=='passed','Baseline replay did not pass')
          meta=inputs.json(base/reward/'policy.json');maximum=finite(meta.get('optimal_reward'))
          require(maximum is not None,'Missing saved baseline DP optimum')
          validation_rows=[r for r in checked.get('rows',[]) if r.get('method')==reward]
          require(len(validation_rows)==1 and abs(validation_rows[0]['optimum']-maximum)<=TOL,'Baseline DP metadata and independent check disagree')
          record.update(maximum=maximum,status='maximum_only');record['sources'].append(str(base/reward/'policy.json'))
          ranges=[]
          for percent in (0,1,5):
            folder=study/'runs'/mid/f'{reward}_face{percent}'
            try:
              check=inputs.json(folder/'PLANNING_CHECK.json')
              require(check.get('status')=='passed','Face replay did not pass')
              face=inputs.json(folder/'metadata.json').get('face') or {}
              values=[finite(face.get(k)) for k in ('maximum','minimum','range')]
              require(face.get('reward')==reward and all(v is not None for v in values),'Missing face reward range')
              high,low,width=values
              require(abs(high-maximum)<=TOL and abs(width-(high-low))<=TOL and width>=-TOL,'Face range and DP maximum disagree')
              ranges.append((low,width));record['sources'].append(str(folder/'metadata.json'))
            except Exception as error:record['issues'].append({'face_percent':percent,'error':repr(error)})
          if ranges:
            require(max(v[0] for v in ranges)-min(v[0] for v in ranges)<=TOL and max(v[1] for v in ranges)-min(v[1] for v in ranges)<=TOL,'Reward-face range records disagree')
            record.update(minimum=ranges[0][0],range=ranges[0][1],status='maximum_and_range')
        except Exception as error:record['issues'].append({'error':repr(error)})
        result[mid,reward]=record;records.append(record)
    return result,records

def csv_write(path,rows):
    fields=list(dict.fromkeys(key for row in rows for key in row))
    with Path(path).open('w',newline='') as handle:
      writer=csv.DictWriter(handle,fieldnames=fields);writer.writeheader()
      for row in rows:writer.writerow({k:json.dumps(v,sort_keys=True) if isinstance(v,(dict,list)) else v for k,v in row.items()})

def collect(summary_path):
    summary_path=Path(summary_path).resolve();summary=read(summary_path);metadata=summary['metadata'];rows=summary['endpoints'];study=Path(metadata['study']).resolve()
    require(metadata.get('status')=='final_snapshot','Wait for a completed primary summary')
    require(metadata.get('planning_state')=='finished' and metadata.get('audit_state')=='finished','Primary work is not finished')
    require(metadata.get('final_input_check',{}).get('status')=='passed' and not metadata.get('summary_input_changes') and not metadata.get('read_errors'),'Primary integrity checks did not pass')
    expected=metadata['input_sha256'];changed=[p for p,h in expected.items() if not Path(p).is_file() or sha(p)!=h]
    require(not changed,'Final primary inputs changed: '+repr(changed))
    inputs=Inputs(expected);inventory=inputs.json(study/'MODELS.json');models=inventory['models'];model_index={m['id']:m for m in models}
    require(len(rows)==metadata['planned_scientific_endpoints'],'Primary endpoint coverage is inconsistent')
    refs,ref_records=references(study,models,inputs);cache={};diagnostics=[]
    for row in rows:
      out={k:row.get(k) for k in ('model','worlds','states','concentration','seed','method','arm','endpoint','budget_seconds','analysis_role','secondary','available_seconds','planning_status','planning_check_status','endpoint_status','comparison_eligible','audit_id','audit_complete','audit_lower','audit_upper','selected_gap','omitted_mass')}
      out.update(policy_path=row['policy_path'],reward_status='unavailable',timely_for_checkpoint=False,information_bits=None,brier_improvement=None,issues=[])
      path=Path(row['policy_path']).resolve();key=(row['model'],str(path))
      if key not in cache:
        value={'reward_status':'unavailable','issues':[]}
        try:
          require(path.is_file(),'Policy was not exported')
          folder=study/'runs'/row['model']/row['arm'];check=inputs.json(folder/'PLANNING_CHECK.json')
          require(check.get('status')=='passed','Independent policy replay did not pass')
          inputs.checked(path);policy_meta=inputs.json(path.with_suffix('.json'));model=model_index[row['model']];model_path=Path(model['path']);model_path=model_path if model_path.is_absolute() else study/model_path
          inputs.checked(model_path);require(sha(model_path)==model['sha256'],'Model inventory hash mismatch')
          with np.load(model_path,allow_pickle=False) as physical,np.load(path,allow_pickle=False) as policy:
            residual=replay(physical,policy);E=np.asarray(policy['E']);scores=rewards(E);ehash=exact_E_hash(E)
          if row.get('exact_E_sha256'):require(ehash==row['exact_E_sha256'],'Primary acquired-experiment binding disagrees')
          value.update(scores,reward_status='computed',policy_sha256=sha(path),exact_E_sha256=ehash,policy_replay_residual=residual,available_seconds=finite(policy_meta.get('available_seconds')))
          reward_name=policy_meta.get('method')
          if reward_name in ('information','brier') and policy_meta.get('reward') is not None:
            computed=scores['information_bits' if reward_name=='information' else 'brier_improvement']
            require(abs(computed-policy_meta['reward'])<=TOL,'Direct baseline reward and saved baseline reward disagree')
        except Exception as error:value.update(reward_status='unavailable',issues=[repr(error)])
        cache[key]=value
      out.update(cache[key]);out['issues']=list(out['issues']);available=out.get('available_seconds');out['timely_for_checkpoint']=available is not None and available<=out['budget_seconds']
      for reward,metric in [('information','information_bits'),('brier','brier_improvement')]:
        reference=refs[out['model'],reward];maximum=reference['maximum'];minimum=reference['minimum'];width=reference['range'];actual=out.get(metric)
        out.update({reward+'_reference_status':reference['status'],reward+'_dp_maximum':maximum,reward+'_dp_minimum':minimum,reward+'_attainable_range':width,reward+'_regret':None,reward+'_normalized_regret':None})
        if out['reward_status']=='computed' and actual is not None and maximum is not None:
          regret=maximum-actual;out[reward+'_regret']=regret
          if regret < -TOL or (minimum is not None and actual < minimum-TOL):out['issues'].append(reward+'_outside_saved_DP_range')
          if width is not None and width>TOL:out[reward+'_normalized_regret']=regret/width
      if out['issues'] and out['reward_status']=='computed':out['reward_status']='computed_with_diagnostic_issue'
      diagnostics.append(out)
    return metadata,diagnostics,ref_records,inputs.used

def table(headers,rows):
    clean=lambda x:str(x).replace('|','\\|').replace('\n',' ')
    return '| '+' | '.join(headers)+' |\n| '+' | '.join(['---']*len(headers))+' |\n'+'\n'.join('| '+' | '.join(clean(x) for x in row)+' |' for row in rows)
def fmt(value):return '—' if value is None else f'{value:.6g}'
def span(values):
    values=[x for x in values if x is not None];return '—' if not values else fmt(min(values))+' to '+fmt(max(values))

def plot(rows,models,out):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    figure,axes=plt.subplots(1,3,figsize=(16,5.3),sharey=True);colors=plt.get_cmap('tab20')
    for ax,method in zip(axes,WEIGHTED):
      missing=[]
      for index,model in enumerate(models):
        candidates=[r for r in rows if r['model']==model['id'] and r['method']==method and r['budget_seconds']==40]
        require(len(candidates)==1,'Expected exactly one primary weighted row per class')
        row=candidates[0];x=row.get('information_regret')
        if row['reward_status']!='computed' or not row['timely_for_checkpoint'] or not row.get('comparison_eligible') or x is None:
          missing.append(f'C{index+1:02d}');continue
        low,high=row['audit_lower'],row['audit_upper'];center=(low+high)/2
        ax.errorbar(max(0.,x),center,yerr=[[center-low],[high-center]],fmt='o',color=colors(index),mfc=colors(index) if row['audit_complete'] else 'white',capsize=2,ms=5)
        ax.annotate(f'{index+1:02d}',(max(0.,x),center),xytext=(3,3),textcoords='offset points',fontsize=7,color=colors(index))
      ax.set_title(LABELS[method]);ax.set_xlabel('Information regret to saved DP optimum (bits)');ax.grid(alpha=.2)
      if missing:ax.text(.01,-.23,'Missing: '+', '.join(missing),transform=ax.transAxes,fontsize=7,wrap=True)
    axes[0].set_ylabel('Held-out depth-4 deficiency (numerical bounds; lower is better)')
    figure.suptitle('Post-design diagnostic: 40-second primary weighted policies\nEvery fixed model class retained; point centers are only display locations',fontsize=12)
    figure.tight_layout(rect=(0,.08,1,.9))
    for suffix in ('pdf','png'):figure.savefig(out/f'information_regret_vs_native_deficiency.{suffix}',dpi=170,bbox_inches='tight')
    plt.close(figure)

def report(metadata,rows,reference_rows,figures):
    counts=collections.Counter(r['reward_status'] for r in rows);methods=list(dict.fromkeys(r['method'] for r in rows));body=[]
    for budget in metadata['budgets']:
      for method in methods:
        selected=[r for r in rows if r['method']==method and r['budget_seconds']==budget];good=[r for r in selected if r['reward_status']=='computed' and r['timely_for_checkpoint']]
        body.append([budget,method,f'{len(good)}/{len(selected)}',span([r['information_bits'] for r in good]),span([r['information_regret'] for r in good]),span([r['brier_improvement'] for r in good]),span([r['brier_regret'] for r in good])])
    failures=[r for r in rows if r['reward_status']!='computed' or not r['timely_for_checkpoint']]
    failtext=table(['Model','Method','Budget','Status','Timely','Issues'],[[r['model'],r['method'],r['budget_seconds'],r['reward_status'],r['timely_for_checkpoint'],r['issues']] for r in failures]) if failures else 'Every expected endpoint has a timely validated scalar diagnostic.'
    classes=table(['Plot ID','Model class'],[[f'C{i+1:02d}',m['id']] for i,m in enumerate(metadata['models'])])
    return f'''# Post-design scalar reward diagnostic

These are secondary diagnostics of the completed primary policies, not new primary
metrics or a basis for selecting methods, targets, seeds, checkpoints or policies.
All {len(rows)} expected endpoint rows are retained. Status counts: `{dict(counts)}`.
Uniform-prior world information is in bits. Brier improvement uses categorical
squared loss for the world label, as defined in [the diagnostic protocol](../PROTOCOL.md).

The reported DP maxima and attainable ranges are existing independently checked
length-three records. This script performs no optimization. Regret is maximum
minus actual reward; normalized regret in the CSV divides by the existing
attainable range when it exceeds the numerical tolerance `2e-7`. Tiny floating-point negative residuals remain visible in the
CSV. These values are numerical diagnostics, not exact arithmetic certificates.

## Every method and checkpoint

Each range below describes the listed fixed model classes with timely validated
policies. Counts show the full denominator, including missing or rejected rows.
Baseline successes and native-method losses are retained. Baseline reuses across
budgets and secondary realization averages are identified in the CSV. Repeated
budgets and coupled settings are not independent samples; there are only two
independent seed families. No significance or population inference is made.

{table(['Seconds','Method','Timely / expected','Information bits','Information regret','Brier improvement','Brier regret'],body)}

## Scalar tradeoffs and native capability

The optional plot shows all twelve classes for the three primary weighted
methods at 40 seconds. Lower information regret and lower native deficiency are
both favorable. Error bars are native-audit bounds, not statistical confidence
intervals; point centers are for display only. A policy lacking a native audit
can still have a valid scalar diagnostic in the CSV, but cannot enter the plot.
Missing plot classes are named, not silently dropped.

{('[PDF plot](information_regret_vs_native_deficiency.pdf) · [PNG plot](information_regret_vs_native_deficiency.png)' if figures else 'Plot generation was disabled.')}

{classes}

A scalar reward win does not establish a world-independent decoder, Blackwell
dominance, or strict native-process dominance. Data processing constrains a known
garbling; one information or Brier comparison does not establish that relation.
These finite supplied-model diagnostics also do not prove eventual exploration,
unknown-model learning, or efficient optimization of the complete native score.

## Coverage and failures

{failtext}

[DIAGNOSTICS.csv](DIAGNOSTICS.csv) contains every endpoint, actual reward, saved
DP maximum/minimum, raw and normalized regret, native interval, timing and checks.
[REFERENCES.csv](REFERENCES.csv) preserves all available saved reward-range
records and any missing or inconsistent references. [SUMMARY.json](SUMMARY.json)
contains the complete machine-readable result and input hashes. All source/input
integrity failures abort confirmation aggregation rather than silently choosing
usable outcomes.
'''

def self_test():
    examples=[(np.array([[1.,0.],[1.,0.]]),0.,0.),(np.eye(2),1.,.5),(np.eye(4),2.,.75),(np.array([[.4,0.,.6],[0.,.4,.6]]),.4,.2)]
    entropy=lambda p:-p*math.log2(p)-(1-p)*math.log2(1-p)
    examples.append((np.array([[.75,.25],[.25,.75]]),1-entropy(.25),.125))
    for E,information,brier in examples:
      actual=rewards(E);assert abs(actual['information_bits']-information)<1e-12 and abs(actual['brier_improvement']-brier)<1e-12
      split=np.repeat(E/2,2,axis=1);assert abs(rewards(split)['information_bits']-information)<1e-12 and abs(rewards(split)['brier_improvement']-brier)<1e-12
    assert rewards(np.array([[1.],[1.]]))['information_bits']==0
    T=np.ones((2,2,1,1));Z=np.zeros((2,2,1,2));Z[0,:,:,0]=1.;Z[1,:,:,1]=1.;rows=np.full((21,2),.5);E=np.zeros((2,64))
    for column in range(64):
      observations=[(column//4**k)%2 for k in (2,1,0)]
      for q in (0,1):
        if observations==[q]*3:E[q,column]=1/8
    assert replay({'T':T,'Z':Z},{'rows':rows,'E':E,'leaf':np.full(64,1/8)})==0
    assert rewards(E)['information_bits']==1 and rewards(E)['brier_improvement']==.5
    synthetic={'model':'synthetic','method':'fixed','budget_seconds':40,'reward_status':'computed','timely_for_checkpoint':True,'information_bits':.4,'information_regret':.6,'brier_improvement':.2,'brier_regret':.3,'issues':[]}
    rendered=report({'budgets':[2,10,40],'models':[{'id':'synthetic'}]},[synthetic],[],False)
    assert 'Post-design' in rendered and 'synthetic' in rendered and '0.6' in rendered
    print('Analytic scalar formulas, zero columns, split records, synthetic causal replay and report schema passed; no confirmation results read.')

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--summary',type=Path);parser.add_argument('--output',type=Path,default=HERE/'results');parser.add_argument('--no-plots',action='store_true');parser.add_argument('--self-test',action='store_true');args=parser.parse_args()
    if args.self_test:self_test();return
    if args.summary is None:parser.error('--summary is required after the primary summary finishes')
    output=args.output.resolve();require(output.is_relative_to(HERE),'Diagnostic output must remain inside reward_diagnostics/')
    require(not output.exists() or not any(output.iterdir()),'Use a new output directory; existing diagnostics are preserved')
    summary_path=args.summary.resolve();summary_hash=sha(summary_path);metadata,rows,reference_rows,used=collect(summary_path)
    require(sha(summary_path)==summary_hash,'Primary summary changed during diagnostic collection')
    require(all(Path(p).is_file() and sha(p)==h for p,h in used.items()),'Diagnostic inputs changed during collection')
    output.mkdir(parents=True,exist_ok=True)
    if not args.no_plots:plot(rows,metadata['models'],output)
    csv_write(output/'DIAGNOSTICS.csv',rows);csv_write(output/'REFERENCES.csv',reference_rows)
    doc={'created_utc':now(),'scope':'Post-design scalar diagnostic; not a primary selection metric; no optimization performed','primary_summary':str(summary_path),'primary_summary_sha256':summary_hash,'source_sha256':{str(Path(__file__).resolve()):sha(__file__),str(HERE/'PROTOCOL.md'):sha(HERE/'PROTOCOL.md')},'input_sha256':used,'row_count':len(rows),'status_counts':dict(collections.Counter(r['reward_status'] for r in rows)),'endpoints':rows,'reward_references':reference_rows}
    write_json(output/'SUMMARY.json',doc);(output/'REPORT.md').write_text(report(metadata,rows,reference_rows,not args.no_plots))
    write_json(output/'FILES.json',{str(p.relative_to(output)):sha(p) for p in output.rglob('*') if p.is_file() and p.name!='FILES.json'})
    print(json.dumps({'output':str(output),'rows':len(rows),'status_counts':doc['status_counts']},indent=2))
if __name__=='__main__':main()
