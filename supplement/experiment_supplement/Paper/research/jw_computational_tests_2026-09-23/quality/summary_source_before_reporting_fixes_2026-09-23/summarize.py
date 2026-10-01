#!/usr/bin/env python3
"""Aggregate the frozen finite quality queue without optimizing or selecting outcomes.

Run only after planning/auditing: python summarize.py --audits OUT [--output DIR].
Every expected scientific endpoint is retained. Only independently validated,
input-bound intervals enter paired comparisons. Plot midpoints are visual devices,
never estimated objectives or statistical confidence intervals.
"""
from __future__ import annotations
import argparse,collections,csv,datetime,hashlib,json,math,os,re,sys
from fractions import Fraction
from pathlib import Path
HERE=Path(__file__).resolve().parent
BASELINES=('information','brier','uniform')
ADAPTIVE=('tractability','hard')
CORE=('fixed','tractability','hard','minimax')
MARGIN=1e-6
LABELS={'fixed':'Fixed weights','tractability':'Cost-adaptive weights','hard':'Hard-target weights','minimax':'Finite-library minimax','information':'Information gain','brier':'Posterior Brier','uniform':'Uniform actions','tractability_average':'Cost-adaptive average','hard_average':'Hard-target average'}
for _r in ('information','brier'):
 for _p in (0,1,5):LABELS[f'{_r}_face{_p}']=f'{"Information" if _r=="information" else "Brier"} face {_p}%'

def finite(v):
 try:
  x=float(v);return x if math.isfinite(x) else None
 except (TypeError,ValueError):return None

def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def stamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def normpath(p,base):
 p=Path(p);return (p if p.is_absolute() else base/p).resolve()
def fraction_float(v):
 try:return float(Fraction(v))
 except (ValueError,TypeError,ZeroDivisionError):return None

def expected_tail():
 captured=Fraction(128,2**5*2**21)+Fraction(1,2**4*3)+Fraction(1,2**5*3**5)+Fraction(1,2**6*3**21)
 return Fraction(1,20)*(1-captured)

class Snapshot:
 def __init__(self):self.cache={};self.hashes={};self.errors=[]
 def read(self,path,default=None):
  p=Path(path).resolve()
  if p in self.cache:return self.cache[p]
  if not p.exists():return default
  try:
   data=p.read_bytes();self.hashes[str(p)]=hashlib.sha256(data).hexdigest();value=json.loads(data)
  except (OSError,ValueError) as e:self.errors.append({'path':str(p),'error':repr(e)});return default
  self.cache[p]=value;return value
 def filehash(self,p):
  p=Path(p).resolve()
  if not p.exists():return None
  h=digest(p);self.hashes[str(p)]=h;return h
 def changed(self):return [p for p,h in self.hashes.items() if not Path(p).exists() or digest(p)!=h]

def aggregate_checks(study,snap):
 index={};top=snap.read(study/'PLANNING_CHECK.json',{}) or {}
 for entry in top.get('checks',top.get('results',[])):
  if not isinstance(entry,dict):continue
  result=entry.get('result',entry)
  if entry.get('folder'):index[str(normpath(entry['folder'],study))]=result
  if entry.get('model') and entry.get('arm'):index[str((study/'runs'/entry['model']/entry['arm']).resolve())]=result
 return top,index

def compare(a,b):
 """Lower deficiency is better. Overlap also includes separation below margin."""
 if not a.get('comparison_eligible') or not b.get('comparison_eligible'):
  return {'classification':'unavailable','difference_lower':None,'difference_upper':None,'reason':'; '.join(x for x in [None if a.get('comparison_eligible') else 'arm: '+a.get('endpoint_status','missing'),None if b.get('comparison_eligible') else 'baseline: '+b.get('endpoint_status','missing')] if x)}
 lo=a['audit_lower']-b['audit_upper'];hi=a['audit_upper']-b['audit_lower']
 return {'classification':'win' if hi < -MARGIN else 'loss' if lo > MARGIN else 'overlap_or_within_margin','difference_lower':lo,'difference_upper':hi,'reason':None}

def csv_write(path,rows):
 keys=list(dict.fromkeys(k for r in rows for k in r))
 with path.open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=keys);w.writeheader()
  for r in rows:w.writerow({k:json.dumps(v,sort_keys=True) if isinstance(v,(dict,list)) else v for k,v in r.items()})

def collect(study,audits,snap):
 queue=snap.read(study/'QUEUE.json');inventory=snap.read(study/'MODELS.json')
 if not queue or not inventory:raise ValueError('QUEUE.json and MODELS.json are required')
 models=queue['models'];by_model={m['id']:m for m in inventory['models']}
 if len(by_model)!=len(models) or set(by_model)!={m['id'] for m in models}:raise ValueError('Frozen model queue and inventory disagree')
 budgets=list(queue.get('checkpoints',[2,10,40]));arms=queue['arms'];planning=snap.read(study/'PLANNING_STATUS.json',{}) or {};execution=snap.read(study/'EXECUTION_QUEUE.json',{}) or {}
 topcheck,checks=aggregate_checks(study,snap)
 bindings_doc=snap.read(audits/'BINDINGS.json',{}) or {};binding_list=bindings_doc.get('bindings',[]);bindings={}
 for b in binding_list:
  key=(b.get('model'),b.get('arm'),b.get('endpoint'))
  if key in bindings:raise ValueError('Duplicate audit binding: '+repr(key))
  bindings[key]=b
 aq=snap.read(audits/'AUDIT_QUEUE.json',{}) or {};astatus=snap.read(audits/'STATUS.json',{}) or {};final=snap.read(audits/'FINAL_INPUT_CHECK.json',{}) or {}
 proc_index={(r.get('model'),r.get('arm')):r for r in planning.get('results',[])}
 audit_status={r.get('audit_id'):r for r in astatus.get('results',[])}
 frozen=aq.get('frozen_files',{});drift=[];source_drift=[]
 for p,h in frozen.items():
  f=normpath(p,study)
  if not f.exists() or snap.filehash(f)!=h:drift.append(str(f))
 for p,h in aq.get('source_sha256',{}).items():
  f=normpath(p,study)
  if not f.exists() or snap.filehash(f)!=h:source_drift.append(str(f));drift.append(str(f))
 for p in final.get('changed_paths',[]):
  if str(normpath(p,study)) not in drift:drift.append(str(normpath(p,study)))
 binding_hash_ok=bool(aq.get('bindings_sha256')) and snap.filehash(audits/'BINDINGS.json')==aq.get('bindings_sha256')
 global_files={str((study/n).resolve()) for n in ['MODELS.json','QUEUE.json','PLANNING_STATUS.json']}
 global_drift=not binding_hash_ok or any(p in global_files for p in drift) or bool(source_drift) or bool(final.get('changed_sources'))
 if final.get('status') not in (None,'passed') and not drift:global_drift=True
 rows=[];processes=[];expected_methods=[]
 for arm in arms:
  if arm=='baseline':expected_methods.extend(BASELINES)
  else:
   expected_methods.append(arm)
   if arm in ADAPTIVE:expected_methods.append(arm+'_average')
 methods=list(dict.fromkeys(expected_methods))
 for m in models:
  mid=m['id'];model=by_model[mid];mp=normpath(model['path'],study);model_ok=snap.filehash(mp)==model.get('sha256')
  for arm in arms:
   folder=study/'runs'/mid/arm;run=snap.read(folder/'result.json',{}) or {};meta=snap.read(folder/'metadata.json',{}) or {};process=snap.read(folder/'PROCESS.json',None) or proc_index.get((mid,arm),{});failure=snap.read(folder/'FAILURE.json',{}) or {}
   check=snap.read(folder/'PLANNING_CHECK.json',None) or checks.get(str(folder.resolve()),{})
   processes.append({'model':mid,'arm':arm,'process_exit':process.get('exit'),'process_error':process.get('error'),'planner_status':run.get('status'),'planner_error':run.get('error',failure.get('error')),'planning_check':check.get('status','missing'),'planning_check_error':check.get('error'),'wall_seconds':process.get('wall_seconds'),'planning_seconds':run.get('planning_seconds',run.get('end_to_end_seconds')),'export_seconds':run.get('export_seconds'),'rounds':run.get('iterations'),'run_folder':str(folder)})
   endpoints=[(b,b,False) for b in BASELINES] if arm=='baseline' else [(arm,f'checkpoint_{b}',False) for b in budgets]+([(arm+'_average',f'average_checkpoint_{b}',True) for b in budgets] if arm in ADAPTIVE else [])
   for method,endpoint,secondary in endpoints:
    path=folder/endpoint/'policy.npz';polmeta=snap.read(path.with_suffix('.json'),{}) or {};binding=bindings.get((mid,arm,endpoint));face=meta.get('face') or {}
    applicable_budgets=budgets if arm=='baseline' else [int(endpoint.rsplit('_',1)[-1])]
    for budget in applicable_budgets:
     r={'model':mid,'worlds':m.get('worlds'),'states':m.get('states'),'concentration':m.get('concentration'),'seed':m.get('seed'),'collection_horizon':m.get('t',3),'target_depth':queue.get('heldout_depth',4),'method':method,'label':LABELS.get(method,method),'arm':arm,'endpoint':endpoint,'budget_seconds':budget,'analysis_role':'secondary_realization_average' if secondary else 'primary_40s' if budget==40 else 'earlier_checkpoint','secondary':secondary,'objective_scope':'realization_average_of_adaptive_weighted_collectors' if secondary else 'rich_background_truncation' if arm in ('fixed',*ADAPTIVE) else 'finite_library_minimax_with_reward_constraint' if face else 'finite_library_minimax' if arm=='minimax' else 'finite_information_gain' if method=='information' else 'finite_posterior_Brier_gain' if method=='brier' else 'uniform_action_control','policy_path':str(path),'policy_present':path.exists(),'available_seconds':finite(polmeta.get('available_seconds')),'iteration':polmeta.get('iteration'),'policy_kind':polmeta.get('policy_kind','baseline_DP' if method in BASELINES[:2] else method),'planning_process_exit':process.get('exit'),'planning_process_error':process.get('error'),'planning_status':run.get('status'),'planning_error':run.get('error',failure.get('error')),'planning_check_status':check.get('status','missing'),'planning_check_error':check.get('error'),'planning_residual':finite(check.get('residual')),'selected_lower':finite(polmeta.get('selected_lower')),'selected_upper':finite(polmeta.get('selected_upper')),'selected_gap':finite(polmeta.get('selected_gap')),'omitted_mass':None,'omitted_mass_float':None,'selected_gap_plus_omitted_tail':None,'baseline_reward':finite(polmeta.get('reward')),'baseline_optimal_reward':finite(polmeta.get('optimal_reward')),'comparison_eligible':False,'endpoint_status':'missing_policy','audit_id':None,'audit_lower':None,'audit_upper':None,'audit_complete':False,'audit_completed_targets':0,'audit_expected_targets':32768,'audit_worker_status':None,'audit_validation_status':None,'audit_error':None,'numerical_interval_scope':'Repaired floating-point witness bounds; not exact/outward-rounded or statistical confidence intervals','issues':[]}
     if arm in ('fixed',*ADAPTIVE):
      tail=polmeta.get('omitted_mass',meta.get('omitted_mass'));r['omitted_mass']=tail;r['omitted_mass_float']=fraction_float(tail)
      if tail is not None:
       try:
        if Fraction(tail)!=expected_tail():r['issues'].append('omitted_tail_differs_from_frozen_background')
       except (TypeError,ValueError,ZeroDivisionError):r['issues'].append('invalid_omitted_tail_metadata')
      if r['selected_gap'] is not None and r['omitted_mass_float'] is not None:r['selected_gap_plus_omitted_tail']=max(0.,r['selected_gap'])+r['omitted_mass_float']
     if face:
      round_record=snap.read(folder/f"round_{int(polmeta['iteration']):03d}"/'record.json',{}) if polmeta.get('iteration') is not None else {}
      actual=finite((round_record or {}).get('actual_reward'));threshold=finite(face.get('threshold'))
      r.update(reward_face=face.get('reward'),reward_face_percent=finite(face.get('percent')),reward_optimum=finite(face.get('maximum')),reward_minimum=finite(face.get('minimum')),reward_range=finite(face.get('range')),reward_threshold=threshold,reward_allowed_slack=finite(face.get('slack')),reward_numerical_slack=finite(face.get('numerical_slack')),actual_reward=actual,reward_threshold_shortfall=max(0.,threshold-actual) if actual is not None and threshold is not None else None,face_repair_mixture=finite((round_record or {}).get('face_repair_mixture')))
     row_paths=[str(mp),str(path.resolve()),str(path.with_suffix('.json').resolve())]
     drift_here=[p for p in drift if p in row_paths or p.startswith(str(folder.resolve())+os.sep)]
     if global_drift:r['issues'].append('global_frozen_binding_or_input_integrity_failure')
     if drift_here:r['issues'].append('frozen_input_changed');r['changed_paths']=drift_here
     if not model_ok:r['issues'].append('model_hash_mismatch')
     if not r['policy_present']:r['endpoint_status']='missing_policy'
     elif r['available_seconds'] is None:r['endpoint_status']='missing_availability_time'
     elif r['available_seconds']>budget:r['endpoint_status']='late_for_checkpoint'
     elif check.get('status')!='passed':r['endpoint_status']='planning_validation_'+check.get('status','missing')
     elif r['issues']:r['endpoint_status']='input_integrity_failure'
     elif not binding:r['endpoint_status']='audit_binding_missing'
     elif binding.get('status')=='invalid':r['endpoint_status']='audit_binding_invalid';r['audit_error']=binding.get('error',binding.get('reason'))
     elif not binding.get('audit_id'):r['endpoint_status']='audit_not_queued';r['audit_error']=binding.get('reason')
     elif snap.filehash(path)!=binding.get('policy_sha256') or binding.get('model_sha256')!=model.get('sha256'):r['endpoint_status']='audit_binding_hash_mismatch'
     elif binding.get('policy_metadata_sha256') and snap.filehash(path.with_suffix('.json'))!=binding['policy_metadata_sha256']:r['endpoint_status']='audit_binding_metadata_mismatch'
     else:
      aid=binding['audit_id'];ad=audits/'audits'/aid;ar=snap.read(ad/'result.json',{}) or {};av=snap.read(ad/'validation.json',{}) or {};task=audit_status.get(aid,{})
      r.update(audit_id=aid,audit_directory=str(ad),exact_E_sha256=binding.get('exact_E_sha256'),audit_worker_status=ar.get('status',task.get('audit_status')),audit_orchestrator_status=task.get('status'),audit_validation_status=av.get('status','missing'),audit_error=av.get('error',task.get('error')),audit_seconds=finite(ar.get('elapsed_seconds')),audit_validation_seconds=finite(av.get('validation_seconds')),audit_completed_targets=av.get('completed_target_count',ar.get('completed_target_count',0)),audit_expected_targets=av.get('expected_target_count',32768),audit_global_upper_source=av.get('global_upper_source',ar.get('global_upper_source')))
      if av.get('status')!='passed':r['endpoint_status']='audit_validation_'+av.get('status','pending')
      else:
       lo,hi=finite(av.get('audit_lower')),finite(av.get('audit_upper'))
       if lo is None or hi is None or lo>hi+2e-7 or lo < -2e-7 or hi>1+2e-7:r['endpoint_status']='invalid_audit_interval'
       else:
        r['audit_raw_lower']=lo;r['audit_raw_upper']=hi
        r['audit_lower']=max(0.,min(lo,hi));r['audit_upper']=min(1.,max(lo,hi))
        complete=ar.get('status')=='complete' and ar.get('complete') is True and av.get('complete') is True and r['audit_completed_targets']==32768
        r.update(audit_complete=complete,comparison_eligible=True,endpoint_status='validated_complete' if complete else 'validated_partial')
     rows.append(r)
 # Preserve orchestration-only placeholders without inflating scientific missingness.
 all_bindings=[]
 for b in binding_list:
  z=dict(b);z['structurally_not_applicable']=b.get('endpoint','').startswith('average_checkpoint_') and b.get('arm') not in ADAPTIVE;all_bindings.append(z)
 unfinished=planning.get('state')!='finished' or astatus.get('state') not in ('finished','finished_with_input_changes') or final.get('status')!='passed'
 state={'created_utc':stamp(),'study':str(study),'audit_output':str(audits),'status':'provisional' if unfinished or drift or not binding_hash_ok else 'final_snapshot','planning_state':planning.get('state'),'audit_state':astatus.get('state'),'final_input_check':final,'frozen_input_changes':drift,'frozen_source_changes':source_drift,'bindings_hash_matches_frozen_queue':binding_hash_ok,'model_count':len(models),'independent_seed_families':sorted({m['seed'] for m in models}),'planned_processes':len(models)*len(arms),'planned_scientific_endpoints':len(rows),'expected_audit_bindings':len(models)*(len(BASELINES)+(len(arms)-1)*len(budgets)+sum(a in ADAPTIVE for a in arms)*len(budgets)),'observed_audit_bindings':len(all_bindings),'structural_average_placeholders':sum(b['structurally_not_applicable'] for b in all_bindings),'pairwise_margin':MARGIN,'background_omitted_mass':str(expected_tail()),'background_omitted_mass_float':float(expected_tail()),'queue':queue,'execution_queue':execution,'planning_status':planning,'audit_status':astatus,'planning_check_summary':topcheck,'methods':methods,'budgets':budgets,'models':models,'scope':'Finite supplied-model, collection-length3 and target-depth4 numerical comparison; two seed families, not12 independent replicates. No efficient full-J_w, statistical superiority, all-optima or eventual-exploration claim.'}
 return state,rows,processes,all_bindings

def build_pairs(rows,state):
 index={(r['model'],r['method'],r['budget_seconds']):r for r in rows};out=[]
 for r in rows:
  if r['method'] in BASELINES:continue
  for b in BASELINES:
   baseline=index.get((r['model'],b,r['budget_seconds']),{'endpoint_status':'baseline_row_missing'})
   out.append({k:r[k] for k in ('model','worlds','concentration','seed','method','budget_seconds','analysis_role','secondary')}|{'baseline':b,'margin':MARGIN,'arm_lower':r['audit_lower'],'arm_upper':r['audit_upper'],'baseline_lower':baseline.get('audit_lower'),'baseline_upper':baseline.get('audit_upper'),'arm_status':r['endpoint_status'],'baseline_status':baseline.get('endpoint_status'),'arm_audit_id':r.get('audit_id'),'baseline_audit_id':baseline.get('audit_id'),'arm_selected_gap':r.get('selected_gap'),'arm_omitted_mass':r.get('omitted_mass'),'arm_available_seconds':r.get('available_seconds'),'baseline_available_seconds':baseline.get('available_seconds'),'arm_planning_status':r.get('planning_status'),'baseline_planning_status':baseline.get('planning_status')}|compare(r,baseline))
 return out

def table(headers,body):
 def s(v):return str(v).replace('|','\\|').replace('\n',' ')
 return '| '+' | '.join(map(s,headers))+' |\n| '+' | '.join(['---']*len(headers))+' |\n'+'\n'.join('| '+' | '.join(map(s,row))+' |' for row in body)
def fmt(v):return '—' if v is None else f'{v:.6g}' if isinstance(v,(int,float)) else str(v)
def range_text(values):
 v=[x for x in values if x is not None];return '—' if not v else fmt(min(v))+' to '+fmt(max(v))

def counts_table(rows,state):
 body=[]
 for b in state['budgets']:
  for secondary in (False,True):
   r=[x for x in rows if x['budget_seconds']==b and x['secondary']==secondary];c=collections.Counter(x['endpoint_status'] for x in r)
   body.append([b,'average (secondary)' if secondary else 'primary methods',len(r),c['validated_complete'],c['validated_partial'],len(r)-c['validated_complete']-c['validated_partial']])
 return table(['Budget (s)','Endpoint family','Expected','Complete audits','Valid partial audits','Unavailable/invalid'],body)

def pair_table(pairs,methods,budget):
 body=[]
 for m in methods:
  row=[LABELS.get(m,m)]
  for b in BASELINES:
   c=collections.Counter(p['classification'] for p in pairs if p['method']==m and p['baseline']==b and p['budget_seconds']==budget)
   row.append(f"{c['win']} / {c['loss']} / {c['overlap_or_within_margin']} / {c['unavailable']}")
  body.append(row)
 return table(['Method','vs information W/L/U/M','vs Brier W/L/U/M','vs uniform W/L/U/M'],body)

def face_table(rows,state):
 body=[]
 for b in state['budgets']:
  for reward in ('information','brier'):
   for p in (0,1,5):
    rr=[r for r in rows if r['method']==f'{reward}_face{p}' and r['budget_seconds']==b];valid=[r for r in rr if r['planning_check_status']=='passed' and r['policy_present'] and r['available_seconds'] is not None and r['available_seconds']<=b]
    body.append([b,reward,p,f'{len(valid)}/{len(rr)}',range_text([r.get('selected_gap') for r in valid]),range_text([r.get('reward_allowed_slack') for r in valid]),fmt(max((r.get('reward_threshold_shortfall') or 0 for r in valid),default=None))])
 return table(['Budget','Reward','Face (%)','Timely validated policies','Selected minimax gap range','Allowed reward-loss range','Largest threshold shortfall'],body)

def plots(rows,pairs,state,out):
 import matplotlib
 matplotlib.use('Agg')
 import matplotlib.pyplot as plt
 import numpy as np
 models=[m['id'] for m in state['models']];budgets=state['budgets'];lookup={(r['model'],r['method'],r['budget_seconds']):r for r in rows};files=[]
 families={'primary':[*CORE,*BASELINES],'averages_secondary':['tractability','tractability_average','hard','hard_average',*BASELINES],'information_faces':['information','information_face0','information_face1','information_face5','minimax','fixed'],'brier_faces':['brier','brier_face0','brier_face1','brier_face5','minimax','fixed']}
 for family,methods in families.items():
  fig,axes=plt.subplots(len(budgets),1,figsize=(16,3.8*len(budgets)),sharex=True,squeeze=False);colors=plt.get_cmap('tab10')
  finite_high=[r['audit_upper'] for r in rows if r['method'] in methods and r['comparison_eligible']];top=min(1.02,max(.1,max(finite_high,default=1)*1.08))
  for ax,b in zip(axes.flat,budgets):
   for j,m in enumerate(methods):
    offset=(j-(len(methods)-1)/2)*.10
    for i,mid in enumerate(models):
     r=lookup.get((mid,m,b));x=i+offset
     if r and r['comparison_eligible']:
      lo,hi=r['audit_lower'],r['audit_upper'];center=(lo+hi)/2
      ax.errorbar(x,center,yerr=[[center-lo],[hi-center]],fmt='o',ms=3.5,capsize=2,color=colors(j),mfc=colors(j) if r['audit_complete'] else 'white',mew=.9)
     else:ax.plot(x,-.035,marker='x',ms=3,color=colors(j),transform=ax.get_xaxis_transform(),clip_on=False)
   ax.set_title(f'{b} seconds of planning — '+('primary endpoint' if b==40 else 'earlier checkpoint'));ax.set_ylabel('Worst depth-4 native deficiency');ax.set_ylim(-.01,top);ax.grid(axis='y',alpha=.2)
  axes[-1,0].set_xticks(range(len(models)),models,rotation=35,ha='right');axes[-1,0].set_xlabel('Fixed model classes (parameter settings share their seed)')
  handles=[plt.Line2D([],[],color=colors(i),marker='o',ls='',label=LABELS.get(m,m)) for i,m in enumerate(methods)]
  fig.legend(handles=handles,loc='lower center',ncol=min(4,len(handles)),bbox_to_anchor=(.5,0),frameon=False)
  fig.suptitle('Finite supplied-model comparison: '+family.replace('_',' ')+'\nIntervals are numerical audit bounds; hollow=partial; crosses below axes=unavailable',fontsize=12)
  fig.tight_layout(rect=(0,.07,1,.95));stem='deficiency_budgets_'+family
  for suffix in ('pdf','png'):fig.savefig(out/(stem+'.'+suffix),dpi=170,bbox_inches='tight');files.append(stem+'.'+suffix)
  plt.close(fig)
 for method in [m for m in state['methods'] if m not in BASELINES]:
  fig,axes=plt.subplots(1,3,figsize=(14,6),sharey=True);subset=[p for p in pairs if p['method']==method and p['budget_seconds']==40];ix={(p['model'],p['baseline']):p for p in subset}
  for ax,b in zip(axes,BASELINES):
   for i,mid in enumerate(models):
    p=ix.get((mid,b));y=len(models)-1-i
    if p and p['classification']!='unavailable':
     lo,hi=p['difference_lower'],p['difference_upper'];center=(lo+hi)/2;col={'win':'#207348','loss':'#b63b31','overlap_or_within_margin':'#737373'}[p['classification']]
     ax.errorbar(center,y,xerr=[[center-lo],[hi-center]],fmt='o',ms=4,capsize=3,color=col)
    else:ax.text(.5,y,'missing',transform=ax.get_yaxis_transform(),ha='center',va='center',fontsize=7,color='gray')
   ax.axvline(0,color='black',lw=.7);ax.axvspan(-MARGIN,MARGIN,color='gray',alpha=.15);ax.set_title('vs '+LABELS[b]);ax.set_xlabel('Method deficiency − baseline deficiency');ax.grid(axis='x',alpha=.2)
  axes[0].set_yticks(range(len(models)),list(reversed(models)));fig.suptitle(LABELS.get(method,method)+' — 40-second paired intervals\nLeft of zero favors method; right favors baseline; overlap is unresolved',fontsize=12);fig.tight_layout(rect=(0,0,1,.92));stem='paired_40_'+method
  for suffix in ('pdf','png'):fig.savefig(out/(stem+'.'+suffix),dpi=170,bbox_inches='tight');files.append(stem+'.'+suffix)
  plt.close(fig)
 return files

def render(state,rows,pairs,processes,bindings,figures):
 secondary=[m+'_average' for m in ADAPTIVE];faces=[f'{r}_face{p}' for r in ('information','brier') for p in (0,1,5)]
 unavailable=collections.Counter((r['budget_seconds'],r['method'],r['endpoint_status']) for r in rows if not r['comparison_eligible'])
 missing=table(['Budget','Method','Reason','Settings'],[[b,LABELS.get(m,m),reason,n] for (b,m,reason),n in sorted(unavailable.items())]) if unavailable else 'Every expected scientific endpoint has a validated audit interval.'
 failed=[p for p in processes if p['process_exit'] not in (0,None) or p['planner_status']=='failed' or p['planning_check'] not in ('passed','missing')]
 failures=table(['Model','Arm','Process exit','Planner status','Planning check','Error'],[[p['model'],p['arm'],p['process_exit'],p['planner_status'],p['planning_check'],p.get('planner_error') or p.get('process_error') or p.get('planning_check_error')] for p in failed]) if failed else 'No failed terminal process or failed planning validation is recorded; missing/running processes remain in the coverage tables and CSV.'
 values={'timestamp':state['created_utc'],'snapshot_status':state['status'],'coverage':counts_table(rows,state),'primary_table':pair_table(pairs,CORE,40),'earlier_tables':'\n\n'.join(f'**{b} seconds**\n\n'+pair_table(pairs,CORE,b) for b in state['budgets'] if b!=40),'secondary_table':pair_table(pairs,secondary,40),'face_comparisons':pair_table(pairs,faces,40),'face_diagnostics':face_table(rows,state),'missing_table':missing,'failure_table':failures,'omitted_fraction':state['background_omitted_mass'],'omitted_float':fmt(state['background_omitted_mass_float']),'model_count':str(state['model_count']),'seed_families':', '.join(map(str,state['independent_seed_families'])),'expected_rows':str(len(rows)),'expected_bindings':str(state['expected_audit_bindings']),'observed_bindings':str(state['observed_audit_bindings']),'structural_placeholders':str(state['structural_average_placeholders']),'structural_note':('The audit coordinator additionally reserved '+str(state['structural_average_placeholders'])+' inapplicable average slots. They remain in all_audit_bindings.csv as structural placeholders, separately from scientific missingness.' if state['structural_average_placeholders'] else 'Only hard-target and cost-adaptive methods have average endpoints. Inapplicable averages for fixed, minimax and reward-face methods are not counted as missing.'),'plots':'\n'.join(f'- [{p}]({p})' for p in figures if p.endswith('.pdf')) or 'Plot generation was disabled.','integrity':json.dumps({'final_input_check':state['final_input_check'],'frozen_input_changes':state['frozen_input_changes'],'frozen_source_changes':state['frozen_source_changes'],'bindings_hash_matches':state['bindings_hash_matches_frozen_queue'],'summary_input_changes':state.get('summary_input_changes',[])},indent=2)}
 text=(HERE/'REPORT_TEMPLATE.md').read_text()
 for key,value in values.items():text=text.replace('{{'+key+'}}',value)
 if re.search(r'\{\{[a-z_]+\}\}',text):raise ValueError('Unresolved report template placeholder')
 return text

def self_test():
 good=lambda lo,hi:{'comparison_eligible':True,'audit_lower':lo,'audit_upper':hi}
 assert compare(good(.1,.2),good(.3,.4))['classification']=='win'
 assert compare(good(.3,.4),good(.1,.2))['classification']=='loss'
 assert compare(good(.1,.3),good(.2,.4))['classification']=='overlap_or_within_margin'
 assert compare(good(.1,.2),good(.2+MARGIN/2,.3))['classification']=='overlap_or_within_margin'
 assert compare({'endpoint_status':'missing_policy'},good(0,1))['classification']=='unavailable'
 assert compare(good(0,1),good(.2,.3))['classification']=='overlap_or_within_margin'
 assert expected_tail()==Fraction(5369266971004237,109684753201889280)
 state={'created_utc':'test','status':'provisional','budgets':[2,10,40],'background_omitted_mass':str(expected_tail()),'background_omitted_mass_float':float(expected_tail()),'model_count':12,'independent_seed_families':[1,2],'expected_audit_bindings':468,'observed_audit_bindings':0,'structural_average_placeholders':0,'final_input_check':{},'frozen_input_changes':[],'frozen_source_changes':[],'bindings_hash_matches_frozen_queue':False}
 processes=[{'model':'mock','arm':'fixed','process_exit':0,'planner_status':'converged','planning_check':'passed'},{'model':'mock','arm':'hard','process_exit':1,'planner_status':'failed','planning_check':'failed','planner_error':'synthetic failure'}]
 report=render(state,[],[],processes,[],[])
 assert 'synthetic failure' in report and '{{' not in report
 print('In-memory classification, tail and report-schema tests passed; no study results read or written.')

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--study',type=Path,default=HERE);p.add_argument('--audits',type=Path);p.add_argument('--output',type=Path);p.add_argument('--no-plots',action='store_true');p.add_argument('--allow-provisional',action='store_true');p.add_argument('--self-test',action='store_true');args=p.parse_args()
 if args.self_test:self_test();return
 if args.audits is None:p.error('--audits OUT is required; audit outputs have no assumed location')
 study=args.study.resolve();audits=args.audits.resolve();out=(args.output or study/'summary').resolve()
 if out in (study,audits):p.error('Use a distinct summary output directory')
 out.mkdir(parents=True,exist_ok=True);snap=Snapshot();state,rows,processes,bindings=collect(study,audits,snap);pairs=build_pairs(rows,state)
 figures=[] if args.no_plots else plots(rows,pairs,state,out)
 changed=snap.changed();state['summary_input_changes']=changed;state['read_errors']=snap.errors
 if changed or snap.errors:state['status']='provisional'
 state['summary_source_sha256']=digest(__file__);state['template_sha256']=digest(HERE/'REPORT_TEMPLATE.md');state['input_sha256']=snap.hashes
 state['endpoint_status_counts']=dict(collections.Counter(r['endpoint_status'] for r in rows));state['pair_classification_counts']=dict(collections.Counter(p['classification'] for p in pairs))
 csv_write(out/'endpoints.csv',rows);csv_write(out/'paired_comparisons.csv',pairs);csv_write(out/'planning_processes.csv',processes);csv_write(out/'all_audit_bindings.csv',bindings)
 (out/'summary.json').write_text(json.dumps({'metadata':state,'endpoints':rows,'paired_comparisons':pairs,'planning_processes':processes,'audit_bindings':bindings},indent=2,allow_nan=False)+'\n')
 (out/'REPORT.md').write_text(render(state,rows,pairs,processes,bindings,figures))
 manifest={str(f.relative_to(out)):digest(f) for f in sorted(out.rglob('*')) if f.is_file() and f.name!='FILES.json'};(out/'FILES.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print(json.dumps({'status':state['status'],'output':str(out),'scientific_endpoints':len(rows),'coverage':state['endpoint_status_counts'],'paired_comparisons':len(pairs),'input_changes':changed,'read_errors':snap.errors},indent=2))
 if state['status']!='final_snapshot' and not args.allow_provisional:raise SystemExit(2)
if __name__=='__main__':main()
