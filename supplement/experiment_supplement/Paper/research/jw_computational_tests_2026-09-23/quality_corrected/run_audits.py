#!/usr/bin/env python3
"""Freeze or execute exhaustive audits of every declared planning endpoint.

Prepare only (never launches numerical jobs):
  python run_audits.py --prepare --out AUDIT_RUN [--reuse-from OLD_AUDIT_RUN]
Execute after planning has finished:
  python run_audits.py --run --out AUDIT_RUN --workers 36 --cpu-start 0

AUDIT_QUEUE.json: frozen input/source hashes, model-specific exact-E groups,
ordered jobs, and BINDINGS.json hash. BINDINGS.json records every expected endpoint,
including absent/invalid outputs and its unique audit ID when replay succeeds.
Average endpoints apply only to hard/tractability; other arms have no average slot.
STATUS.json updates atomically as futures finish (no ordered-map head blocking).
Each tasks/ID/ contains logs and PROCESS.json; audits/ID/ is reserved for the
worker, which requires a new empty directory. Numerical work and independent
validation run serially on the same allocated physical CPU.
Optional reuse selects every matching complete validated acquired experiment,
without consulting its score. Historical evidence is plain-copied, hash checked,
and independently revalidated; rejected reuse falls back to a fresh audit.
Historical audit cost and current reuse cost never count as planning time.
"""
import os
for _key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[_key]='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import argparse,concurrent.futures,datetime,hashlib,json,queue,re,shutil,signal,subprocess,threading,time,traceback
import numpy as np
HERE=Path(__file__).resolve().parent
DEFAULT_PYTHON='/tmp/exploration-lp-cpu-venv/bin/python'
BASELINES=('information','brier','uniform')
BUDGETS=(40,10,2)

def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def atomic(path,value):
    path=Path(path);temp=path.with_suffix(path.suffix+'.tmp');temp.write_text(json.dumps(value,indent=2,allow_nan=False)+'\n');temp.replace(path)
def read(path):return json.loads(Path(path).read_text())
def require(condition,message):
    if not condition:raise ValueError(message)
def exact_array_hash(E):
    a=np.ascontiguousarray(E);h=hashlib.sha256();h.update(json.dumps({'shape':a.shape,'dtype':a.dtype.str},sort_keys=True).encode());h.update(b'\0');h.update(a.tobytes());return h.hexdigest()
def priority(model,arm,endpoint):
    if arm=='baseline' or endpoint=='checkpoint_40':tier=0
    elif endpoint=='average_checkpoint_40':tier=1
    elif endpoint.endswith('_10'):tier=2
    else:tier=3
    return [tier,model,arm,endpoint]

def safe_relative(root,name):
    root=Path(root).resolve();relative=Path(name)
    require(not relative.is_absolute() and '..' not in relative.parts,'Unsafe evidence-relative path: '+str(name))
    path=root/relative
    require(not path.is_symlink() and path.is_file() and path.resolve().is_relative_to(root),'Missing or nonplain evidence file: '+str(path))
    return path

def evidence_inventory(folder):
    folder=Path(folder).resolve();inventory={}
    require(folder.is_dir(),'Missing old audit directory: '+str(folder))
    for path in sorted(folder.rglob('*')):
      require(not path.is_symlink(),'Refusing symlink in reused evidence: '+str(path))
      if path.is_file():inventory[str(path.relative_to(folder))]=sha(path)
      else:require(path.is_dir(),'Nonplain reused evidence entry: '+str(path))
    return inventory

def verify_inventory(folder,inventory):
    for relative,expected in inventory.items():
      require(sha(safe_relative(folder,relative))==expected,'Reused evidence hash changed: '+str(relative))

def complete_candidate(result,validation,process):
    return (result.get('status')=='complete' and result.get('complete') is True
      and result.get('completed_target_count')==32768 and result.get('expected_target_count')==32768
      and validation.get('status')=='passed' and validation.get('complete') is True
      and validation.get('completed_target_count')==32768 and validation.get('expected_target_count')==32768
      and process.get('status')=='complete_validated'
      and (process.get('numerical') or {}).get('exit')==0 and (process.get('validation') or {}).get('exit')==0)

def reuse_catalog(old_out,wanted):
    """Freeze eligible old evidence by model/E identity, never by audit value.

    Cheap completeness and recorded-validation gates come first. Every selected
    copy must still pass the current independent witness checker at execution.
    """
    if old_out is None:return {},dict(enabled=False,eligible_groups=0,candidates=[],rejections=[])
    old_out=Path(old_out).resolve();queue_path=old_out/'AUDIT_QUEUE.json';old_queue=read(queue_path)
    require(sha(old_out/'BINDINGS.json')==old_queue['bindings_sha256'],'Old binding manifest hash mismatch')
    old_status=read(old_out/'STATUS.json');statuses={r['audit_id']:r for r in old_status.get('results',[])}
    old_source_snapshots={}
    for original,expected in old_queue['source_sha256'].items():
      snapshot=old_out/'source'/(expected[:16]+'_'+Path(original).name)
      require(snapshot.is_file() and not snapshot.is_symlink() and sha(snapshot)==expected,'Old audit queue source snapshot mismatch')
      old_source_snapshots[str(snapshot)]=expected
    catalog={};candidates=[];rejections=[];started=time.perf_counter()
    for job in sorted(old_queue['jobs'],key=lambda j:j['audit_id']):
      key=(job['model_sha256'],job['exact_E_sha256'])
      if key not in wanted:continue
      aid=job['audit_id'];folder=old_out/'audits'/aid
      try:
        process_path=old_out/'tasks'/aid/'PROCESS.json';process=read(process_path) if process_path.exists() else statuses.get(aid,{})
        result=read(folder/'result.json');validation=read(folder/'validation.json')
        if not complete_candidate(result,validation,process):
          rejections.append(dict(audit_id=aid,reason='not_complete_and_independently_validated'));continue
        provenance=read(folder/'provenance.json')
        require(sha(folder/'model.npz')==job['model_sha256']==provenance['input_sha256'][provenance['model_source']],'Old model/input provenance mismatch')
        require(sha(folder/'policy.npz')==job['representative_policy_sha256']==provenance['input_sha256'][provenance['policy_source']],'Old policy/input provenance mismatch')
        for original,expected in provenance['input_sha256'].items():
          require(old_queue['frozen_files'].get(original)==expected,'Old audit input was not frozen in its queue')
        with np.load(folder/'policy.npz',allow_pickle=False) as policy:
          require(exact_array_hash(policy['E'])==job['exact_E_sha256'],'Old acquired-experiment hash mismatch')
        snapshot_hashes=[]
        for name in provenance.get('source_snapshots',[]):snapshot_hashes.append(sha(safe_relative(folder,name)))
        require(sorted(snapshot_hashes)==sorted(provenance['source_sha256'].values()),'Old execution provenance snapshots are incomplete or changed')
        require(sum(chunk['count'] for chunk in result['chunks'])==32768,'Old chunk count is incomplete')
        for chunk in result['chunks']:require(sha(safe_relative(folder,chunk['file']))==chunk['sha256'],'Old witness chunk hash mismatch')
        inventory=evidence_inventory(folder)
        selected=dict(old_output=str(old_out),old_audit_id=aid,old_audit_directory=str(folder),old_queue_sha256=sha(queue_path),old_bindings_sha256=old_queue['bindings_sha256'],model_sha256=key[0],exact_E_sha256=key[1],old_policy_sha256=job['representative_policy_sha256'],evidence_sha256=inventory,old_process=process,historical_numerical_wall_seconds=(process.get('numerical') or {}).get('wall_seconds'),historical_worker_elapsed_seconds=result.get('elapsed_seconds'),historical_validation_wall_seconds=(process.get('validation') or {}).get('wall_seconds'),historical_validation_internal_seconds=validation.get('validation_seconds'),old_source_snapshots_sha256=old_source_snapshots)
        candidates.append(dict(audit_id=aid,model_sha256=key[0],exact_E_sha256=key[1],file_count=len(inventory),selected=key not in catalog))
        catalog.setdefault(key,selected)
      except Exception as error:rejections.append(dict(audit_id=aid,reason='reuse_evidence_rejected',error=repr(error)))
    return catalog,dict(enabled=True,old_output=str(old_out),old_queue_sha256=sha(queue_path),selection='Every new model-SHA/exact-E group with complete independently validated old evidence; lexicographically first old audit ID for duplicate matches; no score-based selection',eligible_groups=len(catalog),candidates=candidates,rejections=rejections,preparation_hash_seconds=time.perf_counter()-started,scope='Metadata/hash eligibility only; current independent witness revalidation is required before reuse is accepted')

def prepare(study,out,reuse_from=None):
    """Read/replay all endpoints and freeze coverage; no solver subprocesses."""
    study=Path(study).resolve();out=Path(out).resolve()
    require(not out.exists() or not any(out.iterdir()),'Preparation requires a new or empty output directory')
    models_path=study/'MODELS.json';plan_path=study/'QUEUE.json';status_path=study/'PLANNING_STATUS.json'
    inventory=read(models_path);plan=read(plan_path);planning=read(status_path)
    require(planning.get('state')=='finished','Planning must be finished before audit coverage is frozen')
    models=inventory['models'];arms=plan['arms']
    require(len({m['id'] for m in models})==len(models),'Duplicate model IDs')
    require({m['id'] for m in models}=={m['id'] for m in plan['models']},'MODELS and planning QUEUE disagree')
    require(planning.get('completed_processes')==len(models)*len(arms),'Not every planned process has a terminal record')
    planning_audit_path=study/'PLANNING_AUDIT.json';planning_audit=read(planning_audit_path)
    require(planning_audit.get('state')=='finished' and planning_audit.get('checked_runs')==len(models)*len(arms),'Independent planning checks must finish before audit preparation')
    sys.path.insert(0,str(HERE))
    # This checker is independent of both the planner and numerical audit producer.
    from validate_audits import independent_input
    frozen={str(p):sha(p) for p in [models_path,plan_path,status_path,planning_audit_path]}
    bindings=[];groups={};unexpected=[]
    actual_models={p.name for p in (study/'runs').iterdir() if p.is_dir()} if (study/'runs').exists() else set()
    require(not (actual_models-{m['id'] for m in models}),'Unexpected model directories must be resolved explicitly')
    for model in sorted(models,key=lambda x:x['id']):
      mid=model['id'];model_path=(study/model['path']).resolve();require(sha(model_path)==model['sha256'],'Model hash mismatch: '+mid);frozen[str(model_path)]=model['sha256']
      model_arrays=np.load(model_path,allow_pickle=False)
      try:
       actual_arms={p.name for p in (study/'runs'/mid).iterdir() if p.is_dir()} if (study/'runs'/mid).exists() else set()
       require(not(actual_arms-set(arms)),'Unexpected arm directories must be resolved explicitly: '+mid)
       for arm in sorted(arms):
        folder=study/'runs'/mid/arm;result_path=folder/'result.json';process_path=folder/'PROCESS.json'
        require(process_path.exists(),'Missing terminal planning PROCESS.json: '+str(folder))
        frozen[str(process_path)]=sha(process_path);process=read(process_path)
        result=read(result_path) if result_path.exists() else None
        planning_check_path=folder/'PLANNING_CHECK.json';require(planning_check_path.exists(),'Missing independent planning check: '+str(folder));planning_check=read(planning_check_path);frozen[str(planning_check_path)]=sha(planning_check_path)
        for optional in [result_path,folder/'FILES.json',folder/'FAILURE.json']:
          if optional.exists():frozen[str(optional)]=sha(optional)
        names=list(BASELINES) if arm=='baseline' else [name for budget in BUDGETS for name in ([f'checkpoint_{budget}',f'average_checkpoint_{budget}'] if arm in ['hard','tractability'] else [f'checkpoint_{budget}'])]
        observed={p.name for p in folder.iterdir() if p.is_dir() and ((p.name.startswith('checkpoint_') or p.name.startswith('average_checkpoint_')) or (arm=='baseline' and p.name in BASELINES))} if folder.exists() else set()
        require(not(observed-set(names)),'Unplanned exported endpoint requires explicit coverage decision: '+str(folder))
        for endpoint in names:
          path=folder/endpoint/'policy.npz';meta=folder/endpoint/'policy.json'
          binding=dict(model=mid,arm=arm,endpoint=endpoint,priority=priority(mid,arm,endpoint),model_path=str(model_path),model_sha256=model['sha256'],policy_path=str(path),audit_id=None,planning_status=None if result is None else result.get('status'),planning_process_exit=process.get('exit'),planning_check_status=planning_check.get('status'),planning_check_path=str(planning_check_path))
          if not path.exists():
            binding.update(status='missing',reason='no_exported_policy',planning_endpoint=None if result is None else result.get('checkpoints',{}).get(endpoint.rsplit('_',1)[-1]));bindings.append(binding);continue
          frozen[str(path)]=sha(path);binding['policy_sha256']=frozen[str(path)]
          if meta.exists():frozen[str(meta)]=sha(meta);binding['policy_metadata_sha256']=frozen[str(meta)]
          try:
            with np.load(path,allow_pickle=False) as pol:
              T,Z,E,replay_error=independent_input(model_arrays,pol)
              key=exact_array_hash(E)
            binding.update(exact_E_sha256=key,replay_error=replay_error)
            if planning_check.get('status')!='passed':
              binding.update(status='invalid',reason='independent_planning_check_failed',planning_check_error=planning_check.get('error'));bindings.append(binding);continue
            binding['status']='queued'
            group=groups.setdefault((mid,key),dict(model=mid,model_path=str(model_path),model_sha256=model['sha256'],exact_E_sha256=key,members=[]))
            group['members'].append(len(bindings))
          except Exception as error:binding.update(status='invalid',reason='independent_model_policy_replay_failed',error=repr(error))
          bindings.append(binding)
      finally:model_arrays.close()
    group_list=list(groups.values())
    for group in group_list:
      representative=min((bindings[i] for i in group['members']),key=lambda b:b['priority'])
      group.update(priority=representative['priority'],representative_policy=representative['policy_path'],representative_policy_sha256=representative['policy_sha256'])
    group_list.sort(key=lambda g:g['priority'])
    for index,group in enumerate(group_list):
      safe=re.sub(r'[^A-Za-z0-9_.-]','_',group['model']);group['audit_id']=f'{index:04d}_{safe}_{group["exact_E_sha256"][:16]}'
      group['binding_count']=len(group['members'])
      for binding in group['members']:bindings[binding]['audit_id']=group['audit_id']
    catalog,reuse_report=reuse_catalog(reuse_from,{(g['model_sha256'],g['exact_E_sha256']) for g in group_list})
    for group in group_list:
      if (group['model_sha256'],group['exact_E_sha256']) in catalog:group['reuse']=catalog[(group['model_sha256'],group['exact_E_sha256'])]
    bindings_document=dict(schema='jw-quality-audit-bindings-v1',created_utc=utc(),study=str(study),scope='Every planned baseline and 2/10/40-second primary export, plus hard/tractability realization averages only; no audit-outcome selection',expected_endpoint_count=len(bindings),queued_endpoints=sum(b['status']=='queued' for b in bindings),missing_endpoints=sum(b['status']=='missing' for b in bindings),invalid_endpoints=sum(b['status']=='invalid' for b in bindings),bindings=bindings)
    source_paths=[Path(__file__).resolve(),HERE/'audit_worker.py',HERE/'validate_audits.py']
    backend=HERE.parents[1]/'target_selection_2026-09-23';source_paths.extend(backend/name for name in ['scaling_core.py','fast_decoder.py','certified_decoder.py'])
    source_hashes={str(p):sha(p) for p in source_paths}
    require(all(Path(p).exists() and sha(p)==h for p,h in frozen.items()),'Planning input changed during queue preparation')
    out.mkdir(parents=True,exist_ok=True);(out/'source').mkdir()
    for p,h in source_hashes.items():
      dest=out/'source'/(h[:16]+'_'+Path(p).name);shutil.copyfile(p,dest);require(sha(dest)==h,'Source changed while copying')
    atomic(out/'BINDINGS.json',bindings_document)
    document=dict(schema='jw-quality-audit-queue-v1',prepared_utc=utc(),study=str(study),source_sha256=source_hashes,frozen_files=frozen,bindings_sha256=sha(out/'BINDINGS.json'),priority_rule=['baseline and checkpoint_40','average_checkpoint_40','checkpoint_10 and average_checkpoint_10','checkpoint_2 and average_checkpoint_2'],within_tier='lexicographic model,arm,endpoint',deduplication='Only byte-identical E arrays of identical dtype/shape inside one model, after each policy independently replays',reuse=reuse_report,job_count=len(group_list),jobs=group_list)
    atomic(out/'AUDIT_QUEUE.json',document)
    atomic(out/'REUSE_PLAN.json',reuse_report)
    atomic(out/'STATUS.json',dict(state='prepared',updated_utc=utc(),total=len(group_list),completed=0,expected_endpoint_count=len(bindings),missing_endpoints=bindings_document['missing_endpoints'],invalid_endpoints=bindings_document['invalid_endpoints'],results=[]))
    return document

def cpu_allocation(start,count):
    require(1<=count<=36 and 0<=start,'Allocate at most 36 nonnegative consecutive CPUs')
    cpus=list(range(start,start+count));available=os.sched_getaffinity(0);require(set(cpus)<=available,'Requested CPU is outside process affinity')
    keys=[]
    for cpu in cpus:
      top=Path(f'/sys/devices/system/cpu/cpu{cpu}/topology')
      require((top/'physical_package_id').exists() and (top/'core_id').exists(),'Cannot verify physical CPU topology')
      keys.append(((top/'physical_package_id').read_text().strip(),(top/'core_id').read_text().strip()))
    require(len(set(keys))==len(keys),'Requested CPUs include two hyperthreads of one physical core')
    return cpus

def execute(document,out,args):
    out=Path(out).resolve();bindings=read(out/'BINDINGS.json');require(sha(out/'BINDINGS.json')==document['bindings_sha256'],'Bindings manifest changed')
    require(read(out/'STATUS.json')['state']=='prepared','Run is not fresh prepared state; refusing to overwrite or silently resume')
    require(all(Path(p).exists() and sha(p)==h for p,h in document['source_sha256'].items()),'Execution source changed after freeze')
    require(all(Path(p).exists() and sha(p)==h for p,h in document['frozen_files'].items()),'Planning/model/policy input changed after freeze')
    require(args.hard_seconds>args.soft_seconds>0 and args.validation_seconds>0,'Invalid soft/hard/validation timeouts')
    cpus=cpu_allocation(args.cpu_start,args.workers);pool=queue.Queue()
    for cpu in cpus:pool.put(cpu)
    (out/'tasks').mkdir();(out/'audits').mkdir()
    stop=threading.Event();lock=threading.Lock();active={};results=[];started=time.perf_counter()
    execution=dict(started_utc=utc(),workers=args.workers,cpus=cpus,soft_audit_seconds=args.soft_seconds,hard_process_seconds=args.hard_seconds,validation_hard_seconds=args.validation_seconds,python=str(Path(args.python).resolve()),queue_sha256=sha(out/'AUDIT_QUEUE.json'),source_sha256=document['source_sha256'],reuse_candidate_jobs=sum('reuse' in j for j in document['jobs']),audit_cost_scope='Historical numerical/validation, current copy/hash, and current revalidation costs are recorded separately for reused jobs; none is planning cost')
    atomic(out/'EXECUTION.json',execution)
    def status(state='running'):
      atomic(out/'STATUS.json',dict(state=state,updated_utc=utc(),elapsed_seconds=time.perf_counter()-started,total=len(document['jobs']),completed=len(results),reused_complete=sum(r.get('reuse_attempt',{}).get('status')=='accepted' for r in results),rejected_reuse_attempts=sum(r.get('reuse_attempt',{}).get('status')=='rejected_fresh_audit_required' for r in results),successful_complete=sum(r.get('status')=='complete_validated' for r in results),validated_partial=sum(r.get('status')=='partial_validated' for r in results),failed=sum(r.get('status') not in ['complete_validated','partial_validated'] for r in results),expected_endpoint_count=bindings['expected_endpoint_count'],missing_endpoints=bindings['missing_endpoints'],invalid_endpoints=bindings['invalid_endpoints'],active=[v for v in active.values()],results=results))
    def process(cmd,log_path,hard,cpu,aid,phase):
      env=dict(os.environ,OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1');tick=time.perf_counter()
      with log_path.open('w') as log:
        with lock:
          if stop.is_set():raise RuntimeError('Orchestrator interruption requested before subprocess launch')
          proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,env=env,start_new_session=True)
          active[aid]=dict(audit_id=aid,cpu=cpu,pid=proc.pid,phase=phase,started_utc=utc());status()
        timeout=False
        try:code=proc.wait(timeout=hard)
        except subprocess.TimeoutExpired:
          timeout=True
          try:os.killpg(proc.pid,signal.SIGKILL)
          except ProcessLookupError:pass
          code=proc.wait()
      return dict(command=cmd,exit=code,hard_timeout=timeout,wall_seconds=time.perf_counter()-tick,pid=proc.pid)
    def reuse(job,target,folder,cpu,record):
      """Copy and revalidate a frozen candidate, retaining rejected attempts."""
      candidate=job.get('reuse')
      if candidate is None:return False
      started_copy=time.perf_counter();source=Path(candidate['old_audit_directory']);attempt=dict(reused_from=str(source),old_audit_id=candidate['old_audit_id'],model_sha256=job['model_sha256'],exact_E_sha256=job['exact_E_sha256'],new_policy_sha256=job['representative_policy_sha256'],historical_numerical_wall_seconds=candidate['historical_numerical_wall_seconds'],historical_worker_elapsed_seconds=candidate['historical_worker_elapsed_seconds'],historical_validation_wall_seconds=candidate['historical_validation_wall_seconds'],historical_validation_internal_seconds=candidate['historical_validation_internal_seconds'],planning_cost_seconds=0.,status='checking_and_copying')
      record['reuse_attempt']=attempt
      try:
        # Plain copies isolate every JSON and witness from both old and new writes.
        require(not target.exists(),'Reuse destination is not new')
        require(evidence_inventory(source)==candidate['evidence_sha256'],'Old evidence inventory changed after freeze')
        for path,expected in candidate['old_source_snapshots_sha256'].items():require(sha(path)==expected,'Old queue source snapshot changed')
        require(sha(Path(candidate['old_output'])/'AUDIT_QUEUE.json')==candidate['old_queue_sha256'],'Old audit queue changed after reuse freeze')
        with np.load(job['representative_policy'],allow_pickle=False) as current:
          require(exact_array_hash(current['E'])==job['exact_E_sha256'],'Current acquired-experiment identity changed')
        shutil.copytree(source,target,copy_function=shutil.copy2,symlinks=False)
        require(evidence_inventory(target)==candidate['evidence_sha256'],'Copied evidence inventory differs from frozen source')
        (target/'validation.json').replace(target/'historical_validation.json')
        atomic(folder/'HISTORICAL_PROCESS.json',candidate['old_process'])
        attempt['copy_and_hash_seconds']=time.perf_counter()-started_copy
        atomic(target/'REUSE.json',dict(**attempt,old_queue_sha256=candidate['old_queue_sha256'],copied_evidence_sha256=candidate['evidence_sha256'],old_validation_preserved_as='historical_validation.json',scope='Old complete witness evidence transferred only across identical model SHA and bit-identical acquired experiment, then checked with the current independent validator; no new numerical optimization'))
        command=[args.python,str(HERE/'validate_audits.py'),'--audit',str(target),'--cpu',str(cpu)]
        validation=process(command,folder/'reuse_validation.log',args.validation_seconds,cpu,job['audit_id'],'reuse_validation')
        attempt['validation']=validation
        checked=read(target/'validation.json') if (target/'validation.json').exists() else {}
        require(validation['exit']==0 and checked.get('status')=='passed' and checked.get('complete') is True and checked.get('completed_target_count')==32768,'Current validator rejected reused complete evidence')
        attempt.update(status='accepted',current_copy_and_recheck_seconds=attempt['copy_and_hash_seconds']+validation['wall_seconds'])
        record['numerical']=dict(exit=0,hard_timeout=False,wall_seconds=0.,mode='reused_complete_witnesses',historical_numerical_wall_seconds=candidate['historical_numerical_wall_seconds'])
        record['validation']=validation;record['reused_from']=str(source)
        atomic(target/'REUSE.json',read(target/'REUSE.json') | attempt);atomic(folder/'PROCESS.json',record)
        return True
      except Exception as error:
        attempt.update(status='rejected_fresh_audit_required',error=repr(error),attempt_wall_seconds=time.perf_counter()-started_copy)
        if target.exists():target.replace(folder/'rejected_reuse_audit')
        atomic(folder/'REUSE_REJECTION.json',attempt);atomic(folder/'PROCESS.json',record)
        return False

    def task(job):
      aid=job['audit_id'];cpu=pool.get();folder=out/'tasks'/aid;target=out/'audits'/aid
      record=dict(audit_id=aid,model=job['model'],cpu=cpu,started_utc=utc(),status='starting',audit_directory=str(target),binding_count=job['binding_count'])
      try:
        folder.mkdir();atomic(folder/'PROCESS.json',record)
        if stop.is_set():record['status']='cancelled_before_start';return record
        require(sha(job['model_path'])==job['model_sha256'] and sha(job['representative_policy'])==job['representative_policy_sha256'],'Input changed before job launch')
        reused=reuse(job,target,folder,cpu,record)
        if not reused:
          cmd=[args.python,str(HERE/'audit_worker.py'),'--model',job['model_path'],'--policy',job['representative_policy'],'--out',str(target),'--cpu',str(cpu),'--hard-seconds',str(args.soft_seconds)]
          record['numerical']=process(cmd,folder/'audit.log',args.hard_seconds,cpu,aid,'numerical');atomic(folder/'PROCESS.json',record)
          if stop.is_set():record['status']='interrupted';return record
          # Always validate honest partial runs too; missing evidence stays visible.
          if target.exists():
            cmd=[args.python,str(HERE/'validate_audits.py'),'--audit',str(target),'--cpu',str(cpu)]
            record['validation']=process(cmd,folder/'validation.log',args.validation_seconds,cpu,aid,'validation')
          else:record['validation']=dict(exit=None,error='audit_directory_missing')
        result=read(target/'result.json') if (target/'result.json').exists() else None
        checked=read(target/'validation.json') if (target/'validation.json').exists() else None
        record.update(audit_status=None if result is None else result.get('status'),completed_target_count=0 if result is None else result.get('completed_target_count',0),audit_lower=None if checked is None or checked.get('status')!='passed' else checked.get('audit_lower'),audit_upper=None if checked is None or checked.get('status')!='passed' else checked.get('audit_upper'))
        if checked is not None and checked.get('status')=='passed' and record['validation']['exit']==0:
          record['status']='complete_validated' if result is not None and result.get('complete') and checked.get('complete') and record['numerical']['exit']==0 else 'partial_validated'
        else:record['status']='failed'
      except BaseException as error:record.update(status='failed',error=repr(error),traceback=traceback.format_exc())
      finally:
        record['finished_utc']=utc()
        try:
          if folder.exists():atomic(folder/'PROCESS.json',record)
        finally:
          with lock:active.pop(aid,None)
          pool.put(cpu)
      return record
    interrupted=False;executor=concurrent.futures.ThreadPoolExecutor(max_workers=args.workers);futures={}
    try:
      with lock:status()
      for job in document['jobs']:futures[executor.submit(task,job)]=job['audit_id']
      for future in concurrent.futures.as_completed(futures):
        try:record=future.result()
        except BaseException as error:record=dict(audit_id=futures[future],status='orchestrator_task_failure',error=repr(error))
        with lock:results.append(record);status()
        print(json.dumps(record),flush=True)
    except KeyboardInterrupt:
      interrupted=True;stop.set()
      with lock:
        for item in list(active.values()):
          try:os.killpg(item['pid'],signal.SIGTERM)
          except ProcessLookupError:pass
      for future in futures:future.cancel()
    finally:
      executor.shutdown(wait=True,cancel_futures=interrupted)
      if interrupted:
        known={r['audit_id'] for r in results}
        for future,aid in futures.items():
          if aid in known:continue
          if future.cancelled():results.append(dict(audit_id=aid,status='not_started_after_interrupt'))
          else:
            try:results.append(future.result())
            except BaseException as error:results.append(dict(audit_id=aid,status='orchestrator_task_failure',error=repr(error)))
      inventory=dict(document['frozen_files'],**document['source_sha256'])
      changes=[p for p,h in inventory.items() if not Path(p).exists() or sha(p)!=h]
      changed_sources=[p for p in changes if p in document['source_sha256']]
      atomic(out/'FINAL_INPUT_CHECK.json',dict(status='passed' if not changes else 'changed',changed_paths=changes,changed_sources=changed_sources,checked_files=len(inventory)))
      with lock:status('interrupted' if interrupted else ('finished' if not changes else 'finished_with_input_changes'))
    return 130 if interrupted else (2 if changes or any(r['status'] not in ['complete_validated','partial_validated'] for r in results) or bindings['invalid_endpoints'] else 0)

def main():
    p=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter);mode=p.add_mutually_exclusive_group(required=True);mode.add_argument('--prepare',action='store_true');mode.add_argument('--run',action='store_true')
    p.add_argument('--study',default=str(HERE));p.add_argument('--out',required=True);p.add_argument('--reuse-from',help='Old audit output; freeze complete validated exact-model/exact-E reuse candidates before launch');p.add_argument('--workers',type=int,default=36);p.add_argument('--cpu-start',type=int,default=0);p.add_argument('--soft-seconds',type=float,default=1800.);p.add_argument('--hard-seconds',type=float,default=1860.);p.add_argument('--validation-seconds',type=float,default=600.);p.add_argument('--python',default=DEFAULT_PYTHON);args=p.parse_args()
    out=Path(args.out).resolve()
    if args.prepare or not(out/'AUDIT_QUEUE.json').exists():document=prepare(args.study,out,args.reuse_from)
    else:
      document=read(out/'AUDIT_QUEUE.json')
      if args.reuse_from:require(str(Path(args.reuse_from).resolve())==document.get('reuse',{}).get('old_output'),'Reuse source differs from prepared frozen queue')
    print(json.dumps(dict(state='prepared',unique_audits=document['job_count'],out=str(out))),flush=True)
    return 0 if args.prepare else execute(document,out,args)
if __name__=='__main__':sys.exit(main())
