"""Exhaustive t3/n4 fixed-policy audit; one CPU worker, independent native replay.

Writes only the caller's new output directory. Numerical witnesses are evaluated
on original probabilities. They are floating-point evidence, not interval proofs.
"""
import os
for _key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[_key]='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import argparse,hashlib,importlib.metadata,itertools,json,signal,time,traceback,shutil
import numpy as np
HERE=Path(__file__).resolve().parent
BACKEND=HERE.parents[1]/'target_selection_2026-09-23'
sys.path.insert(0,str(BACKEND))
from certified_decoder import StableDecoder
TOL=2e-7
COUNT=32768

def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def write_json(path,value):
    temp=path.with_suffix(path.suffix+'.tmp');temp.write_text(json.dumps(value,indent=2,allow_nan=False)+'\n');temp.replace(path)
def write_npz(path,**arrays):
    temp=path.with_suffix(path.suffix+'.tmp')
    with temp.open('wb') as f:np.savez_compressed(f,**arrays)
    temp.replace(path)
def require(condition,message):
    if not condition:raise ValueError(message)

def load_and_replay(model_path,policy_path):
    with np.load(model_path,allow_pickle=False) as m:T=m['T'].copy();Z=m['Z'].copy()
    with np.load(policy_path,allow_pickle=False) as p:E=p['E'].copy();rows=p['rows'].copy();leaf=p['leaf'].copy()
    require(T.ndim==4 and T.shape[1]==2 and T.shape[2]==T.shape[3] and T.shape[0]>=1,'T must be Q x2 xS xS')
    Q,_,S,_=T.shape
    require(Z.shape==(Q,2,S,2),'Z must be Q x2 xS x2')
    require(rows.shape==(21,2) and leaf.shape==(64,) and E.shape==(Q,64),'Expected canonical t3 rows21x2, leaf64, E Qx64')
    for name,array in [('T',T),('Z',Z),('rows',rows),('leaf',leaf),('E',E)]:
        require(np.isfinite(array).all() and np.min(array)>=0,f'{name} must be finite nonnegative')
    for name,array in [('T',T),('Z',Z),('rows',rows),('E',E)]:
        require(np.max(abs(array.sum(axis=-1)-1))<=1e-10,f'{name} stochasticity failure')
    # Breadth-first full action-observation histories, actions then observations.
    start=np.zeros((Q,S));start[:,0]=1
    nodes=[(start,1.)];row_index=0
    for depth in range(3):
      children=[]
      for state,weight in nodes:
        row=rows[row_index];row_index+=1
        for a in (0,1):
          predicted=np.einsum('qs,qsu->qu',state,T[:,a])
          for o in (0,1):children.append((predicted*Z[:,a,:,o],weight*row[a]))
      nodes=children
    independent_leaf=np.asarray([weight for _,weight in nodes])
    independent_E=np.stack([state.sum(axis=1)*weight for state,weight in nodes],axis=1)
    errors=dict(E=float(np.max(abs(E-independent_E))),leaf=float(np.max(abs(leaf-independent_leaf))))
    require(max(errors.values())<=1e-10,'Policy/model replay disagrees with supplied E or leaf')
    return T,Z,E,rows,leaf,errors

def target_kernel(T,Z,index):
    # Direct physical-model propagation; no target-generator/backend import.
    Q,_,S,_=T.shape;F=np.zeros((Q,16))
    for column,obs in enumerate(itertools.product((0,1),repeat=4)):
      state=np.zeros((Q,S));state[:,0]=1;node=0
      for o in obs:
        a=(index>>(14-node))&1
        state=np.einsum('qs,qsu->qu',state,T[:,a])*Z[:,a,:,o]
        node=2*node+1+o
      F[:,column]=state.sum(axis=1)
    return F

def witness(E,F,decoder):
    report,w=decoder.solve(F)
    G=np.full((E.shape[1],F.shape[1]),1/F.shape[1]);G[w['source_indices']]=w['decoder']
    alpha=w['alpha'];b=w['b']
    residual=max(float(abs(G.sum(1)-1).max()),float(max(0,-G.min())),float(abs(alpha.sum()-1)),float(max(0,-alpha.min())),float(max(0,-b.min())),float(np.maximum(b-alpha[:,None],0).max()))
    upper=float(np.abs(E@G-F).sum(1).max()/2);lower=float((F*b).sum()-np.max(E.T@b,axis=1).sum());gap=upper-lower
    require(np.isfinite([lower,upper,residual]).all(),'Nonfinite witness')
    require(residual<=1e-12 and lower<=upper+1e-10 and gap<=TOL,'Original-probability witness failed')
    return dict(lower=lower,upper=upper,gap=gap,feasibility=residual),dict(G=G,alpha=alpha,b=b,F=F),dict(fallback_used=bool(report.get('fallback_used',False)),merged_source_columns=int(report.get('merged_source_columns',0)),coarsening_bound=float(report.get('coarsening_bound',0)))

def run(args):
    out=Path(args.out).resolve();out.mkdir(parents=True,exist_ok=True)
    require(not any(out.iterdir()),'Output directory must be new or empty; refusing overwrite')
    require(args.cpu in os.sched_getaffinity(0),'Requested CPU is unavailable')
    require(np.isfinite(args.hard_seconds) and args.hard_seconds>0,'hard-seconds must be positive')
    os.sched_setaffinity(0,{args.cpu})
    start=time.monotonic();deadline=start+args.hard_seconds
    state=dict(status='starting',complete=False,target_depth=4,collection_length=3,expected_target_count=COUNT,completed_target_count=0,audit_lower=0.,audit_upper=1.,global_upper_source='universal TV bound',cpu=args.cpu,hard_seconds=args.hard_seconds,certificate_tolerance=TOL,certificate_scope='Repaired floating-point decoder upper and decision-dual lower on original probabilities; no exact arithmetic or outward rounding',chunks=[],input_replay=None,elapsed_seconds=0.)
    bounds=[];buffer=[];hardest=None;hardest_upper=None;input_hashes={};full_upper=1.;completed=False
    def checkpoint():
      nonlocal buffer
      if buffer:
        first=buffer[0][0];last=buffer[-1][0];path=out/'chunks'/f'{first:05d}_{last:05d}.npz';path.parent.mkdir(exist_ok=True)
        write_npz(path,indices=np.asarray([i for i,_,_,_ in buffer]),lower=np.asarray([r['lower'] for _,r,_,_ in buffer]),upper=np.asarray([r['upper'] for _,r,_,_ in buffer]),G=np.stack([w['G'] for _,_,w,_ in buffer]),alpha=np.stack([w['alpha'] for _,_,w,_ in buffer]),b=np.stack([w['b'] for _,_,w,_ in buffer]),F=np.stack([w['F'] for _,_,w,_ in buffer]))
        state['chunks'].append(dict(file=str(path.relative_to(out)),sha256=digest(path),count=len(buffer),first=first,last=last));buffer=[]
      if bounds:
        write_npz(out/'bounds.npz',indices=np.asarray([i for i,_ in bounds]),lower=np.asarray([r['lower'] for _,r in bounds]),upper=np.asarray([r['upper'] for _,r in bounds]))
      for name,record in [('hardest_witness.npz',hardest),('largest_upper_witness.npz',hardest_upper)]:
        if record is not None:
          i,r,w=record;write_npz(out/name,index=np.asarray(i),lower=np.asarray(r['lower']),upper=np.asarray(r['upper']),**w)
      state.update(completed_target_count=len(bounds),elapsed_seconds=time.monotonic()-start,audit_lower=max([0.]+[r['lower'] for _,r in bounds]),audit_upper=min(full_upper,max(r['upper'] for _,r in bounds)) if completed else full_upper,global_upper_source='minimum of complete target uppers and full-revelation upper' if completed else ('full-revelation decoder' if (out/'full_revelation_witness.npz').exists() else 'universal TV bound'),hardest_lower_target=None if hardest is None else hardest[0],largest_upper_target=None if hardest_upper is None else hardest_upper[0],max_per_target_gap=max([0.]+[r['gap'] for _,r in bounds]),max_witness_feasibility=max([0.]+[r['feasibility'] for _,r in bounds]))
      write_json(out/'checkpoint.json',state)
    def alarm_handler(signum,frame):raise TimeoutError('Audit hard wall deadline reached')
    previous=signal.signal(signal.SIGALRM,alarm_handler)
    signal.setitimer(signal.ITIMER_REAL,args.hard_seconds)
    try:
      model=Path(args.model).resolve();policy=Path(args.policy).resolve();input_hashes={str(model):digest(model),str(policy):digest(policy)}
      provenance=dict(model_source=str(model),policy_source=str(policy),input_sha256=input_hashes,source_sha256={str(p):digest(p) for p in [Path(__file__).resolve(),BACKEND/'scaling_core.py',BACKEND/'certified_decoder.py',BACKEND/'fast_decoder.py']},versions={name:importlib.metadata.version(name) for name in ['numpy','scipy','highspy']},argv=sys.argv)
      shutil.copyfile(model,out/'model.npz');shutil.copyfile(policy,out/'policy.npz');write_json(out/'provenance.json',provenance)
      T,Z,E,rows,leaf,replayed=load_and_replay(out/'model.npz',out/'policy.npz');state['input_replay']=replayed
      Q=len(T);remaining=deadline-time.monotonic();require(remaining>0,'Deadline reached in input validation')
      fr=StableDecoder(E,Q,time_limit=min(30.,remaining));rr,ww,meta=witness(E,np.eye(Q),fr)
      write_npz(out/'full_revelation_witness.npz',lower=np.asarray(rr['lower']),upper=np.asarray(rr['upper']),**ww);state['full_revelation']=rr;full_upper=min(1.,rr['upper'])
      decoder=StableDecoder(E,16,time_limit=min(30.,max(.001,deadline-time.monotonic())))
      checkpoint()
      for index in range(COUNT):
        remaining=deadline-time.monotonic()
        if remaining<=0:raise TimeoutError('Audit hard wall deadline reached')
        decoder.inner.time_limit=min(30.,remaining)
        F=target_kernel(T,Z,index);r,w,meta=witness(E,F,decoder)
        bounds.append((index,r));buffer.append((index,r,w,meta))
        if hardest is None or r['lower']>hardest[1]['lower']:hardest=(index,r,w)
        if hardest_upper is None or r['upper']>hardest_upper[1]['upper']:hardest_upper=(index,r,w)
        if len(buffer)==256:checkpoint()
      completed=True
      require(all(digest(p)==h for p,h in input_hashes.items()),'Source input changed during audit')
      state.update(status='complete',complete=True)
    except BaseException as error:
      state.update(status='partial_timeout' if isinstance(error,TimeoutError) else 'failed',complete=False,failure=dict(type=type(error).__name__,message=str(error)))
      write_json(out/'failure.json',dict(**state['failure'],traceback=traceback.format_exc(),completed_target_count=len(bounds)))
    finally:
      signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,previous)
      checkpoint();state['complete']=completed and state['status']=='complete';write_json(out/'result.json',state)
    print(json.dumps({k:v for k,v in state.items() if k!='chunks'},indent=2))
    return 0 if state['complete'] else (3 if state['status']=='partial_timeout' else 2)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--model',required=True);parser.add_argument('--policy',required=True);parser.add_argument('--out',required=True);parser.add_argument('--cpu',required=True,type=int);parser.add_argument('--hard-seconds',type=float,default=1800.)
    sys.exit(run(parser.parse_args()))
