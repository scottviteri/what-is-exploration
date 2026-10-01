"""Independent saved-audit validation; no producer or LP-backend import.

Reconstructs physical target laws and policy records separately, then replays
original-probability primal/dual witnesses for every saved target.
"""
import os
for _key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[_key]='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import argparse,hashlib,json,time
import numpy as np
TOL=2e-7

def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def require(condition,message):
    if not condition:raise ValueError(message)
def write_json(path,value):
    temp=path.with_suffix('.tmp');temp.write_text(json.dumps(value,indent=2,allow_nan=False)+'\n');temp.replace(path)

def independent_input(model,policy):
    T=model['T'];Z=model['Z'];E=policy['E'];rows=policy['rows'];leaf=policy['leaf'];Q,_,S,_=T.shape
    require(T.shape==(Q,2,S,S) and Z.shape==(Q,2,S,2),'Invalid model shape')
    require(E.shape==(Q,64) and rows.shape==(21,2) and leaf.shape==(64,),'Invalid t3 policy shape')
    for name,array in [('T',T),('Z',Z),('E',E),('rows',rows),('leaf',leaf)]:require(np.isfinite(array).all() and array.min()>=0,'Invalid '+name)
    for name,array in [('T',T),('Z',Z),('E',E),('rows',rows)]:require(abs(array.sum(-1)-1).max()<=1e-10,'Nonstochastic '+name)
    replayed=np.zeros_like(E);weights=np.zeros(64)
    for column in range(64):
      state=np.zeros((Q,S));state[:,0]=1;prefix=0;weight=1.
      for depth in range(3):
        digit=(column//(4**(2-depth)))%4;a=digit//2;o=digit%2;offset=(4**depth-1)//3
        weight*=rows[offset+prefix,a]
        # Matrix products in a per-world loop, distinct from producer einsum.
        state=np.asarray([(state[q]@T[q,a])*Z[q,a,:,o] for q in range(Q)])
        prefix=4*prefix+digit
      weights[column]=weight;replayed[:,column]=state.sum(1)*weight
    error=max(float(abs(replayed-E).max()),float(abs(weights-leaf).max()))
    require(error<=1e-10,'Independent model/policy replay mismatch')
    return T,Z,E,error

def native_target(T,Z,index):
    Q,_,S,_=T.shape;F=np.zeros((Q,16));initial=np.zeros((Q,S));initial[:,0]=1
    def visit(state,depth,node,column):
      if depth==4:F[:,column]=state.sum(1);return
      action=(int(index)>>(14-node))&1
      predicted=np.asarray([state[q]@T[q,action] for q in range(Q)])
      visit(predicted*Z[:,action,:,0],depth+1,2*node+1,2*column)
      visit(predicted*Z[:,action,:,1],depth+1,2*node+2,2*column+1)
    visit(initial,0,0,0);return F

def cache_native_targets(T,Z):
    """Independently propagate all 4^4 controlled histories once.

    Action choices are imposed, so the 256 columns are controlled history
    likelihoods, not one joint history probability law. A target selects the
    sixteen columns compatible with its action tree. No planner/producer code
    or saved target array is consulted while constructing this cache.
    """
    Q,_,S,_=T.shape
    initial=np.zeros((Q,S));initial[:,0]=1
    states=[initial]
    for depth in range(4):
      following=[]
      for state in states:
        for action in (0,1):
          predicted=np.asarray([state[q]@T[q,action] for q in range(Q)])
          for observation in (0,1):
            following.append(predicted*Z[:,action,:,observation])
      states=following
    laws=np.stack([state.sum(1) for state in states],axis=1)
    # Each entry is the base-four action/observation history for one tree and
    # one observation word. Action bits are in the original breadth-first order.
    trees=np.arange(32768,dtype=np.uint16)[:,None]
    observations=np.arange(16,dtype=np.uint16)[None,:]
    nodes=np.zeros((32768,16),dtype=np.uint16)
    columns=np.zeros_like(nodes)
    for depth in range(4):
      observation=(observations>>(3-depth))&1
      action=(trees>>(14-nodes))&1
      columns=4*columns+2*action+observation
      nodes=2*nodes+1+observation
    return laws,columns

def cached_native_target(cache,index):
    laws,columns=cache
    return laws[:,columns[int(index)]]

def check_witness(E,F,G,alpha,b,expected_lower,expected_upper):
    Q,X=E.shape;Y=F.shape[1]
    require(F.shape==(Q,Y) and G.shape==(X,Y) and alpha.shape==(Q,) and b.shape==(Q,Y),'Witness shape mismatch')
    require(all(np.isfinite(x).all() for x in [F,G,alpha,b]),'Nonfinite witness')
    feasibility=max(float(abs(G.sum(1)-1).max()),float(max(0,-G.min())),float(abs(alpha.sum()-1)),float(max(0,-alpha.min())),float(max(0,-b.min())),float(np.maximum(b-alpha[:,None],0).max()))
    upper=float(np.abs(E@G-F).sum(1).max()/2);lower=float(np.sum(F*b)-sum(np.max(E[:,x]@b) for x in range(X)))
    disagreement=max(abs(upper-float(expected_upper)),abs(lower-float(expected_lower)))
    require(feasibility<=1e-12 and lower<=upper+1e-10 and upper-lower<=TOL and disagreement<=1e-12,'Invalid original-probability witness or reported bracket')
    return dict(lower=lower,upper=upper,gap=upper-lower,feasibility=feasibility,replay_disagreement=disagreement)

def validate(folder):
    start=time.perf_counter();folder=Path(folder).resolve();result=json.loads((folder/'result.json').read_text());provenance=json.loads((folder/'provenance.json').read_text())
    require(digest(folder/'model.npz')==provenance['input_sha256'][provenance['model_source']],'Model copy hash mismatch')
    require(digest(folder/'policy.npz')==provenance['input_sha256'][provenance['policy_source']],'Policy copy hash mismatch')
    for snapshot in provenance.get('source_snapshots',[]):
      path=folder/snapshot;require(digest(path) in provenance['source_sha256'].values(),'Execution source snapshot hash mismatch')
    with np.load(folder/'model.npz',allow_pickle=False) as m,np.load(folder/'policy.npz',allow_pickle=False) as p:T,Z,E,input_error=independent_input(m,p)
    target_cache=cache_native_targets(T,Z)
    full_upper=1.;global_source='universal TV bound';full_path=folder/'full_revelation_witness.npz'
    if full_path.exists():
      with np.load(full_path,allow_pickle=False) as w:
        require(np.max(abs(w['F']-np.eye(len(T))))<=1e-12,'Full-revelation target mismatch')
        checked=check_witness(E,w['F'],w['G'],w['alpha'],w['b'],w['lower'],w['upper']);full_upper=min(1.,checked['upper']);global_source='full-revelation decoder'
    ids=[];records=[];max_feas=0.;max_gap=0.;max_error=0.;checksums=[]
    for chunk in result['chunks']:
      path=folder/chunk['file'];require(digest(path)==chunk['sha256'],'Witness chunk hash mismatch')
      with np.load(path,allow_pickle=False) as archive:
        w={key:archive[key] for key in ['indices','F','G','alpha','b','lower','upper']}
        require(all(len(w[key])==chunk['count'] for key in ['indices','F','G','alpha','b','lower','upper']),'Chunk count mismatch')
        for i,F,G,a,b,lo,up in zip(w['indices'],w['F'],w['G'],w['alpha'],w['b'],w['lower'],w['upper']):
          i=int(i);require(0<=i<32768,'Invalid target ID');require(np.max(abs(F-cached_native_target(target_cache,i)))<=1e-12,'Independent target kernel mismatch')
          r=check_witness(E,F,G,a,b,lo,up);records.append(r);ids.append(i)
          max_feas=max(max_feas,r['feasibility']);max_gap=max(max_gap,r['gap']);max_error=max(max_error,r['replay_disagreement'])
      checksums.append(dict(file=chunk['file'],sha256=chunk['sha256']))
    require(ids==list(range(len(ids))),'Target IDs are not the unique completed prefix')
    require(len(ids)==result['completed_target_count'],'Completion count mismatch')
    complete=len(ids)==32768
    require(not result['complete'] or (complete and result['status']=='complete'),'False complete-audit assertion')
    if ids:
      with np.load(folder/'bounds.npz',allow_pickle=False) as w:
        require(np.array_equal(w['indices'],np.asarray(ids)),'Bounds IDs disagree')
        require(np.max(abs(w['lower']-np.asarray([r['lower'] for r in records])))<=1e-12 and np.max(abs(w['upper']-np.asarray([r['upper'] for r in records])))<=1e-12,'Compact bounds disagree')
      for name,key,field in [('hardest_witness.npz','hardest_lower_target','lower'),('largest_upper_witness.npz','largest_upper_target','upper')]:
        with np.load(folder/name,allow_pickle=False) as w:
          i=int(w['index']);require(i==result[key],'Hardest witness ID mismatch');require(abs(records[i][field]-max(r[field] for r in records))<=1e-12,'Hardest witness is not extremal')
          require(np.max(abs(w['F']-cached_native_target(target_cache,i)))<=1e-12,'Hardest target mismatch');check_witness(E,w['F'],w['G'],w['alpha'],w['b'],w['lower'],w['upper'])
    lower=max([0.]+[r['lower'] for r in records]);upper=min(full_upper,max(r['upper'] for r in records)) if complete else full_upper
    require(abs(lower-result['audit_lower'])<=1e-12 and abs(upper-result['audit_upper'])<=1e-12,'Global audit bounds disagree')
    require(lower<=upper+TOL,'Global interval is empty')
    return dict(status='passed',audit=str(folder),complete=complete,reported_status=result['status'],completed_target_count=len(ids),expected_target_count=32768,model_policy_replay_error=input_error,max_witness_feasibility=max_feas,max_per_target_gap=max_gap,max_replay_disagreement=max_error,audit_lower=lower,audit_upper=upper,global_upper_source=global_source if not complete else 'complete target uppers and full-revelation upper',validation_seconds=time.perf_counter()-start,scope='Independent physical-model replay, native target reconstruction, and original-probability decoder/dual witness replay. Floating-point evidence, not exact arithmetic or eventual exploration.',checked_chunks=checksums)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--audit',required=True);parser.add_argument('--output');parser.add_argument('--cpu',type=int)
    args=parser.parse_args()
    if args.cpu is not None:os.sched_setaffinity(0,{args.cpu})
    output=Path(args.output) if args.output else Path(args.audit)/'validation.json'
    try:
      value=validate(args.audit);write_json(output,value);print(json.dumps({k:v for k,v in value.items() if k!='checked_chunks'},indent=2))
    except Exception as exc:
      write_json(output,dict(status='failed',error=repr(exc)));raise
