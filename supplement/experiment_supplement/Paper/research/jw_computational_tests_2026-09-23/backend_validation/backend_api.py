"""Frozen adaptive adapter execution and complete numerical witness export.

No numerical packages are imported until load_backend is called. Artifacts are
numerical evidence; independent_audit.py provides a separately implemented replay.
"""
from pathlib import Path
from fractions import Fraction
import hashlib,json,sys,time
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'AGENTS.md').exists())
PREP=ROOT/'Paper/research/jw_adaptive_weights_2026-09-23'
sys.path.insert(0,str(PREP))
from frozen_adapter import load_backend,context_for,target_binding,solve_reweighted
from adaptive_weights import Objective,CutCache,canonical

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,data):
 p=Path(p);p.parent.mkdir(parents=True,exist_ok=True)
 tmp=p.with_suffix(p.suffix+'.tmp');tmp.write_text(json.dumps(canonical(data),indent=2,allow_nan=False)+'\n');tmp.replace(p)
def bootstrap():return load_backend(execution_authorized=True)
def bindings_for(targets):
 return [target_binding(str(t['id']),t['kernel'],'deterministic-observation-tree-v1') for t in targets]
def context(backend,g,model_sha,labels):return context_for(g,model_sha,labels)
def objective_for(ctx,targets,weights):return Objective.finite(ctx,bindings_for(targets),weights)
def pack_evaluation(np,ev,path):
 arrays={'lower':ev['lower'],'upper':ev['upper']}
 for j,w in enumerate(ev['witnesses']):
  for key,value in w.items():arrays[f'witness_{j}_{key}']=value
 for j,c in enumerate(ev['cuts']):
  for key in ['intercept','slope','alpha','b']:arrays[f'cut_{j}_{key}']=c[key]
 np.savez_compressed(path,**arrays)
def export(backend,folder,g,targets,model,metadata,result):
 """Export every master and decoder witness, including non-winning iterations."""
 folder=Path(folder);folder.mkdir(parents=True,exist_ok=True);np=backend.np
 started=time.perf_counter()
 np.savez_compressed(folder/'inputs.npz',T=model['T'],Z=model['Z'],raw=g.raw,
  leaf_index=g.leaf_index,**{f'target_{j}':t['kernel'] for j,t in enumerate(targets)})
 write(folder/'metadata.json',metadata)
 best=result.get('best')
 if best is not None:
  np.savez_compressed(folder/'policy.npz',rows=best['rows'],E=best['E'],leaf=best['leaf'])
  pack_evaluation(np,best['evaluated'],folder/'selected_decoders.npz')
 for i,ev in enumerate(result.get('evidence_to_export',[])):
  dest=folder/f'iteration_{i:03d}';dest.mkdir(exist_ok=True)
  np.savez_compressed(dest/'master.npz',**ev['master_arrays'])
  cp=ev['cut_prefix'];P=g.flow.shape[1]
  np.savez_compressed(dest/'cuts.npz',targets=[c['target'] for c in cp],
   intercepts=[c['intercept'] for c in cp],slopes=np.asarray([c['slope'] for c in cp]).reshape((-1,P)))
  np.savez_compressed(dest/'policy.npz',rows=ev['rows'],E=ev['E'])
  if ev.get('oracle') is not None:pack_evaluation(np,ev['oracle'],dest/'decoders.npz')
  write(dest/'availability.json',{'available_seconds':ev.get('available_seconds')})
 for name in ['cache','witness_store']:
  if name in result:write(folder/(name+'.json'),result[name])
 light={k:v for k,v in result.items() if k not in ['best','evidence_to_export','cache','witness_store']}
 light['export_seconds']=time.perf_counter()-started
 write(folder/'result.json',light)
 write(folder/'FILES.json',{str(p.relative_to(folder)):sha(p) for p in sorted(folder.rglob('*')) if p.is_file() and p.name!='FILES.json'})
 return light

def solve(backend,g,targets,objective,cache,*,model_sha,labels,seconds=40,gap=1e-6,witness_store=None):
 return solve_reweighted(backend,g,targets,objective,cache,model_sha256=model_sha,
  world_labels=labels,seconds=seconds,gap=gap,witness_store=witness_store,execution_authorized=True)
