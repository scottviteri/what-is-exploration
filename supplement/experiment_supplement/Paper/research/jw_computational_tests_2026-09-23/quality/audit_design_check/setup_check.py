from pathlib import Path
import sys,json,hashlib,numpy as np
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parents[2]/'target_selection_2026-09-23'
sys.path.insert(0,str(SOURCE))
import scaling_core as core
m=core.random_model(2026096900,worlds=4);g=core.geometry(m['T'],m['Z'],3)
np.savez_compressed(HERE/'model.npz',T=m['T'],Z=m['Z'])
weights={():1.};aw=np.zeros(42)
for i,h in enumerate(g.decisions):
 for a in (0,1):
  aw[2*i+a]=weights[h]*.5
  for o in (0,1):weights[h+((a,o),)]=aw[2*i+a]
E,rows,leaf=core.replay(g,aw);np.savez_compressed(HERE/'uniform_policy.npz',E=E,rows=rows,leaf=leaf)
rng=np.random.default_rng(923991);desired=rng.dirichlet([1.,1.],size=21);desired[3]=[1,0];desired[17]=[0,1]
weights={():1.}
for i,h in enumerate(g.decisions):
 for a in (0,1):
  aw[2*i+a]=weights[h]*desired[i,a]
  for o in (0,1):weights[h+((a,o),)]=aw[2*i+a]
E,rows,leaf=core.replay(g,aw);np.savez_compressed(HERE/'adaptive_policy.npz',E=E,rows=rows,leaf=leaf)
wrong=E.copy();wrong[:,[0,1]]=wrong[:,[1,0]];np.savez_compressed(HERE/'bad_policy.npz',E=wrong,rows=rows,leaf=leaf)
(HERE/'PROTOCOL.json').write_text(json.dumps(dict(seed=2026096900,worlds=4,concentration=1,states=3,design_only=True,tests=['full32768 uniform audit then independent validation','adaptive nonuniform policy with null columns; short forced timeout then partial validation','stochastic but wrong E must be rejected','saved witness tampering must be rejected'],source_sha256=hashlib.sha256((SOURCE/'scaling_core.py').read_bytes()).hexdigest()),indent=2)+'\n')
