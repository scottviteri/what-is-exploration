#!/usr/bin/env python3
import os
for k in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
from fractions import Fraction as F
import backend_api as api
from adaptive_weights import CutCache,Objective,RationalTarget,exact_native_kernel,digest
from frozen_adapter import target_binding
backend=api.bootstrap();np=backend.np
from independent_audit import audit
from rich_audit import check_rich
model={'T':np.ones((2,2,1,1)),'Z':np.array([[[[1.,0.]],[[1.,0.]]],[[[0.,1.]],[[1.,0.]]]])}
g=backend.core.geometry(model['T'],model['Z'],2);raw=backend.core.geometry(model['T'],model['Z'],1).raw
enc=[RationalTarget(2,2,1,1,k) for k in (0,1)]+[RationalTarget(2,2,1,2,1)]
targets=[{'id':e.key,'kernel':np.asarray(exact_native_kernel(e,[[F(float(v)) for v in row] for row in raw]),dtype=float)} for e in enc]
modelsha=digest({'analytic':'rational targets on read bit'});labels=[0,1];ctx=api.context(backend,g,modelsha,labels);bindings=[target_binding(e.key,t['kernel']) for e,t in zip(enc,targets)];eps=F(1,20);adaptive=[F(1,3)]*3
obj=Objective.rich(ctx,bindings,enc,dict(zip([e.key for e in enc],adaptive)),eps);cache=CutCache(ctx)
r=api.solve(backend,g,targets,obj,cache,model_sha=modelsha,labels=labels,seconds=10)
metadata={'t':2,'kind':'native_weighted','target_specs':[{'kind':'rational','key':e.key} for e in enc],'target_binding_ids':[b.identity for b in bindings],'weights':[str(w) for w in obj.weights],'rich_epsilon':str(eps),'adaptive_weights':[str(v) for v in adaptive]}
folder=api.HERE/'tiny'/'rational_rich';api.export(backend,folder,g,targets,model,metadata,r);a=audit(folder);b=check_rich(folder);api.write(folder/'audit.json',a);api.write(folder/'rich_audit.json',b)
assert r['status']=='converged_numerically';assert a['upper']<1e-6
api.write(api.HERE/'RATIONAL_CHECKS.json',{'status':'passed','numerical':a,'exact_tail':b,'frozen_source_sha256':{n:api.sha(api.HERE/n) for n in ['rational_checks.py','rich_audit.py']}})
print('passed rational rich audit')
