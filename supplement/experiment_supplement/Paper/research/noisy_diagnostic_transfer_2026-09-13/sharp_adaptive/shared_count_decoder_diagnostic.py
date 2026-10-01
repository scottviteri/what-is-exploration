#!/usr/bin/env python3
"""Common signed-count decoder across the saved optimal collectors only."""
from pathlib import Path
import importlib.util,json,sys,time
import numpy as np
from scipy.optimize import linprog
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('compressed_oracle_shared_count',HERE/'compressed_oracle.py')
CO=importlib.util.module_from_spec(spec);sys.modules[spec.name]=CO;spec.loader.exec_module(CO)

def main():
    start=time.monotonic();oracle=CO.CompressedPolicyOracle();lp=CO.BASE.LP()
    previous=json.loads((HERE/'shared_decoder_diagnostic.json').read_text())
    with np.load(HERE/'shared_decoder_diagnostic.npz') as data:full=data['source_kernels']
    E=np.stack([full[:,:,oracle.history_state==s].sum(axis=2) for s in range(len(oracle.states))],axis=2)
    omitted=float(np.max(np.abs(E.sum(axis=2)-full.sum(axis=2))))
    assert omitted<1e-10
    T=oracle.target_kernels['adaptive_L'];Y=T.shape[1]
    error=lp.var(1.);G=np.asarray([[lp.var() for _ in range(Y)] for _ in oracle.states])
    for row in G:lp.row({i:1 for i in row},1,True)
    for source in E:
        for theta in range(4):
            errors=[]
            for y in range(Y):
                e=lp.var();errors.append(e)
                terms={G[s,y]:source[theta,s] for s in range(len(oracle.states))}
                lp.row(terms|{e:-1},T[theta,y]);lp.row({i:-v for i,v in terms.items()}|{e:-1},-T[theta,y])
            lp.row({i:.5 for i in errors}|{error:-1},0)
    ae,au=lp.matrix(lp.eq),lp.matrix(lp.ub)
    be,bu=(np.asarray([v for _,v in rows]) for rows in (lp.eq,lp.ub))
    sol=linprog(lp.cost,A_eq=ae,b_eq=be,A_ub=au,b_ub=bu,bounds=lp.bounds,method=CO.SEARCH.METHOD,options=CO.SEARCH.OPTIONS)
    assert sol.success,sol.message
    lo,hi=np.asarray(lp.bounds).T
    dual=float(be@sol.eqlin.marginals+bu@sol.ineqlin.marginals+lo@sol.lower.marginals+hi@sol.upper.marginals)
    residuals={'equality':float(np.max(abs(ae@sol.x-be),initial=0)),
               'inequality':float(np.max(au@sol.x-bu,initial=0)),
               'bounds':float(np.max(np.maximum(lo-sol.x,sol.x-hi),initial=0)),
               'duality_gap':abs(float(sol.fun)-dual)}
    decoder=sol.x[G];errs=np.sum(abs(E@decoder-T),axis=2)/2
    arrays=CO.BASE.certificate_arrays(lp,sol,ae,au,be,bu)
    arrays.update(source_kernels=E,decoder=decoder,decoder_indices=G,target_kernel=T,states=np.asarray(oracle.states))
    certificate=HERE/'shared_count_decoder_diagnostic.npz';np.savez_compressed(certificate,**arrays)
    report={'status':'completed_float64_diagnostic','scope':'One common 28-state signed-count decoder on the 12 selected saved collectors only; no full-face conclusion.',
            'source_sha256':CO.SEARCH.digest(__file__),'oracle_sha256':CO.SEARCH.digest(HERE/'compressed_oracle.py'),
            'input_sha256':CO.SEARCH.digest(HERE/'shared_decoder_diagnostic.npz'),
            'selected_collectors':previous['selected_collectors'],'states':oracle.states,
            'common_decoder_error':float(sol.fun),'common_decoder_dual_lower':dual,
            'source_world_errors':errs.tolist(),'omitted_off_face_mass':omitted,'residuals':residuals,
            'variables':len(lp.cost),'equalities':len(lp.eq),'inequalities':len(lp.ub),
            'run_seconds':time.monotonic()-start,'certificate_path':certificate.name,
            'certificate_sha256':CO.SEARCH.digest(certificate)}
    assert max(residuals.values())<1e-8
    CO.SEARCH.write_json(HERE/'shared_count_decoder_diagnostic.json',report)
    print(json.dumps({k:report[k] for k in ('common_decoder_error','common_decoder_dual_lower','omitted_off_face_mass','residuals','run_seconds')},indent=2))

if __name__=='__main__':main()
