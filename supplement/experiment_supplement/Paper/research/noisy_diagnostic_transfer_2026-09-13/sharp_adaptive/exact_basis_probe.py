#!/usr/bin/env python3
"""Development exact HiGHS-basis dual reconstruction for one native-face LP."""
from pathlib import Path
from fractions import Fraction as Q
import sys,time,json
sys.path.insert(0,'/tmp/native_exact_polish')
import highspy
from flint import fmpq_mat
import numpy as np
from scipy.sparse import vstack
from linear_native_oracle import TerminalPolicyOracle,ExactLinearOracleCertificate,CO
HERE=Path(__file__).resolve().parent

def exact_basis(oracle,helper,coefficient):
    start=time.monotonic();A=vstack([oracle.ae,oracle.au],format='csr');m,n=A.shape
    lp=highspy.HighsLp();lp.num_col_=n;lp.num_row_=m
    lp.col_cost_=np.asarray(coefficient,float);lp.col_lower_=np.zeros(n);lp.col_upper_=np.ones(n)
    lp.row_lower_=np.r_[oracle.be,np.full(len(oracle.bu),-highspy.kHighsInf)]
    lp.row_upper_=np.r_[oracle.be,oracle.bu]
    lp.a_matrix_.format_=highspy.MatrixFormat.kRowwise
    lp.a_matrix_.start_=A.indptr;lp.a_matrix_.index_=A.indices;lp.a_matrix_.value_=A.data
    highs=highspy.Highs();highs.setOptionValue('output_flag',False);highs.setOptionValue('solver','simplex')
    highs.setOptionValue('primal_feasibility_tolerance',1e-10);highs.setOptionValue('dual_feasibility_tolerance',1e-10)
    highs.passModel(lp);highs.run();basis=highs.getBasis()
    basiccols=[j for j,s in enumerate(basis.col_status) if s==highspy.HighsBasisStatus.kBasic]
    basicrows=[i for i,s in enumerate(basis.row_status) if s==highspy.HighsBasisStatus.kBasic]
    assert len(basiccols)+len(basicrows)==m
    # Basic row variables yield y_i=0. Eliminate them before exact solve.
    active=[i for i in range(m) if i not in basicrows];pos={i:k for k,i in enumerate(active)}
    exactrows=helper.eq+helper.ub
    transpose=[[Q(0)]*len(active) for _ in basiccols];bpos={j:k for k,j in enumerate(basiccols)}
    for i in active:
        for j,q in exactrows[i]:
            if j in bpos:transpose[bpos[j]][pos[i]]=q
    B=fmpq_mat([[str(q) for q in row] for row in transpose]);rhs=fmpq_mat([[str(coefficient[j])] for j in basiccols])
    ysmall=B.solve(rhs);y=[Q(0)]*m
    for i,k in pos.items():y[i]=Q(str(ysmall[k,0]))
    residual=list(coefficient)
    for row,mult in zip(exactrows,y):
        if mult:
            for j,q in row:residual[j]-=q*mult
    mu=y[len(helper.eq):]
    # If numerical basis was slightly dual infeasible, clip inequality multipliers
    # and recompute box correction: still exact, but may lose sharpness.
    clipped=False
    for k,v in enumerate(mu):
        if v>0:
            clipped=True;i=len(helper.eq)+k;y[i]=Q(0)
            for j,q in exactrows[i]:residual[j]+=q*v
    rhsall=helper.be+helper.bu
    constant=sum(q*v for q,v in zip(rhsall,y));correction=sum(min(Q(0),r) for r in residual)
    return {'upper':str(-constant-correction),'upper_float':float(-constant-correction),
            'constant':str(constant),'correction':str(correction),'equality_multipliers':list(map(str,y[:len(helper.eq)])),
            'inequality_multipliers':list(map(str,y[len(helper.eq):])),'stationarity_residual':list(map(str,residual)),
            'max_objective':list(map(str,[-q for q in coefficient])),
            'basis_size':m,'reduced_basis_size':len(active),'inequality_sign_clipped':clipped,
            'numeric_objective':highs.getObjectiveValue(),'seconds':time.monotonic()-start}

def main():
    oracle=TerminalPolicyOracle();helper=ExactLinearOracleCertificate(oracle)
    path=HERE/'native_history_minnorm_candidate.json'
    if not path.exists():path=HERE/'native_history_certificate.json'
    d=json.loads(path.read_text());G=[[Q(q) for q in row] for row in d['decoder']];T=[[Q(q) for q in row] for row in d['target_rows']]
    out=[]
    for theta,mask in [(0,22),(3,11),(2,21)]:
        coefficient=[Q(0)]*helper.variables
        for h,row,j in zip(oracle.terminal_histories,G,oracle.terminal_indices):coefficient[j]=-oracle.bellman['prefix_laws'][h][theta]*sum(row[y] for y in range(5) if mask>>y&1)
        r=exact_basis(oracle,helper,coefficient);target=sum(T[theta][y] for y in range(5) if mask>>y&1)
        r.update(world=theta,mask=mask,target_mass=str(target),event_error_upper=str(Q(r['upper'])-target),event_error_upper_float=float(Q(r['upper'])-target))
        out.append(r);print(json.dumps({k:r[k] for k in ('world','mask','event_error_upper_float','basis_size','reduced_basis_size','inequality_sign_clipped','seconds')}),flush=True)
    CO.SEARCH.write_json(HERE/'exact_basis_probe_results.json',{'scope':'Development exact basis reconstruction; limited events, not a complete upper.','input_path':path.name,'input_sha256':CO.SEARCH.digest(path),'events':out})

if __name__=='__main__':main()
