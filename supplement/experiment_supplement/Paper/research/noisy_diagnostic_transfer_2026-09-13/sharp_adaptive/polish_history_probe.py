#!/usr/bin/env python3
"""Bounded development probe: exact feasible-vertex cuts and decoder projection.

Requires optional python-flint from /tmp/native_exact_polish. Produces candidate
artifacts only; exact all-event certification must be run separately.
"""
from pathlib import Path
from fractions import Fraction as Q
import importlib.util,json,sys,time
sys.path.insert(0,'/tmp/native_exact_polish')
from flint import fmpq_mat
import numpy as np
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('linear_native_polish_probe',HERE/'linear_native_oracle.py')
LN=importlib.util.module_from_spec(spec);sys.modules[spec.name]=LN;spec.loader.exec_module(LN)

def rq(x):return Q(str(x))

def solve_affine(rows,rhs,n,reference):
    A=fmpq_mat([[str(v) for v in row]+[str(b)] for row,b in zip(rows,rhs)])
    R,rank=A.rref();pivots=[]
    for i in range(rank):
        j=next(j for j in range(n+1) if R[i,j])
        if j==n:raise ValueError('inconsistent exact system')
        pivots.append(j)
    free=[j for j in range(n) if j not in pivots]
    x=list(reference)
    for i,j in enumerate(pivots):x[j]=rq(R[i,n])-sum(rq(R[i,k])*x[k] for k in free)
    return x,rank

def recover(oracle,helper,sol):
    for tol in (1e-7,1e-9,1e-11):
        try:
            free=[j for j,x in enumerate(sol.x) if tol<x<1-tol]
            fixed={j:Q(int(x>.5)) for j,x in enumerate(sol.x) if j not in free}
            pos={j:k for k,j in enumerate(free)};rows=[];rhs=[]
            active=list(zip(helper.eq,helper.be))
            slack=oracle.bu-oracle.au@sol.x
            active+= [(r,b) for r,b,s in zip(helper.ub,helper.bu,slack) if s<=tol]
            for row,b in active:
                v=[Q(0)]*len(free)
                for j,q in row:
                    if j in fixed:b-=q*fixed[j]
                    else:v[pos[j]]=q
                if any(v):rows.append(v);rhs.append(b)
                elif b:raise ValueError('inconsistent fixed coordinates')
            xfree,rank=solve_affine(rows,rhs,len(free),[Q(float(sol.x[j])).limit_denominator(10**8) for j in free])
            x=[fixed[j] if j in fixed else xfree[pos[j]] for j in range(helper.variables)]
            assert min(x)>=0 and max(x)<=1
            assert all(sum(q*x[j] for j,q in row)==b for row,b in zip(helper.eq,helper.be))
            assert all(sum(q*x[j] for j,q in row)<=b for row,b in zip(helper.ub,helper.bu))
            return x,{'free':len(free),'rank':rank,'tolerance':tol}
        except Exception as e:last=str(e)
    raise ValueError('exact primal recovery failed: '+last)

def main():
    start=time.monotonic();oracle=LN.TerminalPolicyOracle();helper=LN.ExactLinearOracleCertificate(oracle)
    data=json.loads((HERE/'native_history_certificate.json').read_text())
    G=[[Q(q) for q in row] for row in data['decoder']];T=[[Q(q) for q in row] for row in data['target_rows']]
    P=[oracle.bellman['prefix_laws'][h] for h in oracle.terminal_histories]
    critical=[(e['world'],e['mask']) for e in data['events'] if e['event_error_upper_float']>.072-1e-8]
    cuts=[];records=[];failures=[]
    # Adjust only entries comfortably inside[0,1], exchanging mass with each row's largest entry.
    center=[list(row) for row in G]
    directions=[]
    for h,row in enumerate(center):
        anchor=max(range(5),key=lambda y:row[y])
        for y,q in enumerate(row):
            if y!=anchor and Q(1,10**7)<q<Q(1)-Q(1,10**7):directions.append((h,y,anchor))
    for iteration in range(5):
        for theta,mask in critical:
            coef=[p[theta]*sum(row[y] for y in range(5) if mask>>y&1) for p,row in zip(P,G)]
            sol=oracle.optimize_terminal(np.asarray(coef,float))['solution']
            try:x,info=recover(oracle,helper,sol)
            except Exception as e:failures.append({'iteration':iteration,'world':theta,'mask':mask,'error':str(e)});continue
            E=[p[theta]*x[j] for p,j in zip(P,oracle.terminal_indices)]
            rhs=Q(9,125)+sum(T[theta][y] for y in range(5) if mask>>y&1)
            cut=[e*int(mask>>y&1) for e in E for y in range(5)]
            if cut not in [c for c,b in cuts]:cuts.append((cut,rhs))
            records.append({'iteration':iteration,'world':theta,'mask':mask,'recovery':info})
        rows=[];rhs=[]
        for cut,b in cuts:
            rows.append([cut[h*5+y]-cut[h*5+a] for h,y,a in directions])
            rhs.append(b-sum(c*q for c,q in zip(cut,[q for row in center for q in row])))
        try:shift,rank=solve_affine(rows,rhs,len(directions),[Q(0)]*len(directions))
        except Exception as e:failures.append({'iteration':iteration,'projection_error':str(e)});break
        G=[list(row) for row in center]
        for (h,y,a),q in zip(directions,shift):G[h][y]+=q;G[h][a]-=q
        if min(q for row in G for q in row)<0:
            failures.append({'iteration':iteration,'projection_error':'negative decoder coordinate'});break
        violations=[];upper=0.
        for theta in range(4):
            for mask in range(1,31):
                coef=[p[theta]*sum(row[y] for y in range(5) if mask>>y&1) for p,row in zip(P,G)]
                result=oracle.optimize_terminal(np.asarray(coef,float))
                value=result['dual_upper_bound']-float(sum(T[theta][y] for y in range(5) if mask>>y&1));upper=max(upper,value)
                if value>.072+1e-11:violations.append((theta,mask))
        print(json.dumps({'iteration':iteration,'cuts':len(cuts),'projection_rank':rank,'numeric_upper':upper,'violations':len(violations),'seconds':time.monotonic()-start}),flush=True)
        out=dict(status='candidate_exact_stochastic_decoder',scope='Development candidate only; requires separate all-event certificate.',
                 terminal_histories=oracle.terminal_histories,decoder=[[str(q) for q in row] for row in G],
                 float_decoder=np.asarray(G,float).tolist(),target_rows=data['target_rows'],target_count_groups=data['target_count_groups'],
                 numeric_upper=upper,records=records,failures=failures,iteration=iteration,
                 source_sha256=LN.CO.SEARCH.digest(__file__),input_sha256=LN.CO.SEARCH.digest(HERE/'native_history_certificate.json'))
        LN.CO.SEARCH.write_json(HERE/'native_history_polish_candidate.json',out)
        if not violations:break
        critical=violations
    LN.CO.SEARCH.write_json(HERE/'history_polish_probe_results.json',{'status':'development_probe_finished','records':records,'failures':failures,'seconds':time.monotonic()-start})

if __name__=='__main__':main()
