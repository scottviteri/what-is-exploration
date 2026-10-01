#!/usr/bin/env python3
"""Exact rational upper certificates for the compressed policy oracle.

For min c*x subject to Ax=b, Bx<=d, 0<=x<=1, choose ANY rational lambda
and nonpositive rational mu. With r=c-A'lambda-B'mu,

    min c*x >= b*lambda+d*mu+sum_i min(0,r_i).

Thus numerical dual multipliers can be rationalized without assuming exact
stationarity. The box residual term certifies the remaining error exactly.
The maximization oracle uses c=-state_coefficients, so negate this lower bound.
LP data are recovered from the exact coefficient alphabet used by the model,
not by unverified generic rounding of arbitrary floating point matrices.
"""
from fractions import Fraction as Q
from pathlib import Path
import importlib.util
import json
import sys
import time

import numpy as np

HERE=Path(__file__).resolve().parent
SPEC=importlib.util.spec_from_file_location('compressed_oracle_exact_certificate',HERE/'compressed_oracle.py')
CO=importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name]=CO
SPEC.loader.exec_module(CO)


def fraction(value):
    if isinstance(value,Q):return value
    if isinstance(value,(int,np.integer)):return Q(int(value))
    if isinstance(value,str):return Q(value)
    raise TypeError('Exact coefficients must be Fraction, integer, or rational strings; floats are not accepted')


class ExactOracleCertificate:
    def __init__(self,oracle):
        self.oracle=oracle
        self.alphabet={}
        def register(q):
            q=Q(q)
            for signed in (q,-q):
                key=float(signed)
                if key in self.alphabet:
                    assert self.alphabet[key]==signed,(key,self.alphabet[key],signed)
                self.alphabet[key]=signed
        for q in (0,1,Q(1,2),Q(9,125)):
            register(q)
        for row in oracle.exact_rays:
            for q in row:register(q)
        for h in oracle.reachable[-1]:register(max(oracle.bellman['prefix_laws'][h]))
        for target in oracle.targets.values():
            for row in target['exact']:
                for q in row:register(q)
        def exact_rows(matrix):
            matrix=matrix.tocsr()
            return [[(int(matrix.indices[k]),self.alphabet[float(matrix.data[k])])
                     for k in range(matrix.indptr[i],matrix.indptr[i+1])]
                    for i in range(matrix.shape[0])]
        self.eq=exact_rows(oracle.ae);self.ub=exact_rows(oracle.au)
        self.be=[self.alphabet[float(x)] for x in oracle.be]
        self.bu=[self.alphabet[float(x)] for x in oracle.bu]
        assert np.array_equal(oracle.bounds,np.tile([0.,1.],(len(oracle.lp.cost),1)))
        self.variables=len(oracle.lp.cost)

    def certify(self,coefficients,result=None,max_denominator=10**9,include_witness=True):
        """Return an exact upper for max coefficients*state_weights.

        coefficients must be exact Fraction/int/string values in oracle.states
        order. result may be the corresponding oracle.optimize result. It is
        safe even if the supplied result optimized another objective: any dual
        multipliers yield a feasible Lagrangian lower after residual repair.
        """
        start=time.monotonic()
        coefficients=list(map(fraction,coefficients))
        assert len(coefficients)==len(self.oracle.states)
        if result is None:
            result=self.oracle.optimize(np.asarray(coefficients,dtype=float))
        sol=result['solution']
        lam=[Q(float(x)).limit_denominator(max_denominator) for x in sol.eqlin.marginals]
        mu=[min(Q(0),Q(float(x)).limit_denominator(max_denominator)) for x in sol.ineqlin.marginals]
        residual=[Q(0)]*self.variables
        for index,q in zip(self.oracle.z,coefficients):residual[index]=-q
        constant=sum(b*q for b,q in zip(self.be,lam))+sum(b*q for b,q in zip(self.bu,mu))
        for rows,multipliers in ((self.eq,lam),(self.ub,mu)):
            for row,multiplier in zip(rows,multipliers):
                if multiplier:
                    for j,value in row:residual[j]-=value*multiplier
        correction=sum(min(Q(0),r) for r in residual)
        lower=constant+correction
        report={'status':'exact_rational_lagrangian_upper','upper':str(-lower),
                'upper_float':float(-lower),'minimization_lower':str(lower),
                'lagrangian_constant':str(constant),'box_residual_correction':str(correction),
                'box_residual_correction_float':float(correction),
                'maximum_stationarity_residual':str(max(map(abs,residual),default=Q(0))),
                'max_denominator':max_denominator,
                'coefficients':list(map(str,coefficients)),
                'numerical_maximum':float(result['value']),
                'certified_upper_minus_numeric':float(-lower)-float(result['value']),
                'seconds':time.monotonic()-start,
                'scope':'Upper for the exact native-optimal compressed policy LP; feasibility of this bound does not claim numerical primal optimality.'}
        if include_witness:
            report.update(equality_multipliers=list(map(str,lam)),
                          inequality_multipliers=list(map(str,mu)),
                          stationarity_residual=list(map(str,residual)))
        return report

    def export_model(self,path):
        report={'source_sha256':CO.SEARCH.digest(__file__),
                'oracle_sha256':CO.SEARCH.digest(HERE/'compressed_oracle.py'),
                'coefficient_recovery':'Exact known coefficient alphabet; every stored float must equal the float encoding of a unique declared rational.',
                'variables':self.variables,'states':self.oracle.states,
                'state_indices':self.oracle.z.tolist(),
                'equalities':[[[j,str(q)] for j,q in row] for row in self.eq],
                'inequalities':[[[j,str(q)] for j,q in row] for row in self.ub],
                'equality_rhs':list(map(str,self.be)),'inequality_rhs':list(map(str,self.bu)),
                'bounds':['0','1']}
        CO.SEARCH.write_json(path,report)


def smoke():
    oracle=CO.CompressedPolicyOracle();helper=ExactOracleCertificate(oracle)
    helper.export_model(HERE/'compressed_oracle_exact_model.json')
    rng=np.random.default_rng(9132026)
    reports=[]
    for _ in range(3):
        coefficients=[Q(int(x),1000) for x in rng.integers(-2000,2001,len(oracle.states))]
        result=oracle.optimize(np.asarray(coefficients,dtype=float))
        certificate=helper.certify(coefficients,result)
        assert certificate['certified_upper_minus_numeric']>=-1e-10
        assert certificate['certified_upper_minus_numeric']<=1e-5
        reports.append(certificate)
    CO.SEARCH.write_json(HERE/'exact_oracle_certificate_smoke.json',{
        'status':'passed_exact_certificate_smoke','source_sha256':CO.SEARCH.digest(__file__),
        'model_sha256':CO.SEARCH.digest(HERE/'compressed_oracle_exact_model.json'),'tests':reports})
    print(json.dumps([{k:r[k] for k in ('upper_float','numerical_maximum',
        'certified_upper_minus_numeric','box_residual_correction_float','seconds')} for r in reports],indent=2))


if __name__=='__main__':smoke()
