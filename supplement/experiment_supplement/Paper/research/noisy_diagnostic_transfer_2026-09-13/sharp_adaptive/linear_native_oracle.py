#!/usr/bin/env python3
"""Arbitrary linear objectives on the frozen compressed native-face LP.

The LP still contains every reachable full-history policy-flow variable. Its
native constraints use sufficient signed-count compression, but objectives may
distinguish all208 reachable terminal histories. This supports testing a common
FULL-HISTORY decoder instead of imposing a common count decoder.
"""
from pathlib import Path
from fractions import Fraction as Q
import importlib.util
import json
import sys
import time

import numpy as np
from scipy.optimize import linprog

HERE=Path(__file__).resolve().parent
SPEC=importlib.util.spec_from_file_location('compressed_oracle_linear_native',HERE/'compressed_oracle.py')
CO=importlib.util.module_from_spec(SPEC);sys.modules[SPEC.name]=CO;SPEC.loader.exec_module(CO)
ESPEC=importlib.util.spec_from_file_location('exact_oracle_linear_native',HERE/'exact_oracle_certificate.py')
EXACT=importlib.util.module_from_spec(ESPEC);sys.modules[ESPEC.name]=EXACT;ESPEC.loader.exec_module(EXACT)


class TerminalPolicyOracle(CO.CompressedPolicyOracle):
    def __init__(self,cost_bound=.0072,exact_face=True):
        super().__init__(cost_bound,exact_face)
        self.terminal_histories=self.reachable[-1]
        self.terminal_indices=np.asarray([self.w[h] for h in self.terminal_histories])
        self.terminal_prefix_laws=np.asarray([self.bellman['prefix_laws'][h]
                                           for h in self.terminal_histories],dtype=float).T
        self.full_terminal_positions=np.asarray([self.histories.index(h) for h in self.terminal_histories])

    def optimize(self,coefficients,certificate_path=None,replay=False):
        """Compatible state objective entry point; defaults to no policy replay."""
        coefficients=np.asarray(coefficients,dtype=float)
        if coefficients.shape!=(len(self.states),):
            raise ValueError(f'Expected {len(self.states)} state coefficients')
        objective=np.zeros(len(self.lp.cost));objective[self.z]=coefficients
        result=self.optimize_linear(objective,certificate_path,replay)
        result['source_kernel']=result['compressed_source_kernel']
        return result

    maximize=optimize

    def optimize_terminal(self,coefficients,certificate_path=None,replay=False):
        coefficients=np.asarray(coefficients,dtype=float)
        if coefficients.shape!=(len(self.terminal_histories),):
            raise ValueError(f'Expected {len(self.terminal_histories)} reachable-terminal coefficients')
        objective=np.zeros(len(self.lp.cost));objective[self.terminal_indices]=coefficients
        return self.optimize_linear(objective,certificate_path,replay)

    def optimize_linear(self,objective,certificate_path=None,replay=False):
        """Maximize arbitrary objective*x; coefficients are in all857 LP variables."""
        objective=np.asarray(objective,dtype=float)
        if objective.shape!=(len(self.lp.cost),):
            raise ValueError(f'Expected {len(self.lp.cost)} LP coefficients')
        start=time.monotonic();c=-objective
        sol=linprog(c,A_eq=self.ae,b_eq=self.be,A_ub=self.au,b_ub=self.bu,
                    bounds=self.lp.bounds,method=CO.SEARCH.METHOD,options=CO.SEARCH.OPTIONS)
        seconds=time.monotonic()-start;self.calls+=1;self.total_seconds+=seconds
        if not sol.success:raise RuntimeError(sol.message)
        lo,hi=self.bounds.T
        dual=float(self.be@sol.eqlin.marginals+self.bu@sol.ineqlin.marginals+
                   lo@sol.lower.marginals+hi@sol.upper.marginals)
        residuals={'equality':float(np.max(abs(self.ae@sol.x-self.be),initial=0)),
                   'inequality':float(np.max(self.au@sol.x-self.bu,initial=0)),
                   'bounds':float(np.max(np.maximum(lo-sol.x,sol.x-hi),initial=0)),
                   'stationarity':float(np.max(abs(c-self.ae.T@sol.eqlin.marginals-
                                       self.au.T@sol.ineqlin.marginals-sol.lower.marginals-sol.upper.marginals),initial=0)),
                   'duality_gap':abs(float(sol.fun)-dual)}
        assert max(residuals.values())<=5e-8,residuals
        terminal=sol.x[self.terminal_indices]
        state=sol.x[self.z]
        reached_source=self.terminal_prefix_laws*terminal
        full=np.zeros((4,len(self.histories)));full[:,self.full_terminal_positions]=reached_source
        compressed=self.rays*state
        result={'value':-float(sol.fun),'dual_upper_bound':-dual,'solution':sol,
                'terminal_weights':terminal,'state_weights':state,
                'reachable_source_kernel':reached_source,'full_source_kernel':full,
                'compressed_source_kernel':compressed,'source_kernel':reached_source,
                'solver_seconds':seconds,'residuals':residuals,
                'native_epigraph_cost':.1*sum(sol.x[i] for i in self.deficit_indices.values())}
        if replay:
            actions=[]
            for layer in self.levels[:-1]:
                for h in layer:
                    row=np.zeros(3)
                    if h in self.w and sol.x[self.w[h]]>1e-12:
                        for a in range(3):
                            if (h,a) in self.x:row[a]=max(0.,sol.x[self.x[h,a]]/sol.x[self.w[h]])
                        if row.sum()>0:
                            row/=row.sum()
                        else:
                            row[self.bellman['allowed'][h][0]]=1.
                    else:row[self.bellman['allowed'][h][0]]=1.
                    actions.append(row)
            actions=np.asarray(actions);weights=CO.BASE.realization(self.levels,actions)
            replayed=CO.BASE.experiment(self.levels,{h:np.asarray(p,dtype=float)
                                         for h,p in self.bellman['prefix_laws'].items()},weights)
            residuals['policy_replay']=float(np.max(abs(full-replayed)))
            assert residuals['policy_replay']<=5e-8
            result.update(action_rows=actions,policy=actions,
                          realization_weights=np.asarray([weights[h] for layer in self.levels for h in layer]))
        if certificate_path is not None:
            self.lp.cost=c.tolist()
            arrays=CO.BASE.certificate_arrays(self.lp,sol,self.ae,self.au,self.be,self.bu)
            arrays.update(terminal_indices=self.terminal_indices,state_indices=self.z,
                          terminal_prefix_laws=self.terminal_prefix_laws,rays=self.rays,
                          terminal_weights=terminal,state_weights=state,
                          source_kernel=reached_source,full_source_kernel=full,
                          compressed_source_kernel=compressed)
            if replay:arrays.update(action_rows=result['action_rows'],realization_weights=result['realization_weights'])
            np.savez_compressed(certificate_path,**arrays)
        return result


class ExactLinearOracleCertificate(EXACT.ExactOracleCertificate):
    def certify_terminal(self,coefficients,result=None,max_denominator=10**9,include_witness=True):
        coefficients=list(map(EXACT.fraction,coefficients))
        assert len(coefficients)==len(self.oracle.terminal_indices)
        objective=[Q(0)]*self.variables
        for i,q in zip(self.oracle.terminal_indices,coefficients):objective[i]=q
        return self.certify_linear(objective,result,max_denominator,include_witness)

    def certify_linear(self,objective,result=None,max_denominator=10**9,include_witness=True):
        start=time.monotonic();objective=list(map(EXACT.fraction,objective))
        assert len(objective)==self.variables
        if result is None:result=self.oracle.optimize_linear(np.asarray(objective,dtype=float))
        sol=result['solution']
        lam=[Q(float(x)).limit_denominator(max_denominator) for x in sol.eqlin.marginals]
        mu=[min(Q(0),Q(float(x)).limit_denominator(max_denominator)) for x in sol.ineqlin.marginals]
        residual=[-q for q in objective]
        constant=sum(b*q for b,q in zip(self.be,lam))+sum(b*q for b,q in zip(self.bu,mu))
        for rows,multipliers in ((self.eq,lam),(self.ub,mu)):
            for row,multiplier in zip(rows,multipliers):
                if multiplier:
                    for j,value in row:residual[j]-=value*multiplier
        correction=sum(min(Q(0),r) for r in residual);lower=constant+correction
        report={'status':'exact_rational_lagrangian_upper','upper':str(-lower),
                'upper_float':float(-lower),'minimization_lower':str(lower),
                'lagrangian_constant':str(constant),'box_residual_correction':str(correction),
                'max_denominator':max_denominator,'max_objective':list(map(str,objective)),
                'numerical_maximum':float(result['value']),
                'certified_upper_minus_numeric':float(-lower)-float(result['value']),
                'seconds':time.monotonic()-start,
                'scope':'Upper for arbitrary linear objective on exact native-optimal policy LP; not a worst-deficiency certificate by itself.'}
        if include_witness:
            report.update(equality_multipliers=list(map(str,lam)),
                          inequality_multipliers=list(map(str,mu)),
                          stationarity_residual=list(map(str,residual)))
        return report


def smoke():
    oracle=TerminalPolicyOracle();certifier=ExactLinearOracleCertificate(oracle)
    old=CO.SEARCH.PolicyOracle(exact_face=True);rng=np.random.default_rng(9132026)
    reports=[]
    for k in range(3):
        coeff=[Q(int(x),1000) for x in rng.integers(-2000,2001,len(oracle.terminal_indices))]
        result=oracle.optimize_terminal(np.asarray(coeff,dtype=float),HERE/f'linear_native_smoke_{k}.npz',replay=True)
        full=np.zeros(625);full[oracle.full_terminal_positions]=np.asarray(coeff,dtype=float)
        ref=old.optimize(full)
        assert abs(ref['value']-result['value'])<=1e-8
        exact=certifier.certify_terminal(coeff,result)
        assert -1e-10<=exact['certified_upper_minus_numeric']<=1e-5
        reports.append({'value':result['value'],'old_value':ref['value'],
                        'new_seconds':result['solver_seconds'],'old_seconds':ref['solver_seconds'],
                        'residuals':result['residuals'],'exact':exact})
    report={'status':'passed_smoke','source_sha256':CO.SEARCH.digest(__file__),
            'compressed_oracle_sha256':CO.SEARCH.digest(HERE/'compressed_oracle.py'),
            'exact_helper_sha256':CO.SEARCH.digest(HERE/'exact_oracle_certificate.py'),
            'terminal_histories':oracle.terminal_histories,'terminal_indices':oracle.terminal_indices.tolist(),
            'tests':reports}
    CO.SEARCH.write_json(HERE/'linear_native_smoke.json',report)
    print(json.dumps([{k:r[k] for k in ('value','old_value','new_seconds','old_seconds','residuals')} for r in reports],indent=2))


if __name__=='__main__':smoke()
