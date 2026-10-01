"""Recovery backend with direct deficiency witnesses at the unchanged 2e-7 gap.

Old LP KKT diagnostics are retained. Acceptance is based on a feasible decoder
and feasible bounded decision loss, evaluated against ORIGINAL source columns.
This is a different numerical backend; no old failure is reclassified as passed.
"""
import numpy as np
import scaling_core as core
from fast_decoder import NativeDecoder
from certified_decoder import StableDecoder
import highspy,time

class WitnessNative(NativeDecoder):
    def solve(self,F):
        started=time.perf_counter();deadline=started+self.time_limit
        F=np.asarray(F,dtype=float)
        if F.shape!=(self.Q,self.Y) or not np.isfinite(F).all() or np.min(F)<0 or np.max(abs(F.sum(1)-1))>core.TOL:
            raise ValueError('Invalid target experiment')
        cost=self.c.copy();cost[self.cost_indices]=-F.ravel();attempts=[]
        for mode,solver,cap in [('retained','simplex',1.),('cold','simplex',3.),('cold','ipm',self.time_limit)]:
            remaining=deadline-time.perf_counter()
            if remaining<=0:break
            ts=time.perf_counter();attempt=dict(mode=mode,solver=solver)
            try:
                if mode=='retained':
                    h=self.h;h.setOptionValue('solver',solver)
                    if h.changeColsCost(len(self.cost_indices),self.cost_indices,cost[self.cost_indices])!=highspy.HighsStatus.kOk:raise RuntimeError('Cost update failed')
                else:h=self._new_solver(solver,cost)
                remaining=deadline-time.perf_counter()
                if remaining<=0:raise TimeoutError('Setup exceeded call budget')
                h.setOptionValue('time_limit',h.getRunTime()+min(cap,remaining))
                h.run();status=h.getModelStatus();attempt['status']=h.modelStatusToString(status)
                if status!=highspy.HighsModelStatus.kOptimal:raise RuntimeError(attempt['status'])
                report,witness=self._extract(h,cost,F)
                attempt.update(success=True,seconds=time.perf_counter()-ts);attempts.append(attempt)
                self.h=h;self.solver='simplex'
                report.update(method='explicit-witness-'+solver,attempts=attempts,fallback_used=len(attempts)>1,
                              total_seconds=time.perf_counter()-started,solve_seconds=sum(x['seconds'] for x in attempts))
                return report,witness
            except Exception as exc:
                attempt.update(success=False,error=repr(exc),seconds=time.perf_counter()-ts);attempts.append(attempt)
        raise RuntimeError('Recovery decoder failed: '+repr(attempts))
    def _extract(self,h,cost,F):
        sol=h.getSolution();info=h.getInfo()
        x=np.asarray(sol.col_value);y=np.asarray(sol.row_dual);z=np.asarray(sol.col_dual)
        if not all(np.isfinite(v).all() for v in [x,y,z]):raise RuntimeError('Nonfinite solver witness')
        raw=-y[1+self.Q*self.Y:].reshape(self.X,self.Y)
        G=np.maximum(raw,0.);den=G.sum(1,keepdims=True)
        if np.any(den<=0):raise RuntimeError('Empty repaired decoder row')
        G/=den
        alpha=np.maximum(x[:self.Q],0.)
        if alpha.sum()<=0:raise RuntimeError('Empty decision prior')
        alpha/=alpha.sum()
        b=np.clip(x[self.Q:self.Q+self.Q*self.Y].reshape(self.Q,self.Y),0.,alpha[:,None])
        upper=float(np.max(abs(self.E@G-F).sum(1))/2)
        lower=float(np.sum(F*b)-np.max(self.E.T@b,axis=1).sum())
        residuals=dict(decoder_normalization=float(np.max(abs(G.sum(1)-1))),
                       decoder_nonnegative=float(max(0.,-G.min())),
                       alpha_normalization=float(abs(alpha.sum()-1)),
                       alpha_nonnegative=float(max(0.,-alpha.min())),
                       loss_nonnegative=float(max(0.,-b.min())),
                       loss_bounded=float(max(0.,(b-alpha[:,None]).max())),
                       interval_order=float(max(0.,lower-upper)),interval_gap=float(max(0.,upper-lower)))
        if not np.isfinite([lower,upper]).all() or max(residuals.values())>core.TOL:
            raise RuntimeError(f'Explicit deficiency witnesses failed: {residuals}')
        # Keep numerical stationarity diagnostics; they are not the theorem used
        # to certify this repaired decoder/decision-loss interval.
        stationarity=float(np.max(abs(cost-self.A.T@y-z)))
        report=dict(lower=lower,upper=upper,bracket=upper-lower,residuals=residuals,
                    raw_decoder_row_residual=float(np.max(abs(raw.sum(1)-1))),
                    raw_decoder_negative=float(max(0.,-raw.min())),decoder_repair_max=float(np.max(abs(G-raw))),
                    lp_stationarity_diagnostic=stationarity,
                    explicit_witness_acceptance=True,
                    simplex_iterations=int(info.simplex_iteration_count),ipm_iterations=int(info.ipm_iteration_count))
        return report,dict(source_indices=self.keep.copy(),decoder=G,alpha=alpha,b=b)

class RecoveryDecoder(StableDecoder):
    def __init__(self,E,outputs,method='native-ipm',time_limit=30):
        super().__init__(E,outputs,method,time_limit)
        coarse=self.inner.E.copy()
        self.inner=WitnessNative(coarse,outputs,method,time_limit)
    def solve(self,F):
        r,w=super().solve(F)
        r['residuals_scope']='Feasible decoder/decision-loss bounds; LP diagnostics retained separately.'
        return r,w
