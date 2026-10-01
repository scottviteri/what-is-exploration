"""Numerical source coarsening with decoder/dual checks on ORIGINAL probabilities.

Only very small columns are merged into an existing signal. The resulting
experiment is a literal garbling; no policy or model is changed. Coarse decoder
rows are lifted back and the dual is evaluated on the original source, so every
accepted bracket still bounds the requested original deficiency.
"""
import time
import numpy as np
from fast_decoder import NativeDecoder
from scaling_core import TOL

class StableDecoder:
    def __init__(self,E,outputs,method='native-simplex',time_limit=120):
        started=time.perf_counter();E=np.asarray(E,dtype=float)
        self.keep=np.flatnonzero(np.max(E,axis=0)>0);self.E=E[:,self.keep]
        sizes=self.E.max(axis=0);mass=np.zeros(E.shape[0]);merged=[]
        for j in np.argsort(sizes):
            if sizes[j]>=1e-9:break
            trial=mass+self.E[:,j]
            if trial.max()<=TOL/20:merged.append(int(j));mass=trial
        removed=set(merged);retained=[j for j in range(self.E.shape[1]) if j not in removed]
        if not retained:raise ValueError('Source coarsening cannot remove every signal')
        destination=max(retained,key=lambda j:sizes[j]);where={j:i for i,j in enumerate(retained)}
        self.mapping=np.array([where[destination] if j in removed else where[j] for j in range(self.E.shape[1])])
        coarse=self.E[:,retained].copy();coarse[:,where[destination]]+=mass
        self.coarsening_bound=float(mass.max());self.merged_columns=len(merged);self.mass_by_world=mass
        self.inner=NativeDecoder(coarse,outputs,method,time_limit)
        self.build_seconds=time.perf_counter()-started
        self.import_reports=self.inner.import_reports

    def solve(self,F):
        report,w=self.inner.solve(F)
        G=w['decoder'][self.mapping];alpha=w['alpha'];b=w['b']
        upper=float(np.max(np.abs(self.E@G-F).sum(axis=1)/2))
        lower=float(np.sum(F*b)-np.max(self.E.T@b,axis=1).sum())
        if upper-lower>TOL or lower>upper+TOL:raise RuntimeError(f'Original-source coarsening certificate failed: {lower}, {upper}')
        if np.max(abs(G.sum(1)-1))>TOL or np.min(G)<0:raise RuntimeError('Lifted decoder invalid')
        report.update(coarse_lower=report['lower'],coarse_upper=report['upper'],
                      lower=lower,upper=upper,bracket=upper-lower,
                      merged_source_columns=self.merged_columns,coarsening_bound=self.coarsening_bound,
                      certificate_scope='Decoder and dual evaluated on original nonzero source columns',
                      residuals_scope='KKT residuals refer to the coarsened numerical LP, not the original LP')
        return report,dict(source_indices=self.keep,decoder=G,alpha=alpha,b=b,
                          source_merge_mapping=self.mapping,coarsening_mass_by_world=self.mass_by_world)
