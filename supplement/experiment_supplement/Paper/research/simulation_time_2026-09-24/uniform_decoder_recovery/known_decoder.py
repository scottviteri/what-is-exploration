"""Try explicit stochastic decoders before lazily creating the general LP backend.

Only a two-sided bracket with the unchanged tolerance bypasses the optimizer.
A positive but small upper bound is not silently promoted to an exact deficiency.
The caller supplies prefix maps from its history ordering; sizes alone do not
establish a prefix relationship. Every candidate is evaluated on original laws.
"""
import time
import numpy as np


class KnownDecoderFirst:
    def __init__(self, E, outputs, fallback_factory, tolerance=2e-7):
        self.E = np.asarray(E, dtype=float).copy()
        self.Y = int(outputs)
        if self.E.ndim != 2 or min(self.E.shape) == 0 or self.Y != outputs or self.Y < 1:
            raise ValueError('Invalid experiment dimensions')
        if not np.isfinite(self.E).all() or self.E.min() < 0 or np.max(abs(self.E.sum(1)-1)) > 1e-10:
            raise ValueError('Invalid source law')
        if not np.isfinite(tolerance) or tolerance <= 0:
            raise ValueError('Invalid tolerance')
        self.tolerance = tolerance
        self.keep = np.flatnonzero(self.E.max(0) > 0)
        self.factory = fallback_factory
        self.backend = None

    def solve(self, F, source_to_target=None):
        start = time.perf_counter()
        F = np.asarray(F, dtype=float)
        if F.shape != (len(self.E), self.Y) or not np.isfinite(F).all() or F.min() < 0 or np.max(abs(F.sum(1)-1)) > 1e-10:
            raise ValueError('Invalid target law')
        candidates = []
        if source_to_target is not None:
            mapping = np.asarray(source_to_target)
            if mapping.shape != (self.E.shape[1],) or not np.issubdtype(mapping.dtype, np.integer) or mapping.min() < 0 or mapping.max() >= self.Y:
                raise ValueError('Invalid supplied record map')
            candidates.append(('explicit_record_projection', mapping))
        if self.E.shape[1] == self.Y:
            candidates.append(('identity', np.arange(self.Y)))
        attempted = []
        for name, mapping in candidates:
            G = np.zeros((len(self.keep), self.Y))
            G[np.arange(len(self.keep)), mapping[self.keep]] = 1.
            upper = float(np.max(abs(self.E[:, self.keep] @ G - F).sum(1))/2)
            attempted.append(dict(method=name, upper=upper))
            # Nonnegativity of deficiency is certified by this zero decision loss.
            if upper <= self.tolerance:
                alpha = np.full(len(F), 1/len(F))
                b = np.zeros_like(F)
                return dict(lower=0., upper=upper, bracket=upper, method=name,
                            optimizer_called=False, attempted_known_decoders=attempted,
                            total_seconds=time.perf_counter()-start,
                            certificate_scope='Explicit decoder and zero lower witness evaluated on original source.'), dict(
                                source_indices=self.keep.copy(), decoder=G, alpha=alpha, b=b)
        # Constructing a solver can itself be expensive; defer it until necessary.
        if self.backend is None:
            self.backend = self.factory(self.E, self.Y)
        report, witness = self.backend.solve(F)
        report = dict(report, optimizer_called=True, attempted_known_decoders=attempted,
                      total_seconds_with_shortcuts=time.perf_counter()-start)
        return report, witness
