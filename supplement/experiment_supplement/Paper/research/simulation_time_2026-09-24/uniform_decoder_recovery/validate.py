"""Bounded arithmetic and lazy-fallback tests; no numerical optimizer calls."""
import json
from pathlib import Path
import numpy as np
from known_decoder import KnownDecoderFirst


def validate():
    calls = []
    class Stub:
        def solve(self, F):
            calls.append('solve')
            return {'sentinel': True}, {}
    def fallback(E, Y):
        calls.append('construct')
        return Stub()
    E = np.array([[.3,.2,.1,.4],[.1,.1,.6,.2]])
    mapping = np.array([0,0,1,1]); F = np.column_stack([E[:,:2].sum(1),E[:,2:].sum(1)])
    wrapper = KnownDecoderFirst(E,2,fallback)
    r,w = wrapper.solve(F,mapping)
    assert not calls and not r['optimizer_called'] and r['upper'] < 1e-15
    assert np.max(abs(E@w['decoder']-F)) < 1e-15
    tests=['prefix decoder avoids backend construction']
    d=KnownDecoderFirst(E,4,fallback);r,w=d.solve(E)
    assert not calls and r['method']=='identity';tests.append('identity avoids backend construction')
    # A different target must not be accepted just because it has the right size.
    altered = np.array([[1.,0.],[0.,1.]])
    r,w=wrapper.solve(altered,mapping)
    assert r['optimizer_called'] and calls==['construct','solve'];tests.append('wrong prefix target falls back')
    wrapper.solve(altered,mapping)
    assert calls==['construct','solve','solve'];tests.append('fallback backend reused')
    try: wrapper.solve(F,np.array([0,0,1,2]))
    except ValueError: tests.append('invalid projection rejected')
    else: raise AssertionError('invalid projection accepted')
    try: wrapper.solve(F*2,mapping)
    except ValueError: tests.append('unnormalized target rejected')
    else: raise AssertionError('unnormalized target accepted')
    E0=np.column_stack([E[:,0],np.zeros(2),E[:,1:]])
    d=KnownDecoderFirst(E0,2,fallback);r,w=d.solve(F,np.array([0,1,0,1,1]))
    assert not r['optimizer_called'] and np.array_equal(w['source_indices'],[0,2,3,4]);tests.append('zero source columns preserve mapping')
    # An upper bound within a reporting threshold but outside the exact bracket
    # tolerance still invokes the optimizer in the primary audit interface.
    almost=F.copy();almost[:,0]+=.001;almost[:,1]-=.001
    r,w=wrapper.solve(almost,mapping)
    assert r['optimizer_called'];tests.append('threshold success is not mislabeled as closed bracket')
    return dict(status='passed',tests=tests,numerical_solver_calls=0)

if __name__=='__main__':
    result=validate();print(json.dumps(result,indent=2))
    Path(__file__).with_name('VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
