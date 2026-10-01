"""Bounded known-answer and corruption checks, not new campaign outcomes."""
from common import *
from worker import solve,MARGIN
from verify import verify_arrays
import shutil,time

def test_model(noise):
    T=np.zeros((4,2,2,2));Z=np.zeros((4,2,2,2))
    for q in range(4):
        for a in (0,1):
            bit=(q>>(1-a))&1
            T[q,a,:,bit]=1.
            for s in (0,1):
                eta=0. if a==0 else noise
                Z[q,a,s,s]=1-eta;Z[q,a,s,1-s]=eta
    return T,Z

def run():
    start=time.monotonic();out=HERE/'validation';out.mkdir(exist_ok=False);answers=[]
    T,Z=test_model(.1);F=raw_law(T,Z,[((1,0),),((1,1),)])
    for method in ('information','brier'):
        folder=out/method;solve(T,Z,1,F,method,.02,folder,20.)
        r=verify_arrays(T,Z,1,F,method,.02,MARGIN,folder)
        strong=1. if method=='information' else .25
        weak=1-(-.1*np.log2(.1)-.9*np.log2(.9)) if method=='information' else .16
        expected=(1-.02/.4)*(strong-weak)
        assert r['reward_regret_lower']-1e-9<=expected<=r['reward_regret_upper']+1e-9
        assert r['reward_regret_upper']-r['reward_regret_lower']<2e-7
        answers.append(dict(test=method+'_analytic_positive_cost',expected=expected,**r))
    for name,noise,singleton in [('symmetric_zero_cost',0.,False),('singleton_vacuity',.1,True)]:
        T,Z=test_model(noise)
        if singleton:T=T[:1];Z=Z[:1]
        F=raw_law(T,Z,[((1,0),),((1,1),)])
        folder=out/name;solve(T,Z,1,F,'information',.02,folder,20.)
        r=verify_arrays(T,Z,1,F,'information',.02,MARGIN,folder)
        assert r['reward_regret_upper']<1e-10
        answers.append(dict(test=name,**r))
    T,Z=test_model(.1);F=raw_law(T,Z,[((1,0),),((1,1),)])
    for name in ('corrupt_decoder','corrupt_cost','wrong_target_binding'):
        folder=out/name;shutil.copytree(out/'information',folder)
        if name=='corrupt_decoder':
            with np.load(folder/'policy_decoder.npz') as z:arrays={k:z[k].copy() for k in z.files}
            arrays['G'][0]*=0.;save(folder/'policy_decoder.npz',**arrays)
        elif name=='corrupt_cost':
            with np.load(folder/'lp.npz') as z:arrays={k:z[k].copy() for k in z.files}
            arrays['cost'][0]+=.01;save(folder/'lp.npz',**arrays)
        try:
            verify_arrays(T,Z,1,F[:,::-1] if name=='wrong_target_binding' else F,'information',.02,MARGIN,folder)
        except AssertionError:answers.append(dict(test=name,status='rejected_as_expected'))
        else:raise AssertionError(name+' accepted')
    report=dict(status='passed',created_utc=now(),seconds=time.monotonic()-start,tests=answers,
                file_sha256={str(p.relative_to(HERE)):sha(p) for p in sorted(out.rglob('*.npz'))})
    write(HERE/'VALIDATION.json',report);print(json.dumps(report),flush=True)

if __name__=='__main__':
    os.sched_setaffinity(0,{11});run()
