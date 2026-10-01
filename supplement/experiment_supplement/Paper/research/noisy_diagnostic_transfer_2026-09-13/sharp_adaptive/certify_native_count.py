#!/usr/bin/env python3
"""Exact bound for the iter11 common-count decoder checkpoint.

Rationalize one stochastic decoder, then certify every world/event support
function on the actual native-optimal policy face with repaired exact duals.
"""
from fractions import Fraction as Q
from pathlib import Path
import importlib.util,json,sys,time
import numpy as np
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('linear_native_count_certificate',HERE/'linear_native_oracle.py')
LN=importlib.util.module_from_spec(spec);sys.modules[spec.name]=LN;spec.loader.exec_module(LN)

def rational_decoder(raw,denominator):
    rows=[]
    for row in raw:
        qs=[Q(float(max(0.,x))).limit_denominator(denominator) for x in row]
        largest=max(range(len(qs)),key=lambda y:qs[y])
        qs[largest]=1-sum(q for y,q in enumerate(qs) if y!=largest)
        assert min(qs)>=0 and sum(qs)==1
        rows.append(qs)
    return rows

def main():
    start=time.monotonic();checkpoint=HERE/'native_count_checkpoint.npz'
    checkpoint_hash=LN.CO.SEARCH.digest(checkpoint)
    with np.load(checkpoint) as data:
        raw=data['decoder'].copy();states=data['states'].copy()
    oracle=LN.TerminalPolicyOracle();certifier=LN.ExactLinearOracleCertificate(oracle)
    assert np.array_equal(states,np.asarray(oracle.states))
    candidates=[]
    for denominator in (10**4,10**6,10**8):
        decoder=rational_decoder(raw,denominator)
        defect=float(np.max(np.sum(abs(np.asarray(decoder,dtype=float)-raw),axis=1))/2)
        candidates.append({'denominator':denominator,'max_row_tv_change':defect})
    chosen=next(c for c in candidates if c['max_row_tv_change']<=1e-8)
    decoder=rational_decoder(raw,chosen['denominator']);T=oracle.targets['adaptive_L']['exact']
    events=[];upper=Q(0)
    for theta in range(4):
        for mask in range(64):
            coefficients=[ray[theta]*sum(row[y] for y in range(6) if mask>>y&1)
                          for ray,row in zip(oracle.exact_rays,decoder)]
            result=oracle.optimize(np.asarray(coefficients,dtype=float))
            exact=certifier.certify(coefficients,result)
            target=sum(T[theta][y] for y in range(6) if mask>>y&1)
            bound=Q(exact['upper'])-target;upper=max(upper,bound)
            events.append({'world':theta,'mask':mask,'target_mass':str(target),
                           'event_error_upper':str(bound),'event_error_upper_float':float(bound),
                           'support_certificate':exact})
        print(json.dumps({'world_finished':theta,'certified_upper_so_far':float(upper),
                          'seconds':time.monotonic()-start}),flush=True)
    report={'status':'passed_exact_rational_upper','scope':
            'A single world-independent decoder from signed-count state, valid for every policy with exact native_repeats cost S<=9/1250. Its bound is an upper on the worst policy-specific adaptive deficiency, not an assertion that the common decoder or bound is optimal.',
            'source_sha256':LN.CO.SEARCH.digest(__file__),
            'linear_oracle_sha256':LN.CO.SEARCH.digest(HERE/'linear_native_oracle.py'),
            'compressed_oracle_sha256':LN.CO.SEARCH.digest(HERE/'compressed_oracle.py'),
            'exact_helper_sha256':LN.CO.SEARCH.digest(HERE/'exact_oracle_certificate.py'),
            'exact_model_sha256':LN.CO.SEARCH.digest(HERE/'compressed_oracle_exact_model.json'),
            'checkpoint_sha256':checkpoint_hash,'checkpoint_path':checkpoint.name,
            'checkpoint_iteration':11,'H':4,'noise':['1/10','1/10'],'native_cost_bound':'9/1250',
            'states':oracle.states,'rays':[[str(q) for q in row] for row in oracle.exact_rays],
            'decoder':[[str(q) for q in row] for row in decoder],
            'target_rows':[[str(q) for q in row] for row in T],
            'target_groups':oracle.targets['adaptive_L']['groups'],
            'target_full_rows':[[str(q) for q in row] for row in oracle.targets['adaptive_L']['full']],
            'denominator_candidates':candidates,'chosen_denominator':chosen['denominator'],
            'exact_upper':str(upper),'exact_upper_float':float(upper),
            'clean_exact_upper':'923/12500','clean_exact_upper_float':.07384,
            'events':events,'oracle_calls':oracle.calls,'run_seconds':time.monotonic()-start}
    assert upper<=Q(923,12500)
    assert LN.CO.SEARCH.digest(checkpoint)==checkpoint_hash
    LN.CO.SEARCH.write_json(HERE/'native_count_certificate.json',report)
    print(json.dumps({k:report[k] for k in ('exact_upper','exact_upper_float','oracle_calls','run_seconds')},indent=2))

if __name__=='__main__':main()
