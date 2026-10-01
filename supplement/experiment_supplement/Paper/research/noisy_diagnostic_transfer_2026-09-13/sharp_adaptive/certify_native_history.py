#!/usr/bin/env python3
"""Exact common-full-history decoder bounds; denominator search is explicit.

Every event uses a rational decoder and exact native-face LP dual repair. A
positive residual above .072 is retained, never rounded down to sharpness.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse,importlib.util,json,sys,time
import numpy as np
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('linear_native_history_certificate',HERE/'linear_native_oracle.py')
LN=importlib.util.module_from_spec(spec);sys.modules[spec.name]=LN;spec.loader.exec_module(LN)

def rational_decoder(raw,denominator):
    rows=[]
    for row in raw:
        qs=[Q(float(max(0.,x))).limit_denominator(denominator) for x in row]
        j=max(range(len(qs)),key=lambda y:qs[y]);qs[j]=1-sum(q for y,q in enumerate(qs) if y!=j)
        assert min(qs)>=0 and sum(qs)==1;rows.append(qs)
    return rows

def main(args):
    start=time.monotonic();input_path=HERE/args.input
    input_hash=LN.CO.SEARCH.digest(input_path);data=json.loads(input_path.read_text())
    raw=np.asarray(data['float_decoder']);oracle=LN.TerminalPolicyOracle();helper=LN.ExactLinearOracleCertificate(oracle)
    assert data['terminal_histories']==[[list(e) for e in h] for h in oracle.terminal_histories]
    groups=[[0],[1],[2,4],[3],[5]];original=oracle.targets['adaptive_L']['exact']
    assert all(row[4]==2*row[2] for row in original)
    T=[[sum(row[y] for y in group) for group in groups] for row in original]
    P=[oracle.bellman['prefix_laws'][h] for h in oracle.terminal_histories]
    candidates=[];best=None;best_events=None;best_decoder=None
    for denominator in args.denominators:
        decoder=rational_decoder(raw,denominator);events=[];upper=Q(0);worst=None
        for theta in range(4):
            for mask in range(32):
                coefficients=[p[theta]*sum(row[y] for y in range(5) if mask>>y&1) for p,row in zip(P,decoder)]
                result=oracle.optimize_terminal(np.asarray(coefficients,dtype=float))
                exact=helper.certify_terminal(coefficients,result)
                target=sum(T[theta][y] for y in range(5) if mask>>y&1)
                bound=Q(exact['upper'])-target
                if bound>upper:upper=bound;worst=[theta,mask]
                events.append({'world':theta,'mask':mask,'target_mass':str(target),
                               'event_error_upper':str(bound),'event_error_upper_float':float(bound),
                               'support_certificate':exact})
        row={'denominator':denominator,'max_row_tv_change':float(np.max(np.sum(abs(np.asarray(decoder,float)-raw),axis=1))/2),
             'exact_upper':str(upper),'exact_upper_float':float(upper),'worst_event':worst,
             'seconds_elapsed':time.monotonic()-start}
        candidates.append(row)
        print(json.dumps({k:row[k] for k in ('denominator','max_row_tv_change','exact_upper_float','worst_event','seconds_elapsed')}),flush=True)
        if best is None or upper<best:
            best=upper;best_events=events;best_decoder=decoder;chosen=denominator
    ceiling=Q(-((-best.numerator*10**12)//best.denominator),10**12)
    assert ceiling>=best
    report={'status':'passed_exact_rational_upper','scope':
            'One common full-history decoder on every policy with exact native_repeats cost S<=9/1250. A bound above9/125 is not a proof of sharpness.',
            'source_sha256':LN.CO.SEARCH.digest(__file__),
            'linear_oracle_sha256':LN.CO.SEARCH.digest(HERE/'linear_native_oracle.py'),
            'compressed_oracle_sha256':LN.CO.SEARCH.digest(HERE/'compressed_oracle.py'),
            'exact_helper_sha256':LN.CO.SEARCH.digest(HERE/'exact_oracle_certificate.py'),
            'exact_model_sha256':LN.CO.SEARCH.digest(HERE/'compressed_oracle_exact_model.json'),
            'input_path':input_path.name,'input_sha256':input_hash,
            'H':4,'noise':['1/10','1/10'],'native_cost_bound':'9/1250',
            'terminal_histories':oracle.terminal_histories,'terminal_indices':oracle.terminal_indices.tolist(),
            'terminal_prefix_laws':[[str(q) for q in row] for row in P],
            'decoder':[[str(q) for q in row] for row in best_decoder],
            'target_rows':[[str(q) for q in row] for row in T],'target_count_groups':groups,
            'target_count_rows':[[str(q) for q in row] for row in original],
            'target_full_rows':[[str(q) for q in row] for row in oracle.targets['adaptive_L']['full']],
            'target_full_groups':oracle.targets['adaptive_L']['groups'],
            'five_to_six_lift':[['1','0','0','0','0','0'],['0','1','0','0','0','0'],
                                ['0','0','1/3','0','2/3','0'],['0','0','0','1','0','0'],['0','0','0','0','0','1']],
            'denominator_candidates':candidates,'chosen_denominator':chosen,
            'exact_upper':str(best),'exact_upper_float':float(best),
            'clean_exact_upper':str(ceiling),'clean_exact_upper_float':float(ceiling),
            'sharp_at_9_over_125':best<=Q(9,125),'events':best_events,
            'oracle_calls':oracle.calls,'run_seconds':time.monotonic()-start}
    LN.CO.SEARCH.write_json(HERE/args.output,report)
    print(json.dumps({k:report[k] for k in ('chosen_denominator','exact_upper_float','clean_exact_upper','sharp_at_9_over_125','oracle_calls','run_seconds')},indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--input',default='native_history_stable_decoder.json')
    parser.add_argument('--output',default='native_history_certificate.json')
    parser.add_argument('--denominators',type=int,nargs='+',default=[1000,10000,1000000,100000000]);main(parser.parse_args())
