#!/usr/bin/env python3
"""Exact-feasible count/majority common-repair certificates via event duals.

Float64 LPs search for a decoder and marginal potentials. Rational decoder
normalization, potential clipping and exact intercept reconstruction certify
feasibility; the exported rational certificate does not claim LP optimality.
The full event family of an exactly equivalent sufficient target encoding,
including empty/full events, is retained. Explicit disjoint uniform lifts
recover the literal target and preserve total variation exactly.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from fractions import Fraction as Q
import hashlib
from itertools import product
import json
from math import comb
from pathlib import Path
import platform
import sys
import time
import traceback
import warnings

import numpy as np
import scipy
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

HERE = Path(__file__).resolve().parent
WORLDS = tuple(product((0, 1), repeat=2))
NOISES = ((Q(1, 10), Q(1, 10)), (Q(1, 4), Q(1, 4)), (Q(1, 10), Q(3, 10)))
TARGETS = ("LR", "LLL", "RRR", "LLR", "LRR", "adaptive_L")
DESIGN_LOSSES = (Q(0), Q(1, 1000), Q(1, 100), Q(1, 20), Q(1, 10))
SOURCES = ("majority3", "count3")
OPTIONS = {"primal_feasibility_tolerance": 1e-9, "dual_feasibility_tolerance": 1e-9,
           "ipm_optimality_tolerance": 1e-10}
METHOD = "highs-ipm"
DENOMINATOR = 10**9
NUMERICAL_TOLERANCE = 2e-7


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    path = Path(path); temporary = path.with_suffix(path.suffix+".tmp")
    temporary.write_text(json.dumps(value, indent=2, allow_nan=False)+"\n")
    temporary.replace(path)


def rational(value):
    return Q(float(value)).limit_denominator(DENOMINATOR)


def diagnostic_rows(eps, source):
    result = []
    for side in (0, 1):
        rows = []
        for theta in WORLDS:
            probability_one = 1-eps[side] if theta[side] else eps[side]
            counts = [Q(comb(3, k))*probability_one**k*(1-probability_one)**(3-k) for k in range(4)]
            rows.append(counts if source == "count3" else [sum(counts[:2]), sum(counts[2:])])
        assert all(sum(row)==1 and min(row)>=0 for row in rows)
        result.append(rows)
    return result


def target_rows(eps, word):
    H = 3 if word == "adaptive_L" else len(word)
    outputs = list(product((0, 1), repeat=H)); rows = []
    for theta in WORLDS:
        row = []
        for observations in outputs:
            schedule = ("LLL" if observations[0]==0 else "LRR") if word == "adaptive_L" else word
            probability = Q(1)
            for action, observed in zip(schedule, observations):
                side = int(action == "R")
                probability *= 1-eps[side] if observed == theta[side] else eps[side]
            row.append(probability)
        assert sum(row)==1 and min(row)>=0
        rows.append(row)
    return rows, outputs


def compressed_target(eps, word):
    full, sequences = target_rows(eps, word)
    groups = {}; labels = []
    for index, y in enumerate(sequences):
        key = ((sum(y),) if word in ("LLL", "RRR") else
               (y[0]+y[1], y[2]) if word == "LLR" else
               (y[0], y[1]+y[2]) if word in ("LRR", "adaptive_L") else tuple(y))
        if key not in groups:
            groups[key] = []; labels.append(key)
        groups[key].append(index)
    cells = [groups[label] for label in labels]
    compressed = [[sum(row[y] for y in cell) for cell in cells] for row in full]
    lift = [[Q(int(y in cell), len(cell)) for y in range(len(sequences))] for cell in cells]
    mapping = [next(g for g, cell in enumerate(cells) if y in cell) for y in range(len(sequences))]
    # C is deterministic, U is uniform on disjoint cells, U C = Id.
    assert sorted(y for cell in cells for y in cell) == list(range(len(sequences)))
    for theta in range(4):
        for cell in cells:
            assert all(full[theta][y] == full[theta][cell[0]] for y in cell)
        for y in range(len(sequences)):
            assert sum(compressed[theta][g]*lift[g][y] for g in range(len(cells))) == full[theta][y]
    assert all(sum(lift[g][y] for y in cells[h]) == int(g == h)
               for g,h in product(range(len(cells)), repeat=2))
    return compressed, labels, {"groups": cells, "group_labels": [list(x) for x in labels],
             "full_to_compressed": mapping, "uniform_lift": [[str(v) for v in row] for row in lift]}, full, sequences


def subset_sums(row):
    values = [Q(0)]*(1 << len(row))
    for mask in range(1, len(values)):
        low = mask & -mask
        values[mask] = values[mask ^ low]+row[low.bit_length()-1]
    return values


class SparseConstraints:
    def __init__(self, n):
        self.n=n; self.rr=[]; self.cc=[]; self.vv=[]; self.rhs=[]

    def add(self, entries, rhs=0.):
        r = len(self.rhs)
        for c, value in entries:
            if value:
                self.rr.append(r); self.cc.append(c); self.vv.append(value)
        self.rhs.append(float(rhs))

    def matrix(self):
        return coo_matrix((self.vv, (self.rr, self.cc)), shape=(len(self.rhs), self.n)).tocsr()


def search(eps, source, word, design_s, failure_path):
    start = time.monotonic()
    (left, right) = diagnostic_rows(eps, source)
    targets, outputs, compression, full_targets, full_outputs = compressed_target(eps, word)
    nl, nr, Y = len(left[0]), len(right[0]), len(targets[0])
    masks = 1 << Y; block_size=nl+nr+1
    dsize=nl*nr*Y; intercept_index=dsize; slope_index=dsize+1; first_block=dsize+2
    n=first_block+4*masks*block_size
    cost=np.zeros(n); cost[intercept_index]=1; cost[slope_index]=float(design_s)
    bounds=[(0.,1.)]*dsize+[(0.,None),(0.,None)]+[(None,None)]*(n-first_block)
    eq=SparseConstraints(n); ub=SparseConstraints(n)
    for i in range(nl*nr):
        eq.add([(i*Y+y,1.) for y in range(Y)],1.)
    blocks=[]
    float_targets=np.asarray(targets,float)
    for theta in range(4):
        target_events=subset_sums(targets[theta])
        for mask in range(masks):
            base=first_block+(theta*masks+mask)*block_size
            u=list(range(base,base+nl)); v=list(range(base+nl,base+nl+nr)); t=base+nl+nr
            event=[y for y in range(Y) if mask & (1 << y)]
            for index in u+v:
                ub.add([(index,1.),(slope_index,-.25)])
                ub.add([(index,-1.),(slope_index,-.25)])
            for i,j in product(range(nl),range(nr)):
                ub.add([((i*nr+j)*Y+y,1.) for y in event]+[(u[i],-1.),(v[j],-1.),(t,-1.)])
            ub.add([(t,1.),(intercept_index,-1.)]+
                   [(u[i],float(left[theta][i])) for i in range(nl)]+
                   [(v[j],float(right[theta][j])) for j in range(nr)],float(target_events[mask]))
            blocks.append((theta,mask,u,v,t))
    ae,au=eq.matrix(),ub.matrix(); be=np.asarray(eq.rhs); bu=np.asarray(ub.rhs)
    build_seconds=time.monotonic()-start
    solve_start=time.monotonic()
    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter("always")
        sol=linprog(cost,A_eq=ae,b_eq=be,A_ub=au,b_ub=bu,bounds=bounds,method=METHOD,options=OPTIONS)
    solve_seconds=time.monotonic()-solve_start
    warning_messages=[str(item.message) for item in caught]
    if not sol.success:
        arrays={"cost":cost,"b_eq":be,"b_ub":bu}
        for label,matrix in (("A_eq",ae),("A_ub",au)):
            arrays.update({label+"_data":matrix.data,label+"_indices":matrix.indices,
                           label+"_indptr":matrix.indptr,label+"_shape":matrix.shape})
        np.savez_compressed(failure_path,**arrays)
        raise RuntimeError(sol.message)
    equality=float(np.max(abs(ae@sol.x-be),initial=0))
    inequality=float(np.max(np.maximum(au@sol.x-bu,0),initial=0))
    stationarity=float(np.max(abs(cost-ae.T@sol.eqlin.marginals-au.T@sol.ineqlin.marginals-
                                  sol.lower.marginals-sol.upper.marginals),initial=0))
    dual=float(be@sol.eqlin.marginals+bu@sol.ineqlin.marginals+sum(sol.upper.marginals[:dsize]))
    gap=abs(float(sol.fun)-dual)
    assert max(equality,inequality,stationarity,gap)<=NUMERICAL_TOLERANCE,(equality,inequality,stationarity,gap)
    return dict(solution=sol.x,left=left,right=right,targets=targets,outputs=outputs,
                compression=compression,full_targets=full_targets,full_outputs=full_outputs,
                nl=nl,nr=nr,Y=Y,blocks=blocks,slope_index=slope_index,intercept_index=intercept_index,
                info={"variables":n,"equalities":len(be),"inequalities":len(bu),
                      "nonzeros":int(ae.nnz+au.nnz),"build_seconds":build_seconds,
                      "solve_seconds":solve_seconds,"iterations":int(sol.nit),
                      "solver_status":int(sol.status),"solver_message":sol.message,"method":METHOD,
                      "warnings":warning_messages,"search_objective":float(sol.fun),
                      "search_intercept":float(sol.x[intercept_index]),
                      "search_slope":float(sol.x[slope_index]),"search_dual_value":dual,
                      "numerical_residuals":{"equalities":equality,"inequalities":inequality,
                                              "stationarity":stationarity,"duality_gap":gap}})


def reconstruct(eps, source, word, design_s, found):
    start=time.monotonic()
    x=found["solution"]; nl,nr,Y=found["nl"],found["nr"],found["Y"]
    decoder=[]
    for r in range(nl*nr):
        row=[rational(max(0.,float(value))) for value in x[r*Y:(r+1)*Y]]
        largest=max(range(Y),key=lambda k:row[k])
        row[largest]=1-sum(value for k,value in enumerate(row) if k!=largest)
        assert min(row)>=0 and sum(row)==1
        decoder.append(row)
    slope=max(Q(0),rational(x[found["slope_index"]])); radius=slope/4
    decoder_events=[subset_sums(row) for row in decoder]
    target_events=[subset_sums(row) for row in found["targets"]]
    events=[]; intercept=Q(0)
    for theta,mask,ui,vi,_ in found["blocks"]:
        u=[min(radius,max(-radius,rational(x[k]))) for k in ui]
        v=[min(radius,max(-radius,rational(x[k]))) for k in vi]
        t=max(decoder_events[i*nr+j][mask]-u[i]-v[j] for i,j in product(range(nl),range(nr)))
        residual=t+sum(a*b for a,b in zip(found["left"][theta],u))+sum(a*b for a,b in zip(found["right"][theta],v))-target_events[theta][mask]
        intercept=max(intercept,residual)
        events.append(dict(world=theta,mask=mask,u=u,v=v,t=t,residual=residual))
    # Verify the reconstructed certificate, independently of search residuals.
    for ev in events:
        assert all(abs(value)<=radius for value in ev["u"]+ev["v"])
        assert all(ev["t"]+ev["u"][i]+ev["v"][j]>=decoder_events[i*nr+j][ev["mask"]]
                   for i,j in product(range(nl),range(nr)))
        assert ev["residual"]<=intercept
    lift = [[Q(v) for v in row] for row in found["compression"]["uniform_lift"]]
    full_decoder = [[sum(row[g]*lift[g][y] for g in range(Y))
                     for y in range(len(found["full_outputs"]))] for row in decoder]
    assert all(sum(row)==1 and min(row)>=0 for row in full_decoder)
    bound=intercept+slope*design_s
    info=found["info"]|{"reconstruct_seconds":time.monotonic()-start,
                        "search_to_exact_gap":float(bound)-found["info"]["search_objective"]}
    return {"schema_version":1,"eps":list(map(str,eps)),"diagnostic_source":source,"word":word,
            "at_loss":str(design_s),"weights":["1/2","1/2"],"worlds":[list(w) for w in WORLDS],
            "diagnostic_left":[list(map(str,row)) for row in found["left"]],
            "diagnostic_right":[list(map(str,row)) for row in found["right"]],
            "input_pairs":[[i,j] for i,j in product(range(nl),range(nr))],
            "target_rows":[list(map(str,row)) for row in found["targets"]],
            "full_target_rows":[list(map(str,row)) for row in found["full_targets"]],
            "full_output_sequences":[list(y) for y in found["full_outputs"]],
            "target_compression":found["compression"],
            "target_encoding":"exact sufficient encoding with disjoint uniform lift",
            "output_sequences":[list(y) for y in found["outputs"]],
            "target_signal_convention":"compressed labels; full literal records and exact stochastic lift are supplied",
            "decoder":[list(map(str,row)) for row in decoder],
            "full_decoder":[list(map(str,row)) for row in full_decoder],"intercept":str(intercept),"slope":str(slope),
            "bound":str(bound),"bound_float":float(bound),"all_exact_checks_pass":True,
            "event_coverage":"all compressed-target subsets including empty/full for every world; exact TV isometry gives full-target bound",
            "events":[{"world":ev["world"],"mask":ev["mask"],"u":list(map(str,ev["u"])),
                       "v":list(map(str,ev["v"])),"t":str(ev["t"])} for ev in events],
            "exact_checks":{"decoder_rows":nl*nr,"event_world_pairs":len(events),
                            "corner_inequalities":len(events)*nl*nr,"potential_box_inequalities":len(events)*2*(nl+nr),
                            "intercept_inequalities":len(events)},"search":info,
            "lp_lower_candidate":found["info"]["search_objective"],
            "claim":"Exact rational feasibility of this affine transfer bound; no exact search-optimality claim"}


def representation_controls():
    checks=0
    for eps in NOISES:
        counts=diagnostic_rows(eps,"count3"); majority=diagnostic_rows(eps,"majority3")
        for side in (0,1):
            full,_=target_rows(eps,"LLL" if side==0 else "RRR")
            sequences=list(product((0,1),repeat=3))
            for theta in range(4):
                for k in range(4):
                    assert sum(full[theta][j] for j,y in enumerate(sequences) if sum(y)==k)==counts[side][theta][k]
                    checks+=1
                for j,y in enumerate(sequences):
                    k=sum(y)
                    assert counts[side][theta][k]/comb(3,k)==full[theta][j]
                    checks+=1
                assert [sum(counts[side][theta][:2]),sum(counts[side][theta][2:])]==majority[side][theta]
                checks+=1
    target_checks = 0
    for eps, word in product(NOISES, TARGETS):
        compressed_target(eps, word)
        target_checks += 1
    return {"exact_checks":checks,"full_record_count_equivalence":True,"majority_garbling":True,
            "exact_target_compressions_checked":target_checks,"disjoint_uniform_lift_TV_isometry":True}


def parent_majority_control(cert, parent):
    if cert["diagnostic_source"]!="majority3":
        return None
    word="adaptive" if cert["word"]=="adaptive_L" else cert["word"]
    matches=[row for row in parent["certificates"] if row["diagnostic_source"]=="majority3"
             and tuple(map(Q,row["eps"]))==tuple(map(Q,cert["eps"]))
             and row["word"]==word and Q(row["at_loss"])==Q(cert["at_loss"])]
    assert len(matches)==1
    row=matches[0]; difference=cert["search"]["search_objective"]-row["lp_lower_candidate"]
    assert abs(difference)<NUMERICAL_TOLERANCE,(cert["eps"],word,cert["at_loss"],difference)
    return {"parent_word":word,"parent_search_objective":row["lp_lower_candidate"],
            "search_objective_difference":difference,"parent_rational_bound":row["bound"],
            "new_rational_bound":cert["bound"]}


def case_id(eps,source,word,s):
    fmt=lambda x:str(x).replace("/","d")
    return f"{source}_e{fmt(eps[0])}_{fmt(eps[1])}_{word}_s{fmt(s)}"


def main(args):
    start=time.monotonic()
    protocol=HERE/"PROTOCOL.md"; parent_path=HERE.parent/"theory/certificates.json"
    if args.mode=="production" and not protocol.exists():
        raise RuntimeError("Production requires frozen protocol")
    parent=json.loads(parent_path.read_text())
    index=HERE/("results_smoke_compressed.json" if args.mode=="smoke" else "results.json") if args.output is None else Path(args.output).resolve()
    index.parent.mkdir(parents=True,exist_ok=True)
    certdir=HERE/("smoke_compressed_certificates" if args.mode=="smoke" else "certificates")
    certdir.mkdir(exist_ok=True)
    if args.mode=="smoke":
        cases=[(NOISES[0],source,word,s) for source in SOURCES
               for word,s in (("LR",Q(0)),("LRR",Q(1,100)))]
    else:
        cases=[(eps,source,word,s) for eps,source,word,s in product(NOISES,SOURCES,TARGETS,DESIGN_LOSSES)]
    if args.sources:
        cases=[case for case in cases if case[1] in args.sources]
    report={"schema_version":1,"mode":args.mode,"status":"running",
            "started_utc":datetime.now(timezone.utc).isoformat(),"source_sha256":sha(__file__),
            "protocol_sha256":sha(protocol) if protocol.exists() else None,
            "parent_inputs":{"../theory/certificates.json":sha(parent_path),
                             "../theory/certificates.py":sha(HERE.parent/"theory/certificates.py")},
            "versions":{"python":sys.version,"numpy":np.__version__,"scipy":scipy.__version__,"platform":platform.platform()},
            "solver_method":METHOD,"solver_options":OPTIONS,"numerical_control_tolerance":NUMERICAL_TOLERANCE,
            "rational_denominator_limit":DENOMINATOR,"representation_controls":representation_controls(),
            "intended_cases":len(cases),"certificates":[],"failures":[],"warnings":[]}
    if args.resume and index.exists():
        old=json.loads(index.read_text())
        for key in ("source_sha256","protocol_sha256","parent_inputs"):
            if old[key]!=report[key]:
                raise RuntimeError("Refuse resume after changing "+key)
        report=old;report["status"]="running"
    done={row["id"] for row in report["certificates"]}
    def checkpoint():
        report["updated_utc"]=datetime.now(timezone.utc).isoformat()
        report["run_seconds"]=time.monotonic()-start
        write_json(index,report)
    checkpoint()
    try:
        for eps,source,word,s in cases:
            ident=case_id(eps,source,word,s)
            if ident in done:
                continue
            found=search(eps,source,word,s,certdir/(ident+"_FAILED.npz"))
            cert=reconstruct(eps,source,word,s,found)
            cert["source_sha256"]=report["source_sha256"]
            cert["protocol_sha256"]=report["protocol_sha256"]
            control=parent_majority_control(cert,parent)
            if control:
                cert["parent_majority_control"]=control
            path=certdir/(ident+".json")
            write_json(path,cert)
            summary={k:cert[k] for k in ("eps","diagnostic_source","word","at_loss","intercept","slope","bound","bound_float","search","exact_checks","all_exact_checks_pass","lp_lower_candidate") }
            summary.update({"id":ident,"certificate_path":str(path.relative_to(HERE))})
            if control:
                summary["parent_majority_control"]=control
            report["certificates"].append(summary);done.add(ident)
            report["warnings"].extend({"id":ident,"message":message} for message in found["info"]["warnings"])
            checkpoint()
            print(ident,"bound",round(cert["bound_float"],10),"seconds",round(found["info"]["solve_seconds"],2),"done",len(done),flush=True)
        report["status"]="passed_development_smoke" if args.mode=="smoke" else "passed_requested_stage"
        checkpoint()
        print(json.dumps({"status":report["status"],"certificates":len(report["certificates"]),
                          "seconds":report["run_seconds"],"warnings":len(report["warnings"]),"failures":len(report["failures"])}),flush=True)
    except Exception:
        report["status"]="failed"
        report["failures"].append({"case":locals().get("ident"),"traceback":traceback.format_exc()})
        checkpoint()
        raise


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode",choices=("smoke","production"),default="smoke")
    parser.add_argument("--output");parser.add_argument("--resume",action="store_true")
    parser.add_argument("--sources",nargs="+",choices=SOURCES)
    main(parser.parse_args())
