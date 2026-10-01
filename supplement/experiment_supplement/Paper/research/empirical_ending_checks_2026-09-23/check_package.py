"""Read-only evidence-binding and summary replay after the final witness checks.

This does not rewrite CHECK.json or repeat optimization. The full witness
arithmetic was performed by the recorded independent checkers.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
from collections import Counter, defaultdict
from statistics import median

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
cache = {}
bindings = 0
def sha(path):
    p = Path(path)
    if not p.is_absolute():
        p = ROOT / p
    if p not in cache:
        cache[p] = hashlib.sha256(p.read_bytes()).hexdigest()
    return cache[p]
def read(name):
    return json.loads((HERE/name).read_text())
def bind(path, expected):
    global bindings
    assert sha(path) == expected, str(path)
    bindings += 1
def input_bindings(d):
    for key in ("input_sha256", "additional_input_sha256", "validation_logs"):
        for path, h in d.get(key, {}).items():
            bind(path, h)

rewards = read("COMPLETE_REWARDS.json")
comparison = read("COMPLETE_COMPARISON.json")
matched = read("MATCHED_COMPARISON.json")
for d in (rewards,comparison,matched):
    assert d["status"] == "passed"
    input_bindings(d)
bind(HERE/"COMPLETE_REWARDS.json",comparison["reward_report_sha256"])
bind(HERE/"finish.py",comparison["source_sha256"])
bind(HERE/"finish_matched.py",matched["source_sha256"])
assert len(rewards["records"]) == len({r["cell"] for r in rewards["records"]}) == 427
assert len(comparison["points"]) == 220
groups = defaultdict(list)
for r in rewards["records"]:
    groups[r["case"],r["method"]].append(r)
for p in comparison["points"]:
    rows=groups[p["case"],p["method"]]
    assert p["lower"] == min(r["lower"] for r in rows)
    assert p["upper"] == max(r["upper"] for r in rows)
    assert sorted(p["cells"]) == sorted(r["cell"] for r in rows)
    sacrifices=[r["brier_sacrifice"] for r in rows if r["brier_sacrifice"] is not None]
    assert p["brier_sacrifice_min"] == (min(sacrifices) if sacrifices else None)
    assert p["brier_sacrifice_max"] == (max(sacrifices) if sacrifices else None)
ix={(p["case"],p["method"]):p for p in comparison["points"]}
def sign(lo,hi):
    return "win" if lo>1e-6 else "loss" if hi< -1e-6 else "tie" if max(abs(lo),abs(hi))<=1e-6 else "mixed"
for comp in comparison["comparisons"]:
    counts=Counter()
    for r in comp["pairs"]:
        a=ix[r["case"],comp["arm"]];b=ix[r["case"],comp["baseline"]]
        lo=b["lower"]-a["upper"];hi=b["upper"]-a["lower"]
        assert (lo,hi)==(r["lower"],r["upper"])
        assert sign(lo,hi)==r["outcome"]
        counts[r["outcome"]]+=1
    assert dict(counts)==comp["counts"] and sum(counts.values())==22

audits=[]
for dirname in ("control_audits","matched_audits","reference_audits"):
    audits.extend(sorted((HERE/dirname).glob("*/result.json")))
audits.append(HERE/"uniform_audit/result.json")
assert len(audits)==63
for path in audits:
    r=json.loads(path.read_text())
    c=json.loads(path.with_name("CHECK.json").read_text())
    assert r["status"]=="complete" and r["completed_targets"]==r["target_count"]==32768
    assert r["collection_horizon"]==3 and r["target_horizon"]==4
    assert c["status"]=="passed" and c["targets"]==32768 and c["max_gap"]<=2e-7
    bind(path,c["result_sha256"])
    input_bindings(r)

counts=Counter()
for r in matched["records"]:
    label=sign(r["difference_lower"],r["difference_upper"])
    label="native_"+label if label in ("win","loss") else label
    assert label==r["outcome"]
    counts[label]+=1
    assert r["control_brier"]>=r["native_brier"]-1e-10-1e-12
    assert abs(r["reward_threshold"]-(r["native_brier"]-1e-10))<=1e-12
    assert r["control_optimizer_gap"]<=2e-7
    assert r["control_training_worst"]<=r["native_training_worst"]+2e-7
assert dict(counts)==matched["counts"] and sum(counts.values())==22
assert abs(median((r["difference_lower"]+r["difference_upper"])/2 for r in matched["records"])-matched["median_midpoint"])<1e-15

order_counts={}
for name in ("COMPLETE_ORDER.json","MATCHED_ORDER.json"):
    d=read(name);pairs=defaultdict(list)
    for r in d["records"]:
        bind(r["witness"],r["witness_sha256"])
        if "native_policy_sha256" in r:
            bind(r["native_policy"],r["native_policy_sha256"])
            bind(r["control_policy"],r["control_policy_sha256"])
            key=r["id"]
        else:
            key=(r["case"],tuple(sorted((r["source"],r["target"]))))
        assert r.get("status","passed")=="passed"
        assert r["upper"]-r["lower"]<=2e-7
        pairs[key].append(r)
    assert len(pairs)==d["pairs"] and len(d["records"])==d["directions"]
    inc=eq=0
    for rows in pairs.values():
        assert len(rows)==2
        if all(r["lower"]>1e-6 for r in rows):inc+=1
        elif all(r["upper"]<=1e-6 for r in rows):eq+=1
        else:raise AssertionError(rows)
    assert inc==d["incomparable"] and eq==d["equivalent_within_tolerance"]
    order_counts[name]={"incomparable":inc,"equivalent_within_tolerance":eq}

formal=read("FORMAL_CHECK.json")
for path,h in formal["source_sha256"].items():bind(path,h)
input_bindings(formal)
for name in ("EXACT_DIAGNOSTIC.json","EXACT_SAVED_DIAGNOSTIC.json"):
    d=read(name);input_bindings(d)
    if "data_module_sha256" in d:bind(d["data_module"],d["data_module_sha256"])
repair=read("BINDING_REPAIR.json")
for name,h in repair["current_report_sha256"].items():bind(HERE/name,h)
assert len(repair["refreshed_checks"])==19 and not repair["new_optimization"]
evidence=read("EVIDENCE_CHECK.json")
assert evidence["status"]=="passed" and evidence["total_target_witnesses"]==19*32768
assert len(evidence["rejected_corruptions"])==4
bind(HERE/"check_new_evidence.py",evidence["source_sha256"])
assert read("REFERENCE_QUEUE.json")["status"]=="complete"
layout=read("FIGURE_LAYOUT_CHECK.json")
assert layout["status"]=="passed"
for f in layout["figures"].values():
    assert f["width_inches"]==5.5 and f["cases"]==22 and not f["text_outside_canvas"]

report=dict(status="passed",checked_utc=datetime.now(timezone.utc).isoformat(),
    checked_hash_bindings=bindings,distinct_files_hashed=len(cache),
    repaired_audits=19,matched_audits=44,total_target_witnesses_in_recorded_checks=63*32768,
    checked_method_class_envelopes=220,checked_comparison_groups=16,
    matched_counts=dict(counts),directed_summary_checks=order_counts,
    scientific_replay="Reconstructed summary arithmetic, reward floors, finite training gaps and all current input/report/witness bindings.",
    numerical_boundary="Witness arithmetic was replayed by the existing CHECK reports; this final pass does not rerun or timestamp those checks.",
    formal_boundary="Exact explicit rational finite tables only; archive bindings and policy/model execution remain external.",
    source_sha256=sha(Path(__file__)))
(HERE/"PRESENTATION_CHECK.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report,indent=2))
