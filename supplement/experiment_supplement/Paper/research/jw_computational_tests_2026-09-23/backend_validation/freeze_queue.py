"""Create the immutable Track A grid before new solver timings are observed."""
from pathlib import Path
import csv,json,hashlib
HERE=Path(__file__).resolve().parent;ROOT=next(p for p in HERE.parents if (p/'AGENTS.md').exists());OLD=ROOT/'Paper/research/target_selection_2026-09-23/decomposition_research'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=list(csv.DictReader((OLD/'SUMMARY.csv').open()));cells=[]
for repeat in range(3):
 for i,row in enumerate(rows):
  key=f"{row['case']}__t{row['t']}n{row['n']}K{row['K']}__{row['objective']}"
  record=json.loads((OLD/row['run']/key/'comparison.json').read_text())
  methods=['monolithic','decomposition']+(['bridge_cold','bridge_increasing','bridge_decreasing'] if row['objective']=='native_weighted' else [])
  # Rotate every method's order, including whether the monolithic solve is first.
  methods=methods[repeat%len(methods):]+methods[:repeat%len(methods)]
  cells.append(dict(case=row['case'],t=int(row['t']),n=int(row['n']),K=int(row['K']),kind=row['objective'],repeat=repeat,
   target_indices=record['target_indices'],methods=methods,model_path=f"Paper/research/native_objective_benchmark_2026-09-15/results/{row['case']}/model.npz",archived_record_sha256=sha(OLD/row['run']/key/'comparison.json')))
manifest={'schema':'adaptive-track-a-v1','cells':cells,'core_cases':16,'repeats':3,'weighted_cases':9,'total_method_processes':sum(len(c['methods']) for c in cells),'workers':4,'cpus':[4,5,6,7],
 'single_thread':True,'per_process_gib':4,'solver_cap_seconds':40,'per_solve_hard_cap_seconds':65,'gap':1e-6,
 'source_hashes':{p.name:sha(p) for p in HERE.glob('*.py')},'policy':'All original outcomes retained; no held-out capability selection; beyond15min elapsed extensions may be marked pending after parent notice'}
out=HERE/'QUEUE.json'
if out.exists():raise SystemExit('Refuse overwrite frozen queue')
out.write_text(json.dumps(manifest,indent=2)+'\n');print(len(cells),manifest['total_method_processes'])
