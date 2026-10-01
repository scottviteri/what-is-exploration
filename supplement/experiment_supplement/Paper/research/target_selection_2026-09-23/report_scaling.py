"""Read immutable checkpoints plus live coverage; never optimize or edit runs."""
from collections import Counter,defaultdict
import csv,json,statistics,sys
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
root=Path(sys.argv[1]).resolve()
q=json.loads((root/'queue.json').read_text());rows=[];coverage=Counter();last=[]
for p in sorted(root.glob('cell_*/result.json')):
 if '_previous_' in p.parent.name:continue
 try:r=json.loads(p.read_text())
 except (OSError,json.JSONDecodeError):continue
 a=r['arguments'];coverage[r['status']]+=1
 for i,cp in enumerate(r.get('checkpoints',[])):
  audit=cp['audit'];held=r.get('held_out_horizon',{}) if i==len(r['checkpoints'])-1 else {}
  rows.append(dict(cell=p.parent.name,case=r['model_name'],objective=a['objective'],strategy=a['strategy'],face=a['face_objective'],regret=a['regret'],seed=a['target_seed'],t=a['t'],n=a['n'],k=cp['k'],training_seconds=cp['training_seconds'],end_to_end_seconds=cp['end_to_end_seconds'],audit_lower=audit['lower'],audit_upper=audit['upper'],mean_lower=audit['mean_lower'],mean_upper=audit['mean_upper'],minimax_gap=cp.get('full_minimax_gap',''),certified=cp.get('full_minimax_certified',False),heldout_n=held.get('n',''),heldout_upper=held.get('audit',{}).get('upper',''),cell_status=r['status']))
 if r.get('checkpoints'):last.append((a,r['checkpoints'][-1]))
if rows:
 path=root/'CHECKPOINTS.csv';tmp=path.with_suffix('.tmp')
 with tmp.open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
 tmp.replace(path)
lines=['# Target-selection campaign status','',f'Queue: **{q["status"]}**. Last supervisor update: {q.get("finished_utc",q.get("updated_utc",q["started_utc"]))}.',
       f'Registered jobs: {q.get("registered_jobs", "see frozen manifest")}; terminal jobs: {len(q["jobs"])}. Source and job definitions: `{q.get("manifest_path", "../pilot_manifest.json")}`.',
       f'Observed cells: {dict(coverage)}. Accepted checkpoints: {len(rows)}. Supervisor terminal statuses: {dict(Counter(x["status"] for x in q["jobs"]))}.','',
       'These are finite supplied-model planning results. Complete minimax references optimize their own evaluation criterion. Weighted native scores use finite libraries, not eventual J_w. No sampled policy training is performed. Counts below are provisional while coverage is incomplete.','',
       'CPU and GPU have separate worker pools. Training time includes target generation, planning, independent objective replay and adaptive separation; ordinary offline audits are separate. Held-out horizon four never informs selection.','',
       '| Objective / strategy | Completed checkpoints | Certified full-minimax checkpoints |','|---|---:|---:|']
groups=defaultdict(list)
for r in rows:groups[(r['objective'],r['strategy'],r['face'],r['regret'])].append(r)
for key,data in sorted(groups.items()):lines.append(f'| {" / ".join(map(str,key))} | {len(data)} | {sum(x["certified"] for x in data)} |')
lines+=['','Every registered job, including pending, stopped, failed and oversized jobs, is in the frozen manifest and queue records. Each completed checkpoint retains its policy, selected target IDs, compact LP certificate and full per-target audit. Partial sweeps remain separate files and are not labeled complete.','',
        'The figure shows individual curves, not pooled independent environment samples; repeated target seeds share the same environment. Compare matched rows in CHECKPOINTS.csv. Larger libraries need not improve every resulting collector or its held-out performance.']
if rows:
 fig,axs=plt.subplots(1,2,figsize=(11,4),constrained_layout=True)
 colors={'random':'#5485bb','structured':'#d08b31','adaptive':'#37905c'}
 curves=defaultdict(list)
 for row in rows:
  if row['face']=='none' and row['strategy']!='baseline' and row['t']==3 and row['n']==3:curves[row['cell']].append(row)
 labels=set()
 for series in curves.values():
  series.sort(key=lambda r:r['k']);strategy=series[0]['strategy'];objective=series[0]['objective'];ax=axs[0 if objective=='native_minimax' else 1]
  label=strategy if (objective,strategy) not in labels else None;labels.add((objective,strategy))
  ax.plot([max(r['training_seconds'],1e-4) for r in series],[r['audit_upper'] for r in series],color=colors[strategy],alpha=.3,lw=.8,marker='.',label=label)
 for ax,title in zip(axs,['Finite minimax target selection','Finite weighted target selection']):
  ax.set(xscale='log',xlabel='Charged planning / selection seconds',ylabel='Full three-step worst-target error',title=title)
  ax.grid(alpha=.2)
  if ax.get_legend_handles_labels()[0]:ax.legend()
 fig.savefig(root/'curves.tmp.png',dpi=140);(root/'curves.tmp.png').replace(root/'CURVES.png');plt.close(fig)
 lines+=['','![Live target-selection curves](CURVES.png)']
tmp=root/'STATUS.tmp';tmp.write_text('\n'.join(lines)+'\n');tmp.replace(root/'STATUS.md')
