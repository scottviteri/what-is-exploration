import argparse,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--cell');a=p.parse_args()
subprocess.run([sys.executable,str(HERE/'check_planning.py'),'--cells',a.cell,'--output',str(HERE/'planning_checks'/a.cell)],check=True,timeout=120)
r=json.loads((HERE/'planning_checks'/a.cell/(a.cell+'.json')).read_text());assert r['status']=='passed',r
subprocess.run([sys.executable,str(HERE/'audit.py'),'--source',str(HERE/'completion_retry_results'/a.cell),'--output',str(HERE/'control_audits'/a.cell),'--seconds','2400'],check=True,timeout=2550)
