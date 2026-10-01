"""Freeze small final summaries after all registered follow-up stages stop."""
from common import *
import subprocess,time
from datetime import datetime,timezone
while True:
    state=json.loads((HERE/'MONITOR.json').read_text())
    if state['status']=='finished':break
    time.sleep(30)
subprocess.run([sys.executable,str(HERE/'summarize.py')],check=True)
subprocess.run([sys.executable,str(HERE/'plot_followup.py')],check=True)
s=json.loads((HERE/'COMBINED_STATUS.json').read_text())
text=(HERE/'STATUS.md').read_text()
text=text.replace('# Follow-up status','# Completed follow-up execution: outcome and remaining gaps',1)
text+='\n\nThis dated report was frozen after the registered queues stopped. Terminal queue counts identify any failed, skipped or unavailable work; “finished” does not imply every planned case succeeded. All original and follow-up failures remain visible. The near-optimal extension began with 70 available policies out of 88 originally registered. No new manuscript integration, commit, push or export is performed.\n'
(HERE/'FINAL_SUMMARY.md').write_text(text)
include=['FINAL_SUMMARY.md','COMBINED_STATUS.json','combined_figure_data.csv','figure_data.csv','FOLLOWUP_FIGURE.pdf','FOLLOWUP_FIGURE.png','PROTOCOL.md','README.md']
write(HERE/'FINAL_SUMMARY_HASHES.json',dict(frozen_utc=datetime.now(timezone.utc).isoformat(),files={n:digest(HERE/n) for n in include},queues=s['queues']))
