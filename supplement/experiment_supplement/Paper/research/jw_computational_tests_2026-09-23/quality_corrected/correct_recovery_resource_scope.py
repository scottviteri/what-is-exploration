#!/usr/bin/env python3
"""Correct only the resource report's elapsed-time description after recovery.
Retain the producer's original report. No timings, results or comparisons change.
"""
from pathlib import Path
import copy,datetime,hashlib,json,shutil
HERE=Path(__file__).resolve().parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    assert json.loads((HERE/'ANALYSIS_EXECUTION.json').read_text())['state']=='passed'
    path=HERE/'RESOURCE_REPORT.json';report=json.loads(path.read_text())
    recovery_path=HERE/'exhaustive_audits/coordinator_recovery/RECOVERY.json'
    recovery=json.loads(recovery_path.read_text());assert recovery['state']=='finished'
    previous='Orchestrator monotonic elapsed time at the bound STATUS snapshot, including queue/concurrency/dispatch. Active tasks are not included in the completed-task cost totals.'
    assert report['audit']['queue_elapsed_scope']==previous
    orphaned=set(recovery['orphaned_complete_worker_ids'])
    assert set(report['audit']['current_timing_incomplete_jobs'])==orphaned
    current='Calendar elapsed from original queue start to the recovered STATUS snapshot, including coordinator interruption and recovery; reconstructed from UTC timestamps, not one uninterrupted monotonic timer. Ten original numerical process exit/wall measurements are unavailable. Known work totals retain missing entries; saved worker-internal elapsed times are separate telemetry, not substitutes for process wall times.'
    old=copy.deepcopy(report)
    report['audit']['queue_elapsed_scope']=current
    archive=HERE/'exhaustive_audits/coordinator_recovery/RESOURCE_REPORT_before_scope_correction.json'
    assert not archive.exists();shutil.copy2(path,archive)
    correction={'corrected_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'scope':'Only the recovered queue elapsed-time description is corrected; every numeric value and original input binding is unchanged.',
      'original_report_path':str(archive),'original_report_sha256':sha(archive),
      'correction_source_sha256':{str(Path(__file__).resolve()):sha(Path(__file__))},
      'recovery_record_sha256':{str(recovery_path):sha(recovery_path)},
      'previous_queue_elapsed_scope':previous,'current_queue_elapsed_scope':current}
    report['recovery_timing_scope_correction']=correction
    restored=copy.deepcopy(report);restored.pop('recovery_timing_scope_correction');restored['audit']['queue_elapsed_scope']=previous
    assert restored==old
    path.write_text(json.dumps(report,indent=2,sort_keys=True,allow_nan=False)+'\n')
    correction['corrected_report_sha256']=sha(path)
    (HERE/'exhaustive_audits/coordinator_recovery/RESOURCE_SCOPE_CORRECTION.json').write_text(json.dumps(correction,indent=2)+'\n')
    print(json.dumps({'status':'passed','numerical_values_changed':False,'timing_incomplete_jobs':len(orphaned)}))
if __name__=='__main__':main()
