"""Compare isolated caching changes with frozen originals, without old writes."""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[key]='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import argparse,hashlib,importlib.util,json,time
import numpy as np
HERE=Path(__file__).resolve().parent
CORRECTED=HERE.parent
OLD=CORRECTED.parent/'quality'

def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def save(name,value): (HERE/name).write_text(json.dumps(value,indent=2,allow_nan=False)+'\n')
def timed(call):
 wall=time.perf_counter();cpu=time.process_time();result=call()
 return result,dict(wall_seconds=time.perf_counter()-wall,cpu_seconds=time.process_time()-cpu)

def kernels():
 protocol=json.loads((HERE/'PROTOCOL.json').read_text());m=np.load(protocol['model_for_exhaustive_target_equivalence']);T,Z=m['T'],m['Z']
 oldworker=load('old_worker',OLD/'audit_worker.py');newworker=load('new_worker',CORRECTED/'audit_worker.py');oldvalidator=load('old_validator',OLD/'validate_audits.py');newvalidator=load('new_validator',CORRECTED/'validate_audits.py')
 pw,setupw=timed(lambda:newworker.cache_target_kernels(T,Z));pv,setupv=timed(lambda:newvalidator.cache_native_targets(T,Z))
 ow,tow=timed(lambda:np.stack([oldworker.target_kernel(T,Z,i) for i in range(32768)]))
 nw,tnw=timed(lambda:np.stack([newworker.cached_target_kernel(pw,i) for i in range(32768)]))
 ov,tov=timed(lambda:np.stack([oldvalidator.native_target(T,Z,i) for i in range(32768)]))
 nv,tnv=timed(lambda:np.stack([newvalidator.cached_native_target(pv,i) for i in range(32768)]))
 assert np.array_equal(ow,nw),'Producer target probabilities changed'
 assert np.array_equal(ov,nv),'Independent validator target probabilities changed'
 cross=float(abs(nw-nv).max());assert cross<=1e-12
 value=dict(status='passed',targets=32768,model_sha256=sha(protocol['model_for_exhaustive_target_equivalence']),producer_bit_identical=True,validator_bit_identical=True,cross_implementation_max_difference=cross,producer_array_sha256=hashlib.sha256(ow.tobytes()).hexdigest(),validator_array_sha256=hashlib.sha256(ov.tobytes()).hexdigest(),timing=dict(producer_cache_setup=setupw,validator_cache_setup=setupv,original_producer_all_targets=tow,cached_producer_all_targets=tnw,original_validator_all_targets=tov,cached_validator_all_targets=tnv))
 save('TARGET_KERNEL_EQUIVALENCE.json',value);print(json.dumps(value,indent=2))

def audit_case(index):
 protocol=json.loads((HERE/'PROTOCOL.json').read_text());folder=Path(protocol['audits'][index]);result=json.loads((folder/'result.json').read_text());assert result['complete'] and result['completed_target_count']==32768
 protected=[folder/x for x in ['model.npz','policy.npz','result.json','provenance.json','bounds.npz','full_revelation_witness.npz','hardest_witness.npz','largest_upper_witness.npz','validation.json']]+[folder/c['file'] for c in result['chunks']]
 before={str(p):sha(p) for p in protected}
 old=load('validator_original',OLD/'validate_audits.py');new=load('validator_cached',CORRECTED/'validate_audits.py')
 old_result,old_time=timed(lambda:old.validate(folder));new_result,new_time=timed(lambda:new.validate(folder))
 save(f'case{index}_original_validation.json',old_result);save(f'case{index}_cached_validation.json',new_result)
 differences={key:[old_result.get(key),new_result.get(key)] for key in set(old_result)|set(new_result) if key!='validation_seconds' and old_result.get(key)!=new_result.get(key)}
 assert not differences,differences
 assert old_result['status']==new_result['status']=='passed'
 changed=[p for p,h in before.items() if sha(p)!=h];assert not changed,changed
 report=dict(status='passed',audit=str(folder),completed_target_count=new_result['completed_target_count'],all_non_timing_fields_exactly_equal=True,unchanged_old_evidence_files=len(before),old_evidence_sha256=before,original=old_time,cached=new_time,wall_speedup=old_time['wall_seconds']/new_time['wall_seconds'],cpu_speedup=old_time['cpu_seconds']/new_time['cpu_seconds'],metrics={k:new_result[k] for k in ['audit_lower','audit_upper','model_policy_replay_error','max_witness_feasibility','max_per_target_gap','max_replay_disagreement']})
 save(f'case{index}_comparison.json',report);print(json.dumps({k:v for k,v in report.items() if k!='old_evidence_sha256'},indent=2))
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--mode',choices=['kernels','case0','case1'],required=True);parser.add_argument('--cpu',required=True,type=int);args=parser.parse_args();os.sched_setaffinity(0,{args.cpu})
 if args.mode=='kernels':kernels()
 else:audit_case(int(args.mode[-1]))
