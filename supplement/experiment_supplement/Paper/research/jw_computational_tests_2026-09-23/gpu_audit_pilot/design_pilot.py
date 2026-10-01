"""Archived-design-only continuation of the bounded feasibility pilot."""
from pilot import *

def run():
    started=time.perf_counter();old_seconds=time.time()-(HERE/'PROTOCOL.json').stat().st_mtime
    # The first run was stopped at the parent’s seed correction, not at solver failure.
    # This continuation has its own maximum 450-second wall budget, keeping total
    # active numerical work below the original 600-second pilot allowance.
    protocol=dict(design_seeds=[2026096900,2026100900],worlds=[4,8],concentration=1.,collector_horizons=[3,4],target_depth=4,source='Existing target_selection_2026-09-23/main_manifest.json',maximum_active_continuation_seconds=450,target_ids=[0,1,2,3,7,31,127,511,1023,4095,8191,16383,24575,30001,32766,32767],batch_scaling_sizes=[16,128],decision='No objective outcome comparison. Larger batches and full CPU audit conditional on runtime and valid original-source brackets only.')
    write('DESIGN_PROTOCOL.json',protocol)
    records=[]
    for seed,Q in zip(protocol['design_seeds'],protocol['worlds']):
      m=core.random_model(seed,worlds=Q);targets=core.Targets(m['T'],m['Z'],4)
      for t in protocol['collector_horizons']:
        tag=f'design_seed{seed}_q{Q}_t{t}';g=core.geometry(m['T'],m['Z'],t);E=g.raw/2**t
        np.savez_compressed(HERE/(tag+'_model.npz'),T=m['T'],Z=m['Z'],E=E)
        ids=protocol['target_ids'];Fs=np.stack([targets.get(i)['kernel'] for i in ids]);tick=time.perf_counter();dec=GPUBatch(E,16,len(ids),tag);setup=time.perf_counter()-tick;gpu=dec.solve(Fs,tag+'_gpu_witness.npz')
        cpu=StableDecoder(E,16);tick=time.perf_counter();cpus=[];saved={}
        for j,F in enumerate(Fs):
          r,w=cpu.solve(F);bound=replay(E[:,w['source_indices']],F,w['decoder'],w['alpha'],w['b']);bound['target']=ids[j];cpus.append(bound)
          saved.update({f'{j}_{key}':value for key,value in w.items()})
        cpu_seconds=time.perf_counter()-tick
        np.savez_compressed(HERE/(tag+'_cpu_witness.npz'),E=E,F=Fs,**saved)
        independent=[dict(target=ids[j],upper=cpu_primal(E,Fs[j])) for j in [0,7,15]]
        overlap=all(max(a['lower'],b['lower'])<=min(a['upper'],b['upper'])+1e-10 for a,b in zip(gpu['rows'],cpus))
        direct_agreement=all(abs(z['upper']-cpus[j]['upper'])<=TOL for z,j in zip(independent,[0,7,15]))
        r=dict(seed=seed,worlds=Q,t=t,tag=tag,gpu_setup_seconds=setup,gpu=gpu,cpu_seconds=cpu_seconds,cpu_rows=cpus,independent_cpu_primal=independent,crosscheck=overlap and direct_agreement,cpu_full_audit_estimate=cpu_seconds*32768/16,gpu_full_audit_estimate=gpu['seconds']*32768/16)
        records.append(r);write('design_timing.json',records)
        print('DESIGN',tag,'gpu',gpu['seconds'],'accepted',gpu['all_accepted'],'cpu',cpu_seconds,'CPU_FULL_EST',r['cpu_full_audit_estimate'],flush=True)
      E=core.geometry(m['T'],m['Z'],3).raw/8;ids=np.linspace(0,32767,128,dtype=int).tolist();Fs=np.stack([targets.get(i)['kernel'] for i in ids]);tag=f'design_seed{seed}_q{Q}_t3_batch128';gpu=GPUBatch(E,16,128,tag).solve(Fs,tag+'_gpu_witness.npz')
      write(tag+'.json',dict(target_ids=ids,gpu=gpu,full_audit_seconds_estimate=gpu['seconds']*256))
      print('LARGE_BATCH',tag,gpu['seconds'],gpu['all_accepted'],'FULL_EST',gpu['seconds']*256,flush=True)
    # GPU is no longer in use after these fixed pilots. A CPU-only full sweep is
    # attempted only if its conservative estimate fits the remaining cap.
    write('GPU_RELEASED.json',dict(timestamp=time.time(),message='All GPU calls finished. Any remaining work is CPU-only.'))
    full=None
    first=records[0];remaining=450-(time.perf_counter()-started)
    if first['cpu_full_audit_estimate']*1.25<remaining:
      seed=first['seed'];Q=first['worlds'];m=core.random_model(seed,worlds=Q);E=core.geometry(m['T'],m['Z'],3).raw/8;targets=core.Targets(m['T'],m['Z'],4);dec=StableDecoder(E,16);tick=time.perf_counter();rows=[];selected_witness={};failures=[]
      for j in range(32768):
        if time.perf_counter()-started>445:break
        try:
          F=targets.get(j)['kernel'];r,w=dec.solve(F);bound=replay(E[:,w['source_indices']],F,w['decoder'],w['alpha'],w['b']);bound['target']=j;rows.append(bound)
          if j in [0,1,127,8191,16383,24575,32767]:
            selected_witness.update({f'{j}_{key}':value for key,value in w.items()});selected_witness[f'{j}_F']=F
        except Exception as e:failures.append(dict(target=j,error=repr(e)));break
        if j%2048==0:print('CPU_FULL',j,time.perf_counter()-tick,flush=True)
      full=dict(seed=seed,worlds=Q,t=3,n=4,count=len(rows),complete=len(rows)==32768,seconds=time.perf_counter()-tick,rows=rows,failures=failures)
      write('design_cpu_full_audit.json',full);np.savez_compressed(HERE/'design_cpu_full_selected_witnesses.npz',E=E,**selected_witness)
    write('DESIGN_RESULTS.json',dict(status='completed',cases=len(records),gpu_validated_cases=sum(r['gpu']['all_accepted'] and r['crosscheck'] for r in records),continuation_seconds=time.perf_counter()-started,full_audit=None if full is None else {k:v for k,v in full.items() if k!='rows'}))
if __name__=='__main__':run()
