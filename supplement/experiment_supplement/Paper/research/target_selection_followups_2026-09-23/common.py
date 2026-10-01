"""Frozen-source access and atomic output for the authorized follow-up."""
from pathlib import Path
import hashlib,json,os,sys
for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:
    os.environ[key]='1'
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ORIGINAL=HERE.parent/'target_selection_2026-09-23'
MANIFEST=json.loads((ORIGINAL/'main_manifest.json').read_text())
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,value):
    p=Path(p);p.parent.mkdir(parents=True,exist_ok=True)
    tmp=p.with_suffix(p.suffix+'.tmp');tmp.write_text(json.dumps(value,indent=2,allow_nan=False)+'\n');tmp.replace(p)
def verify_sources():
    for name,expected in MANIFEST['source_sha256'].items():
        assert digest(ORIGINAL/name)==expected,('changed source',name)
verify_sources()
sys.path.insert(0,str(ORIGINAL))
import scaling_core as core
import numpy as np

def independent_law(T,Z,layers):
    # Separate literal filtering recursion, no calls to the production mass helper.
    laws={}
    for layer in layers:
        for h in layer:
            state=np.zeros((len(T),T.shape[-1]));state[:,0]=1
            for a,o in h:
                for q in range(len(T)):
                    state[q]=state[q].dot(T[q,a])*Z[q,a,:,o]
            laws[h]=state.sum(axis=1)
    return laws
