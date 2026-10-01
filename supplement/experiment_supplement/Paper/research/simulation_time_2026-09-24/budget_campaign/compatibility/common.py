"""Isolated diagnostic IO; parent primary sources are immutable inputs."""
import sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
PARENT=HERE.parent
sys.path.insert(1,str(PARENT))
from io_utils import now,sha,write,save,levels,raw_law,replay,rewards,np,json,os,TOL

def verify_sources():
    from io_utils import verify_sources as parent_verify
    ph=parent_verify()
    snapshot=json.loads((HERE/'SOURCES.json').read_text())
    assert snapshot['parent_sources_sha256']==ph
    for name,digest in snapshot['files'].items():assert sha(HERE/name)==digest, name
    return sha(HERE/'SOURCES.json')

def inputs(job):
    for rel,digest in job['input_sha256'].items():assert sha(PARENT/rel)==digest,rel
    with np.load(PARENT/job['model']) as z:T=z['T'].copy();Z=z['Z'].copy()
    with np.load(PARENT/job['reference_path']) as z:F=z['E'].copy()
    return T,Z,F
