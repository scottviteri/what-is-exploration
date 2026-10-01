#!/usr/bin/env python3
"""Combine complete per-case independent audits and bind their artifacts."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
OUT=HERE/'results'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    design=json.loads((OUT/'design.json').read_text())
    assert design['code_sha256']==digest(HERE/'compute.py')
    assert design['protocol_sha256']==digest(HERE/'PROTOCOL.md')
    assert design['core_sha256']==digest(HERE.parent/'noisy_diagnostic_transfer_2026-09-13/compute.py')
    cases=[];checks=0;errors={};seconds=0.
    for spec in design['cases']:
        name=spec['name'];audit=json.loads((OUT/f'audit_{name}.json').read_text())
        result=json.loads((OUT/name/'results.json').read_text())
        assert audit['status']=='passed' and result['status']=='complete'
        assert audit['auditor_sha256']==digest(HERE/'audit.py')
        assert len(audit['cases'])==1 and audit['cases'][0]['case']==name
        assert result['code_sha256']==design['code_sha256']
        assert result['protocol_sha256']==design['protocol_sha256']
        assert len(result['optima'])==6 and len(result['endpoints'])==72 and not result['failures']
        cases+=audit['cases'];checks+=audit['check_count'];seconds+=audit['seconds']
        for key,value in audit['max_errors'].items(): errors[key]=max(errors.get(key,0),value)
    manifest={str(p.relative_to(HERE)):digest(p) for p in sorted(OUT.glob('*/*')) if p.is_file()}
    result=dict(status='passed',scope='Complete per-case independent float64 replay; not interval proof.',
                cases=cases,check_count=checks,max_errors=errors,seconds=seconds,
                auditor_sha256=digest(HERE/'audit.py'),compute_sha256=digest(HERE/'compute.py'),
                protocol_sha256=digest(HERE/'PROTOCOL.md'),artifact_sha256=manifest)
    (OUT/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='passed',cases=len(cases),checks=checks,
                         max_residual=max(errors.values()),artifacts=len(manifest)),indent=2))


if __name__=='__main__':main()
