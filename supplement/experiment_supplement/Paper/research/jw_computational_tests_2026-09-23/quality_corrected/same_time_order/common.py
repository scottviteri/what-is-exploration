"""Serialization and fixed design only; no numerical solver imports."""
import csv
import datetime
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
STUDY = HERE.parent
BACKEND = STUDY.parents[1] / 'target_selection_2026-09-23'
METHODS = ('fixed', 'tractability', 'hard', 'minimax')
BASELINES = ('information', 'brier', 'uniform')
DIRECTIONS = ('native_to_baseline', 'baseline_to_native')
TOL = 2e-7
MARGIN = 1e-6
CAP = 30
CPU = 25

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(path):
    return json.loads(Path(path).read_text())

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def write(path, value):
    path = Path(path)
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(value, indent=2, allow_nan=False) + '\n')
    tmp.replace(path)

def unchanged(bindings):
    for name, expected in bindings.items():
        require(Path(name).is_file() and sha(name) == expected, 'Bound file changed: ' + name)

def design(models):
    return [dict(job_id=f'{i:03d}', model=m, method=a, baseline=b, direction=d,
                 budget_seconds=40, collection_length=3)
            for i, (m, a, b, d) in enumerate(
                (m, a, b, d) for m in models for a in METHODS
                for b in BASELINES for d in DIRECTIONS)]

def csv_write(path, rows):
    fields = list(dict.fromkeys(k for row in rows for k in row))
    with Path(path).open('w', newline='') as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow({k: json.dumps(v, sort_keys=True) if isinstance(v, (dict, list)) else v
                             for k, v in row.items()})

def pair_classification(forward, reverse):
    if any(r.get('status') != 'validated' for r in (forward, reverse)):
        return 'unavailable'
    if forward['lower'] > MARGIN and reverse['lower'] > MARGIN:
        return 'numerical_incomparability'
    if forward['upper'] <= TOL and reverse['upper'] <= TOL:
        return 'mutual_approximate_simulation'
    if forward['upper'] <= TOL and reverse['lower'] > MARGIN:
        return 'native_approximate_simulation_reverse_separated'
    if reverse['upper'] <= TOL and forward['lower'] > MARGIN:
        return 'baseline_approximate_simulation_reverse_separated'
    return 'unresolved'
