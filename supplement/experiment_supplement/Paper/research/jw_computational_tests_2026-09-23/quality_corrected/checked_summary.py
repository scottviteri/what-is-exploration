#!/usr/bin/env python3
"""Bind supplementary JSON endpoints to the independently checked CSV snapshot.
Standard library only; no optimizer, numerical re-estimation or endpoint selection.
"""
from pathlib import Path
import csv, hashlib, io, json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def csv_scalar(value):
    if value is None:
        return ''
    if isinstance(value, (dict, list)):
        return json.dumps(value, sort_keys=True)
    return str(value)


def verify_unchanged(bindings):
    for name, digest in bindings.items():
        path = Path(name)
        require(path.is_file() and sha_bytes(path.read_bytes()) == digest,
                'Checked supplementary input changed: ' + name)


def checked_summary(summary_path, check_path=None):
    summary_path = Path(summary_path).resolve()
    check_path = Path(check_path or summary_path.parent.parent / 'SUMMARY_CHECK.json').resolve()
    csv_path = summary_path.parent / 'endpoints.csv'
    check_bytes = check_path.read_bytes()
    check = json.loads(check_bytes)
    require(check.get('status') == 'passed' and check.get('errors') == [],
            'Independent primary check must pass without errors')
    bindings = {str(check_path): sha_bytes(check_bytes),
                str(Path(__file__).resolve()): sha_bytes(Path(__file__).read_bytes())}
    contents = {}
    for path in (summary_path, csv_path):
        expected = check.get('input_sha256', {}).get(str(path))
        require(expected is not None, 'Chosen file is outside checker coverage: ' + str(path))
        data = path.read_bytes()
        require(sha_bytes(data) == expected, 'Checker input hash mismatch: ' + str(path))
        bindings[str(path)] = expected
        contents[path] = data
    report = json.loads(contents[summary_path])
    require(report['metadata'].get('status') == 'final_snapshot', 'Primary report is not final')
    reader = csv.DictReader(io.StringIO(contents[csv_path].decode(), newline=''))
    csv_rows = list(reader)
    headers = reader.fieldnames
    require(headers and len(headers) == len(set(headers)), 'Missing or duplicated CSV columns')
    json_rows = report['endpoints']
    require(set(headers) == set().union(*(set(row) for row in json_rows)),
            'JSON and CSV endpoint columns differ')
    def indexed(rows, encode):
        result = {}
        for row in rows:
            require(None not in row, 'Malformed CSV row')
            serialized = {k: encode(row.get(k)) for k in headers}
            key = tuple(serialized[k] for k in ('model', 'method', 'budget_seconds'))
            require(key not in result, 'Duplicate endpoint key: ' + repr(key))
            result[key] = serialized
        return result
    require(indexed(json_rows, csv_scalar) == indexed(csv_rows, lambda x: x),
            'JSON endpoints differ from independently checked CSV endpoints')
    verify_unchanged(bindings)
    return report, bindings
