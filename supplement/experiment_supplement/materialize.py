#!/usr/bin/env python3
"""Restore exact duplicate data paths from this package's checked alias inventory."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import shutil


def materialize(root: Path) -> int:
    root = root.resolve()
    aliases = json.loads((root / 'ALIASES.json').read_text())['aliases']
    manifest = {r['path']: r for r in json.loads((root / 'MANIFEST.json').read_text())['files']}

    def local(name):
        if '..' in PurePosixPath(name).parts or '\\' in name or ':' in name:
            raise ValueError(f'Unsafe materialization path: {name}')
        path = (root / name).resolve()
        if path == root or not path.is_relative_to(root) or Path(name).is_absolute():
            raise ValueError(f'Unsafe materialization path: {name}')
        return path

    # Validate every source and existing destination before writing any new file.
    pending = []
    for name, record in aliases.items():
        source_name = record['source']
        if source_name in aliases or manifest.get(name, {}).get('sha256') != record['sha256']:
            raise ValueError(f'Alias manifest mismatch: {name}')
        if manifest.get(name, {}).get('alias_of') != source_name:
            raise ValueError(f'Alias source mismatch: {name}')
        if manifest.get(source_name, {}).get('sha256') != record['sha256']:
            raise ValueError(f'Alias source hash mismatch: {name}')
        source, destination = local(source_name), local(name)
        if hashlib.sha256(source.read_bytes()).hexdigest() != record['sha256']:
            raise ValueError(f'Changed alias source: {source_name}')
        if destination.exists():
            if hashlib.sha256(destination.read_bytes()).hexdigest() != record['sha256']:
                raise ValueError(f'Refusing to overwrite changed data: {name}')
        else:
            pending.append((source, destination, record['sha256']))
    for source, destination, digest in pending:
        destination.parent.mkdir(parents=True, exist_ok=True)
        # Exclusive creation protects a newly appeared local file from overwrite.
        with destination.open('xb') as output, source.open('rb') as original:
            shutil.copyfileobj(original, output)
        if hashlib.sha256(destination.read_bytes()).hexdigest() != digest:
            raise ValueError(f'Materialization checksum mismatch: {destination.relative_to(root)}')
    return len(pending)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    count = materialize(args.root)
    print(f'Materialized {count} duplicate paths; all alias/source hashes verified.')


if __name__ == '__main__':
    main()
