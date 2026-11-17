#!/usr/bin/env python3
"""Reconstruct the anonymous supplement and verify every part and final byte hash."""
import argparse
import hashlib
import json
from pathlib import Path
import tempfile


def digest(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def assemble(folder, output):
    checks = json.loads((folder / 'CHECKSUMS.json').read_text())
    expected = checks['supplement.zip']
    if output.exists():
        if output.stat().st_size == expected['bytes'] and digest(output) == expected['sha256']:
            return output
        raise FileExistsError(f'Refusing to replace a different existing file: {output}')
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=output.parent, prefix=output.name + '.', delete=False) as target:
            temporary = Path(target.name)
            full_hash = hashlib.sha256()
            total = 0
            for part in checks['parts']:
                name = part['name']
                if Path(name).name != name or not name.startswith('supplement.zip.part'):
                    raise ValueError('Unexpected part filename')
                part_hash = hashlib.sha256()
                size = 0
                with (folder / name).open('rb') as source:
                    while chunk := source.read(1024 * 1024):
                        target.write(chunk)
                        full_hash.update(chunk)
                        part_hash.update(chunk)
                        size += len(chunk)
                if size != part['bytes'] or part_hash.hexdigest() != part['sha256']:
                    raise ValueError(f'Part checksum mismatch: {name}')
                total += size
            if total != expected['bytes'] or full_hash.hexdigest() != expected['sha256']:
                raise ValueError('Reconstructed archive checksum mismatch')
        temporary.chmod(0o644)
        temporary.replace(output)
        return output
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def main():
    folder = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=folder / 'supplement.zip')
    args = parser.parse_args()
    result = assemble(folder, args.output)
    print(f'Verified anonymous supplement: {result}')


if __name__ == '__main__':
    main()
