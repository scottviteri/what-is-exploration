# Anonymous ICLR rebuttal files

The [paper PDF](paper.pdf) and reconstructed `supplement.zip` are the files to
upload to the review system. Their contents and supported metadata were checked
for known author identifiers. This public repository identifies the authors;
its URL is not an anonymous review link.

The publication connector has a per-request transfer limit, so the ZIP is stored
in three parts. From a checkout of this repository, run with Python 3.11 or later:

```sh
python3 iclr-rebuttal/assemble_supplement.py
```

Alternatively, download this directory's script, [checksums](CHECKSUMS.json), and
all three parts into the same folder, then run the script there:

- [Part 1](supplement.zip.part01)
- [Part 2](supplement.zip.part02)
- [Part 3](supplement.zip.part03)

The script checks each part before accepting the assembled archive. It produces
the exact 93,469,523-byte ZIP prepared for ICLR, with SHA-256
`2f7a3b454dbd51932422be78ede861c7bf5aa28d97d114dd75d55f3d2c6d1401`.
An existing different output is never overwritten. Upload the resulting ZIP,
not the parts or GitHub's whole-repository download.

The ZIP contains selected Lean sources and experiment evidence. Its scientific
content is unchanged by anonymization; two saved checkout paths were made
relative, and the corresponding hashes were updated. The named-author preprint
and manuscript source elsewhere in this repository are separate editions.
