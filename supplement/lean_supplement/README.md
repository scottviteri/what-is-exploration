# Lean source supplement

This source-only snapshot contains the Lean modules attributed to the selected
paper edition `primary_intrinsic_rewards_20260925` and all their local imports:
141 directly attributed modules and
179 dependency modules.

## Build

Install Lean's elan toolchain manager. In this extracted directory run:

```sh
lake exe cache get
lake build
```

The `lean-toolchain` file selects the compiler, and `lake-manifest.json` pins
external packages. The first build needs network access to download the toolchain,
packages and available Mathlib caches. These downloads and generated build files
are substantially larger than this source ZIP and are intentionally excluded.

`Formal.lean` imports the selected proof modules. The standalone Lake configuration
retains the original compiler options and removes the unrelated OracleSearch target.

## Inspect the selection

- `DEPENDENCIES.json` records immediate imports, source hashes, package revisions,
  and example import paths explaining each module's inclusion. Reverse importer
  lists also mention modules from the original repository that are not included.
- `PAPER_CLAIMS.json` preserves the selected claim records and their qualifications.
  Written-support paths refer to the original repository, not files in this ZIP.
- `FILES_SHA256.json` hashes every other file in the archive.
- `ANONYMIZATION.json` records copy-only metadata transformations and their
  original/export hashes. Canonical research records and Lean sources are retained
  in the original repository; author names in internal editorial history are
  replaced in this export without removing scientific qualifications.

Selection is by whole module, not individual declaration. Some included files
therefore contain extra lemmas. Numerical experiment claims are not formalized by
this archive, and the Lean support scope remains that recorded in the claim ledger.
Experimental scripts, manuscript sources, downloaded packages, and compiled caches
are not included.

Archive integrity, local import closure, and known identity/path disclosures are
checked during export. These automated checks do not certify an independent clean
build or correspondence of every paper statement to its proof.

Regenerate from the original repository with:
`python3 Formal/scripts/export_paper_supplement.py`.
