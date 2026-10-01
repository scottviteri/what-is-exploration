# Combined code and data supplement

This archive combines the Lean and experiment source/data packages.
Each component retains its original files and relative directory structure.
There are no nested ZIPs to unpack.

- `lean_supplement/README.md`: selected Lean modules, the generated root import file,
  pinned Lake configuration and claim/dependency manifests. Build from that folder.
- `experiment_supplement/README.md`: Python experiment sources, protocols,
  configurations, selected model/policy arrays and numerical certificates,
  results, plotting scripts and reproduction instructions.
  From that folder, first run `python3 materialize.py` to restore byte-identical
  duplicate data paths, then run the documented Python commands.

The component manifests record exported file hashes and every duplicate-data
alias; no logical data file is omitted by deduplication. `MANIFEST.json` at
this level records both input-archive hashes and every other combined file hash.
Combining preserves the two snapshots; it does not refresh them against later
manuscript changes or rerun proofs or experiments.

Scope: the selected experiment evidence includes primary model/policy arrays,
budget-reference decoder certificates, and the bounded additional evidence listed
in the experiment README. Exhaustive four-step target decoder banks and large
native-planning master/decomposition certificates are excluded. Full replay of
those checks requires regeneration or separately supplied bulk artifacts.
The Lean package has not received an independent clean build. Automated archive
integrity and known-identity checks run before publication; they do not establish
scientific correctness or completeness of every historical evidence path.

To combine the two original component ZIPs again, run
`python3 scripts/combine_supplements.py` in the source repository, or supply
`--lean PATH --experiments PATH --output PATH` explicitly.
