# Generated experiment artifacts

On 25 September 2026, generated experiment payloads were removed from Git history
to make the repository practical to clone. The cleanup covers all published
branches and removes about 15.5 GiB from the current tracked tree.

The main sources of growth were the native-objective computation and target-selection
campaigns under `Paper/research/`. The cleanup also removes generated NumPy arrays,
decoder caches, oversized JSON/CSV data dumps, and per-run or per-target output
records under `Paper/research/`, `Experiments/research/`, and `Experiments/results/`.
It preserves source code, protocols, configuration sources, written reports,
smaller summary records, Lean files, manuscript sources, figures, and PDFs.
The exact excluded paths and output patterns are in the root `.gitignore`.

## Reproduction and evidence

Use each study's README, protocol, and runner to regenerate the raw outputs locally.
The saved reports describe their original executions; regeneration may change
wall-clock measurements, numerical outputs, or optimizer tie-breaking. Retained
summaries do not replace the omitted detailed certificates. Commands that replay
those certificates require regenerating the relevant outputs first. Historical
links to removed payloads are provenance, not a claim that the files ship in a clone.

Keep regenerated payloads outside Git. If a frozen raw run must be shared, use
separate artifact storage and record its location, checksum, and generating command
in the study report. Do not force-add ignored output trees. Small, necessary new
fixtures should be reviewed individually rather than reintroducing a campaign.

## Existing clones

The cleanup rewrites commit IDs. Reclone after saving local work; do not merge or
push the old history back into the cleaned branches. Paper builds and experiments
were not rerun as part of this storage cleanup.
