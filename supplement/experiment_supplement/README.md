# Experiment code, selected data, and results

This package accompanies the selected intrinsic-rewards paper. It contains the
Python sources, protocols, configuration manifests and compact results for:

- The 22-class finite-objective comparison and reward-matched controls:
  `Paper/research/empirical_ending_checks_2026-09-23/`.
- Collection-budget and reference-compatibility comparisons:
  `Paper/research/simulation_time_2026-09-24/budget_campaign/`, its `compatibility/`
  subdirectory, and the separate `uniform_decoder_recovery/` correction.
- The earlier sixteen-target benchmark, including its unfavorable broad-benefit
  result: `Paper/research/native_objective_benchmark_2026-09-15/`.
- Shared planning/decoder implementations and supporting study code, retained
  under their original directory names. This is a conservative study-level
  selection, not a minimal collection of individual functions.

`MANIFEST.json` records exported file hashes, static Python imports, selection
rules and source directories. Static import lists do not resolve every dynamic
path or prove that every archived runner is portable. `ANONYMIZATION.json` records
copy-only transformations: internal author names and task identifiers are
anonymized, and historical absolute workspace prefixes become relative paths.
Scientific numerical content is preserved. The record includes each changed
file's original and exported hashes. Hash references to included, transformed
inputs use the corresponding exported hashes, preserving their byte checks;
references to absent historical inputs retain their canonical hashes.

Exact duplicate numeric arrays are stored once to fit the upload limit.
`ALIASES.json` records every original path, retained source path, and SHA-256.
Run the materializer below before using the archived scripts. It verifies source
and restored hashes and refuses to overwrite any changed local file.

## Install and run the small checks

Use Python 3.11 or newer. From this package's root:

```sh
python3 materialize.py
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements-cpu.txt
.venv/bin/python Experiments/supplement_smoke.py
```

The requirements record the versions used for package smoke checks, not a claim
that every historical run used that exact environment. The optional historical
GPU and exact-arithmetic investigations additionally use cuOpt and python-flint;
they are not needed for the checks above or figure generation below.

## Rebuild the current figures from included summaries

```sh
.venv/bin/python Paper/draft/intrinsic_rewards/figures/finite_objective_figures.py
```

This command writes the selected fixed-budget, matched-control, and budget/cost
figures under `Paper/draft/intrinsic_rewards/figures/`, with a layout-check JSON.
It checks fixed hashes for the three included summaries. The earlier joint plot
and collection-budget matrix can also be regenerated with
`Paper/draft/figures/finite_objective_joint.py`. These commands redraw saved
results; they do not recompute their underlying evidence.

The paper omits the duplicated audit and budget-count panels; the threshold
table retains the budget counts. The full 22-case collection-budget matrix is
included as `Paper/draft/intrinsic_rewards/figures/finite_objective_budget_matrix.pdf`
and can be rebuilt by the earlier joint renderer above.
Stable fixed-budget cell identifiers refer to
`Paper/research/empirical_ending_checks_2026-09-23/COMPLETE_REWARDS.json`.
The earlier fixed-target benchmark discussed in the appendix is the
`native_objective_benchmark_2026-09-15` study listed above; its failed screen and
all endpoints remain included.

## Rerun experiments

Start with the relevant study's `PROTOCOL.md` and source runner. For example, the
original benchmark documents per-case regeneration and audit commands in its
README. The 22-class campaign uses `target_selection_2026-09-23/run_queue.py`,
subsequent completion passes, and the matched-control pipeline; the budget study
has its own `prepare.py`, `run_queue.py`, `check.py` and compatibility runners.
These are archived campaign tools. Their CPU affinities, environment paths,
output locations and time/disk budgets may require local configuration.

## Selected data and verification scope

In addition to compact summaries, this export includes the frozen primary
model/policy arrays for the 427 fixed-budget entries, matched controls and
bidirectional witnesses, 132 budget-reference entries, and 396 budget jobs with
their six-reference decoder certificates (including preserved recovery copies).
It also includes held-out profiles and hardest-target witnesses, final audit profiles,
dynamic-programming certificates, and compatibility LP/policy/decoder files.
The exporter selects this bounded evidence explicitly, including files ignored
by Git; `MANIFEST.json` is the exact inventory of this package.

Exhaustive four-step target decoder banks and large native-planning
master/decomposition certificates are excluded. Full replay of those checks
requires regenerating or separately supplying the bulk outputs. Paths and hashes
in historical reports can therefore refer to absent files; their old statements
about versioning describe the original execution boundaries. See
`Experiments/ARTIFACT_STORAGE.md` for the repository's storage policy.

Automated checks reject known author identities, personal paths/links, and
unsupported metadata before publishing the ZIP. They do not establish complete
anonymity against every inference, an independent experiment rerun, or correctness
of the scientific claims. The combined submission ZIP contains the Lean sources
in its sibling `lean_supplement/` directory.
