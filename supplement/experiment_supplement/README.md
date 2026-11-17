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
- The two-bit learning experiment in the approximation appendix:
  `Paper/research/adversarial_native_learning_2026-11-17/`, including the frozen
  main configuration, all 72-run summary outcomes, source code and independent
  audit. Its raw decoder banks must be regenerated for full saved-state replay.
- Shared planning/decoder implementations and supporting study code, retained
  under their original directory names. This is a conservative study-level
  selection, not a minimal collection of individual functions.
- Finite-history checks of the current alarm example with deterministic PLAY
  startup: `Paper/research/coinless_alarm_2026-11-16/check.py` and `checks.json`.
- Bounded exact channels for actual-world block empowerment:
  `Paper/research/actual_world_empowerment_2026-11-16/paired_check.py` and
  `paired_checks.json`, with the Lean and manuscript inputs whose hashes it records.

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

Use Python 3.12 or newer (required by the pinned SciPy version). From this package's root:

```sh
python3 materialize.py
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements-cpu.txt
.venv/bin/python Experiments/supplement_smoke.py
.venv/bin/python Paper/research/coinless_alarm_2026-11-16/check.py
.venv/bin/python Paper/research/actual_world_empowerment_2026-11-16/paired_check.py
```

The alarm check enumerates all histories for 90 combinations of horizon, startup
action, and continuation rule through five time-steps, and compares the closed
formulas through 64 time-steps. Square
calculations use exact rational arithmetic; Shannon calculations use floating
point. It rewrites the adjacent `checks.json`. It does not prove an infinite
return, quantify over all policies, or certify the Count result. Those claims
require the mathematical proofs and the individually documented Lean support.

The empowerment check constructs exact rational response channels for eight
worlds, collected lengths one through six, probe lengths one through four, and
both modes. Input-digit factorization and disjoint supports certify the bounded
capacities; the check also verifies the one-step startup capacities and finite
return identities. It rewrites `paired_checks.json`, including hashes of the
included source inputs. It does not enumerate all histories, policies, world
delays or infinite returns, and performs no training.

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

For the two-bit learning experiment, install the additional PyTorch dependency
with `pip install -r Experiments/requirements-learning.txt`, then follow that
study's `REPRODUCE.txt`. The learner runs on CPU with double precision. Its
independent mechanics checks use the included `Experiments/src/idexp/lp.py`.
The eight-setting follow-up is outside the paper and this package.

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
