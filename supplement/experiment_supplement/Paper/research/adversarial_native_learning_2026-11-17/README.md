# Learning to collect evidence against adversarial tests

Start with the [explainer](EXPLAINER.pdf) ([editable source](EXPLAINER.tex)),
written and shared before implementation on 17 November 2026.

This pilot trains a finite collector, stochastic decoders, and a target-policy
generator using empirical response tables from labelled, resettable worlds.
Adversarial and random target additions are compared at equal collection,
candidate-fitting, and collector-update budgets. True channels and linear
programs are reserved for evaluation. Unavoidable tradeoffs, decoder fitting
error, and finite-sample model error remain distinct.

The [checklist](CHECKLIST.txt) tracks execution. the lead author approved a compact table
and discussion in the selected paper's learned-approximation appendix; this
two-bit learning experiment is separate from the 22-class supplied-model study.
It does not evaluate the eventual reference score `J_w`. The
[integration review](../../reviews/two_bit_learning_2026-11-16/REVIEW_NOTES.txt)
records the clean and cumulative highlighted paper. The original results PDF
describes the execution before this manuscript integration.

The [results explanation](RESULTS.pdf) ([source](RESULTS.tex)) reports all 72
registered runs. Selecting difficult targets helped on these examples; learning
the proposal distribution added little over uniform proposals with hardest
retention. Both methods approached the finite optimum in the compatible and
irreversible environments. The noisy environment retained a larger gap, and
good collector records did not guarantee equally good fitted decoders.

The [complete numerical report](main/report/RESULTS.md) retains every condition,
and [compact machine-readable results](main/report/COMPACT_SUMMARY.json) include
all signed paired comparisons and source hashes. The
[independent audit](AUDIT.txt) checked 72 runs, 432 checkpoints, 18 datasets,
1,080 candidate scores and six reference policies; a separate dense linear
program recomputed 15,228 target errors. These are numerical checks, not Lean
proofs. The [reproduction instructions](REPRODUCE.txt) give the commands, and
the [development record](DEVELOPMENT.txt) separates the development runs from
the frozen main cohort.

Training is implemented in [learner.py](learner.py), finite response laws and
sampling in [models.py](models.py), and independent numerical evaluation in
[oracle.py](oracle.py). [run_pilot.py](run_pilot.py) freezes the configuration
and sources and audits checkpoints only after each learner returns.
[test_pilot.py](test_pilot.py) supplies the independent replay.

Raw datasets, per-run decoder arrays and the detailed report summary remain
available locally under `main/` and `development/initial/`. The study's
`.gitignore` keeps these regenerable payloads outside Git, following the
[artifact-storage policy](../../../Experiments/ARTIFACT_STORAGE.md). Source
snapshots, configurations, small summaries, figures, reports and audit records
remain eligible for versioning. A fresh clone must regenerate raw runs before
using the saved-run replay command.

A later [structured target-search follow-up](structured_search/README.md)
tested learned proposals on 256 measurement-setting sequences and a shuffled
control. All 48 main runs are retained; the initial development advantage did
not persist on the fresh main seeds. That component study remains outside the
rebuttal following the lead author's reviewer-scope discussion. It does not replace the
original pilot or its blue–green tie.
