# CPU-quota correction and full re-execution

23 September2026. The initial resource check tested cgroup-v2 paths, which are
absent here. The active cgroup-v1 controller instead grants1020000 microseconds
per100000-microsecond period: **10.2 CPUs**, despite96 visible logical CPUs.
The36-worker audit had about0.28CPU per worker, confirming quota throttling.
Twelve planners plus overlapping validation also exceeded the quota temporarily.

The entire original quality attempt is preserved in `../quality/`, including all
132 planning results, successful audits, interrupted checkpoints and logs. No
held-out outcome comparison was aggregated to choose this correction. It is not
evidence of numerical invalidity: all132 original planning records passed replay.
It is a resource-accounting correction for the wall-budget comparison and to
avoid audit timeouts caused by excessive concurrency.

This directory repeats **all132 jobs**, using the identical frozen12 models,
method definitions, code, target order, epsilon and2/10/40-second budgets. Eight
single-thread planners run at once; independent planning verification follows the
planning run. The audit stage uses at most10 workers. No CPU quota is changed.
No model, method, metric or unsuccessful outcome is removed. The original
planning results remain a separately labeled throttled execution, not the primary
standalone-budget comparison. This repetition is declared before corrected
outcomes, and the original source/model hashes are bound bySOURCE_LOCK.json.

Held-out evaluation may use a separately validated cache of repeated controlled-
history laws. This only avoids recomputing the same target kernels; it does not
change the target set, probabilities, objective, witness checks or tolerances.
Its before/after checks and source hashes live in `validation_acceleration/`.
