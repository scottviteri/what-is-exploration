# Planner artifacts

The frozen primary protocol is `PROTOCOL.md`. This document describes the implementation and saved files; it does not change the study design.

`compute.py` defaults to development smoke mode. Production stages require `--mode production --horizons 3` or `4`. The primary return-range tolerances are selected by default. `--tolerances secondary --resume` adds the four native-sum absolute-gap controls to an existing output directory, checking that source and protocol hashes match. `--output` selects a stage directory. Results from distinct horizon directories are separate stages, not independent replications.

## Histories and hypotheses

World row order is `(0,0),(0,1),(1,0),(1,1)`. Action indices are `L=0,R=1,WAIT=2`; observations are `0,1`. Histories are ordered by depth, and children in the order `(L,0),(L,1),(R,0),(R,1),(WAIT,0)`. Histories containing `(WAIT,1)` are omitted because their controlled probability is zero in every world. Arbitrary policy prescriptions on these omitted histories extend the stored policy without changing its experiment. No observation-conditioned feasible choice on a nonnull history is restricted.

`histories_H{H}.json` stores all levels, all policy histories and all terminal histories explicitly. There are `(5**H-1)/4` policy rows and `5**H` terminal columns. The separately retained realization weights have one entry for every history through depth H, in layer order.

## Results and collectors

Each output directory owns a `results.json`; every relative path therein is relative to that directory. The file is atomically checkpointed after each completed optimum or purpose envelope. `status=passed_requested_stage` means the requested stage completed, not that all protocol stages or the independent audit completed. `config` records the intended design and `executed_subset` the most recent stage selection. `optima` and `rows` retain all records across a hash-checked resume. Native objective records have `planning_q=null`, `prior_independent=true`, and an explicit list of both planning priors to which the same result applies.

Costs are minimized: posterior costs are negative terminal gain; native costs are positive weighted deficiency or the largest deficiency over six scored targets. `normalization_scale` is no-data cost minus optimal cost. WAIT makes the no-data endpoint feasible, so this is the genuine full feasible score range. Primary envelope rows have `normalization_name=full_feasible_return_range`, their numeric `fraction`, and `eta=fraction*normalization_scale`. Secondary rows have `normalization_name=absolute`, `fraction=null`, and `eta=0.005`. The optimum itself has a recorded numerical primal/dual bracket.

Every optimum and envelope saves:

- `policies/ID.npz`: `source_kernel`, `action_rows`, `realization_weights`.
- `certificates/ID.npz`: the full LP certificate described below.
- `deficiency_witnesses/ID.npz`: independent fixed-source decoder and decision witnesses for all nine target experiments.

`target_deficiencies` lists all six scored and three omitted target errors **for that saved collector**. These errors are not automatically worst-deficiency envelopes. `purpose_values` lists all five Bayes-optimal purpose values for the saved collector. An envelope's named `purpose_value` is the complete minimum over its allowed near-optimal policy set; other coordinates evaluated on that witness are not asserted to attain their separate minima. `purpose_benchmarks` are unrestricted best H-step values from dynamic programming. `purpose_loss` is that benchmark minus the named envelope value.

## LP certificate

NPZ files contain sparse CSR matrices `A_eq` and `A_ub`, each serialized by `_data`, `_indices`, `_indptr`, `_shape`; right-hand sides `b_eq,b_ub`; `cost,bounds,solution`; and `eq_dual,ub_dual,lower_dual,upper_dual,objective` in SciPy/HiGHS sign conventions. The matrices describe minimization subject to `A_eq*x=b_eq`, `A_ub*x<=b_ub`, and finite variable bounds.

`w_indices,x_indices,terminal_w_indices` map the full policy realization variables to stored history order. Endpoint certificates additionally save `original_objective_cost` and `objective_cut_rhs`, making the near-optimality constraint explicit. Policy realization uses `sum_a x(h,a)=w(h)` and `w(hao)=x(h,a)` for each valid observation fiber; world-dependent probabilities multiply these realization weights only when forming experiments.

Decoder allocations `z(h,y)=w(h)*G(h,y)` give linear source rows, permitting joint optimization of policy and a target-specific decoder. A positive weighted sum or upper epigraph for the largest target deficiency is minimized. For a purpose envelope, the original objective becomes an upper-bound constraint and the terminal Bayes decision-value epigraph is minimized. This is valid minimization of the actual best decoder value; the code never maximizes a deficiency epigraph.

## Fixed-experiment deficiency witnesses

For each target `T`, `T__source_indices` selects nonzero source columns; `T__decoder` is a stochastic decoder on those columns. `T__upper_value` is its maximum worldwise TV error. `T__dual_alpha` is a distribution on worlds and `T__dual_b` satisfies `0<=b(theta,y)<=alpha(theta)`. Its lower witness is

`sum(T*b) - sum_x max_y sum_theta E(theta,x)*b(theta,y)`.

The matching `T__lower_value` brackets deficiency from below. Both sides are independently solved for every saved collector/target pair. Zero-probability source columns can receive any decoder row. All arithmetic is float64; tolerances, residual maxima, solver versions, runtime, computation hash and protocol hash are recorded. Numerical solver failures are retained in the report; failed main LPs also preserve the problem matrices.
