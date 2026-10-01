# Noisy native diagnostics under competing acquisition

Frozen primary protocol, 13 September 2026. Written before the new production runs. Implementation smoke tests are development checks and are stored separately. This study was authorized following the project assessment in `../intrinsic_objective_project_review_2026-09-12/`.

## Scientific question and claim boundary

Can a small objective built from genuinely noisy native diagnostics provide a useful guarantee for additional native targets or later decisions when acquisition choices compete for a binding budget? Compare all near-optimal policies, not selected optimizer representatives. Distinguish universal-source decoder certificates from bounds restricted to this feasible policy family.

This is a finite supplied-model study of terminal objectives. It is not an experiment optimizing the entire countable eventual J_w, a learned-agent benchmark, an asymptotic completion test, or a new Lean result. The proof question is whether stochastic diagnostic marginals can be combined with a controlled residual error; independence of separately decoded marginals is not assumed.

## Fixed causal interface

Worlds are theta=(U,V) in {0,1}^2, kept fixed for a collection run. The action alphabet is L,R,WAIT and observations are 0,1.

- L returns U through a binary symmetric channel with crossover e_L.
- R returns V through a binary symmetric channel with crossover e_R.
- WAIT returns 0 deterministically and does not change anything.

All sensor randomness is independent across uses conditional on the world. Both sensors remain available. Full action-observation history is retained. Collector horizons H are 3 and 4. Every behavioral randomized history-dependent policy is feasible. Histories containing WAIT followed by observation 1 have zero controlled probability in every world; an implementation may omit these histories provided it records that reduction and extends policies arbitrarily there.

Primary sensor-error pairs are (0.1,0.1), (0.25,0.25), and (0.1,0.3). Posterior objectives use independent planning priors P(U=1)=q in {0.5,0.01}, P(V=1)=0.5. These priors do not alter world laws, native deficiencies or evaluation purposes.

The WAIT policy induces an uninformative experiment at every H. Every other record dominates this experiment. Consequently no-data values are the actual worst feasible values of the posterior objectives and the largest feasible native losses. This permits genuine full-return-range normalization without enumerating all pure policies to find a worst native loss.

## Native targets and retained weights

Every target is an actual finite intervention in the same interface. Its full record is retained, or replaced by a proved equivalent sufficient encoding of that record.

| Name | Intervention | Weight |
| --- | --- | ---: |
| L | One L measurement | 0.2 |
| R | One R measurement | 0.2 |
| tagged | Fair recorded choice between one L and one R measurement | 0.1 |
| LR | L followed by R | 0.1 |
| LLL | Three L measurements | 0.1 |
| RRR | Three R measurements | 0.1 |

The weights total 0.8 and remain fixed when targets are added. They can be extended to a positive countable separating native family using the remaining mass. No renormalization of the retained target weights is performed.

Four sum objectives minimize the following terminal losses at H:

1. `native_singles`: weights on L and R only.
2. `native_tagged`: add the tagged target.
3. `native_joint`: add LR.
4. `native_repeats`: add LLL and RRR.

`native_minimax` minimizes the largest deficiency among all six targets. Its loss is not called the exhaustive native audit. The other two objectives maximize terminal information gain (bits) and terminal expected squared-posterior-norm increase. There is no time discount in any objective in this study.

The omitted evaluation targets are LLR, LRR and an adaptive three-step intervention: first choose L, then choose L for both remaining steps if its observation was 0, and R for both remaining steps if it was 1. These targets are fixed before production and omitted from every scored library. Their errors on saved policies are diagnostics, not automatically complete worst-error envelopes.

## Complete purpose envelopes

The five fixed purposes are:

- Guess U with zero-one payoff under the uniform four-world evaluation prior.
- Guess V under the same prior.
- Guess the full world under the same prior.
- Guess U under an evaluation prior with P(U=1)=0.25 and P(V=1)=0.5, independently.
- Guess U xor V under the uniform prior.

For each policy, maximize the purpose value over its world-independent decoder. For each objective/tolerance/purpose, then minimize that value over all eligible policies. A separate witness may attain each endpoint; coordinatewise minima are not asserted to be jointly attained. Compute each purpose's unrestricted best H-step value as an evaluation benchmark, rather than assuming perfect revelation is available.

Primary tolerance fractions are 0, 0.01 and 0.05 of each objective's genuine full feasible return range. For posterior scores this range is the optimum minus zero. For native losses it is the no-data loss minus the optimal loss. Save both the range and the absolute gap. Numerical zero-regret faces retain an explicit numerical tolerance; do not describe floating-point feasibility as exact rational certification.

A secondary native-library comparison uses a common absolute weighted-loss tolerance 0.005 for the four weighted sums. This isolates refinement effects from a changing scale. It does not assume that adding targets improves every purpose when the optimum loss changes. The first three sums have common zero minimum for H>=2, witnessed by LR followed by WAIT; the repeat-target minimum may be positive.

No guarantee of monotone improvement is asserted across separately normalized curves. Retained-weight nesting applies at fixed absolute tolerance only where the enlarged libraries have a common zero minimum.

## Analytic controls fixed before production

1. WAIT-only has zero posterior gain and the no-data native losses.
2. LR followed by WAIT exactly simulates L, R, tagged and LR; the first three native sum minima are zero at both horizons.
3. The two posterior optima can be checked independently by finite dynamic programming on literal histories.
4. At equal sensor error e, consider the H=4 policy which picks a side fairly, measures it three times, then switches for the last measurement with probability 1-b, where b=2e(1-e). Otherwise it measures the same side a fourth time. Its policy randomization is independent of observations. Let a1=1-e and a3=1-3e^2+2e^3; optimal four-sample balanced-bit accuracy equals a3. The candidate analytic prediction is exact simulation of both BSC(e) single targets and hence their tagged mixture, while its uniform joint-world guessing value is a1^2-(a3-a1)^2, below LR's a1^2. This predicts a positive joint-target deficiency of at least (a3-a1)^2 despite zero single-target loss. Independent symbolic and decoder checks must confirm the argument; failure is retained rather than silently replacing the prediction.
5. More informative repeated and mixed targets can expose information missed by balanced bit guessing. Every such assertion requires an actual deficiency or decision witness, not only sensor-count intuition.

## Optimization, artifacts and independent verification

Use full-history policy realization weights and target-specific decoder allocations. Positive weighted deficiencies and the declared minimax reference are LPs; posterior and fixed-purpose coefficients are linear in the same realization weights. Save primal/dual certificates, recovered behavioral policies, source/target kernels, objective values, purpose values, selected target deficiencies, dimensions, timing, solver status and numerical residuals.

Near-optimal policy sets must cover arbitrary randomized policies, including mixtures with individually below-threshold components. Independently replay recovered policies and reconstruct every world row. Independently assemble fixed-experiment decoder LPs and verify objective/purpose values. Check target kernels directly from their intervention definitions. Compare posterior optima to a separately implemented dynamic program. Replay the analytic negative control with rational arithmetic where possible.

Maximizing an upper-bound deficiency epigraph is invalid. Full worst-deficiency envelopes require a complete dual-piece/vertex construction or another proved certificate; otherwise report explicit bounds and saved-policy diagnostics only. A complete finite purpose envelope is not a complete native profile or a uniform cover of all later decisions.

Hash this protocol and production computation files into run metadata. Native solutions may be reused across planning priors, with reuse explicitly marked. Retain numerical failures before any algorithmic amendment. Any substantive post-run change to model, targets, grid or primary interpretation requires a separate dated amendment.

## Staging and success criteria

Run the H=3 grid first, inspect runtime and solver checks, then run H=4. The intended primary grid has both horizons, all three noise pairs, both planning priors, seven objectives, five purposes and three tolerance fractions, with explicit prior-independent cache reuse. Complete the secondary absolute-gap comparison after primary feasibility is established. A resource-related omission is reported as unfinished, not as a negative result or a completed full grid.

A main-paper candidate needs a nonvacuous guarantee for targets outside the scored library, complete all-policy purpose evidence, explicit noise/budget/optimization terms, independent checks, and gains and costs across the declared grid. Repeating rare-prior neglect or winning the same weighted audit being optimized is insufficient. Null library improvements, tradeoffs unfavorable to native objectives and loose transfer bounds are retained.
