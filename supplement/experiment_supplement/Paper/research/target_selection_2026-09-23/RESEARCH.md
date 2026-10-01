# Research rationale and certificate boundaries

23 September 2026. Written derivations and implementation research, not new Lean
claims. See PROTOCOL.md for prospective choices and the frozen manifests for the
actual attempted grid.

## What the existing evidence motivates

The September 15 native benchmark failed its broad-benefit screen, including no
nominal wins over Brier on the primary decision metric. Its fixed 16-target
weighted objective is not withdrawn. The subsequent saved-record weight analysis
found both native/Brier loss rankings in all eight non-equivalent pairs under
broad admissible reweightings; that analysis did not reoptimize collectors.

The September 23 campaigns found favorable finite worst-target results for the
fixed native library, together with Brier wins on several cases and longer-target
failures. Numerical representatives do not establish all-optima failure.
The full-minimax reference's 20 collection-length-four/five runs started from eight
fixed three-step action sequences. Seventeen closed the full 128-target numerical
gap immediately; three needed 16 or 20 active targets. In recurring model 91501,
the recorded audit improved from .0629950 to .0419778 at t=4 and .0298235 to
.0155629 at t=5. These selected examples motivate the registered varied-case study;
they do not select its environments by favorable outcome.

Experiment 76 held nine collectors fixed and studied target discovery. Mandatory
fixed action sequences eliminated heuristic misses above .001 for eight of nine
collectors, but the remaining information collector still had false plateaus.
This motivates structured seeds and complete audit bounds, not a plateau stopping
rule or a claim that random target sampling is uniformly reliable.

Sources: ../native_objective_benchmark_2026-09-15/README.md and analysis/weights/;
../lp_scaling_2026-09-23/overnight_results/ and
../intrinsic_extension_2026-09-23/recovery_results/;
../../../Experiments/docs/EXP76_RESULTS.md.

## Prefix and mixture reductions

If T is a garbling of U, composing a decoder E→U with U→T yields
δ(E,T)≤δ(E,U). Thus a shorter retained prefix is redundant in a maximum when
its longer extension remains. A recorded random choice among component targets
has deficiency at most their weighted average, hence at most their maximum.
The old 16-target minimax library therefore reduces to its eight length-three
fixed sequences. Weighted sums do not admit this deletion: their shorter-target
and mixture terms express additional priorities. Pairwise information-order
pruning beyond structural prefixes requires its own certified comparison; no
approximate numeric zero is silently promoted to exact dominance.

## Restricted master and complete audit

Let S be the selected targets and P the feasible collector family (possibly
restricted by an intrinsic-return threshold). A repaired master LP dual L obeys

    L <= min_{pi in P} max_{T in S} δ(K_pi,t,T)
      <= min_{pi in P} A_(t,n)(pi).

For a feasible incumbent, exhaustive target-specific decoder upper bounds give
U >= A_(t,n)(pi). Hence U-L certifies full-target minimax suboptimality. Keeping
the largest previous master dual remains valid while P and n stay fixed. A
hardest-target search incumbent supplies a lower bound on an audit, not its
upper bound. Sampling stagnation cannot certify convergence.

For a uniform mean over N targets, optimizing the mean over a K-target subset
with lower bound L_K gives global reference lower bound (K/N)L_K, since omitted
losses are nonnegative. The incumbent's exhaustive mean upper gives the opposite
bound. This can be loose until coverage grows. Uniform sample means and structured
means are different finite approximation rules, not a fixed infinite J_w.

This alternating restricted optimization and worst-case analysis is the standard
cutting-set pattern; see Mutapcic and Boyd, 2009,
https://web.stanford.edu/~boyd/papers/prac_robust.html . Our complete target oracle
is exhaustive at n=3/4. The earlier mixed-integer n=4 oracle failed to close its
bounds under either tested formulation; it is not assumed efficient here.

## Why ordinary backward induction is not the whole oracle

Fixed-history intrinsic rewards admit exact policy-tree dynamic programming.
Target deficiency additionally optimizes a world-independent decoder coupling all
source signals and target branches. Choosing target actions and the separating
decision witness jointly introduces products. Fixing a witness may permit a DP
subproblem, but alternating such subproblems supplies lower witnesses, not a
certified global target maximum. Exploring tighter formulations is useful only
with complete small-depth comparisons and honest upper/lower gaps. This campaign
first measures whether restricted-master target generation already removes the
practical bottleneck.

## Favorable intrinsic optima

Information/Brier controls constrain the actual expected reward to be within
0, .01 or .05 of its attainable range below the DP optimum. A 1e-10 numerical
reward slack is separately recorded. A recovered LP policy that falls below the
threshold is mixed in causal realization weights with a DP-optimal policy, then
replayed and checked against that same threshold. The mixing probability is
rounded upward at resolution 1e-8; its value and before/after reward are saved.
The repaired policy is independently audited. Its objective need not equal the
master primal, but the unchanged master dual remains a lower bound. A large
repair may leave a large certification gap, which stays visible. This is a best
capability within near-optimal policies comparison, not worst-over-optima.

## Stable numerical decoding without changing the experiment

Tiny source columns can cause large raw LP stationarity residuals even when the
solver reports optimality. The retained prelaunch failures document this.
The wrapper merges such columns into a retained large signal, with worldwise
merged mass η<=1e-8. This gives a literal garbling E'=ER. Mapping its merged
signal back to that retained original signal reconstructs E within TV η, so

    δ(E,F) <= δ(E',F) <= δ(E,F)+η.

The coarse decoder is lifted back to every ORIGINAL source column. Its TV upper
and a feasible dual lower are recomputed using ORIGINAL probabilities and must
still have gap <=2e-7. This is a certificate on E, not an unqualified coarse-LP
value. Saved witnesses contain the map and worldwise mass; reduced-LP KKT
residuals are explicitly labeled separately. No probability in the saved model
or collector is edited and no acceptance tolerance is relaxed.

## What would count as a useful outcome

Report seconds and active targets needed to certify the same finite optimum;
full-depth audit versus charged computation at matched case/t/n; target-seed
variation; held-out n=4 error of n=3-selected final policies; and the difference
between ordinary and favorable information/Brier selections. Keep adverse cases,
increasing error after library expansion, failures, and incomplete coverage.
An adaptive method can save targets but lose wall time because it pays for full
separation. More targets can change tradeoffs and worsen an individual collector.
Neither result is a failure of the experiment.

No canonical target weighting, efficient evaluator of eventual J_w, universal
native superiority, unseen-model learner transfer, or complete-return Bayesian
optimization is inferred. The freshly supplied classes test repeated planning
across different environments; the actual world remains unknown within each.

## Completed bounded solver study

The separate [decomposition study](decomposition_research/README.md) derives and
implements globally valid affine lower cuts from decoder dual witnesses. The
master keeps collector flow variables and deficiency bounds; the decoder work
remains explicit and is charged. Cut coefficients use every syntactic history,
including histories unreachable under the current policy. This changes the
optimization algorithm for a fixed finite library, not the objective or audit.

Independent arithmetic audits passed all 16 corrected configurations. Thirteen
have matching monolithic certificates, two monolithic comparisons timed out,
and one tested decomposition alone. At t=3 with all 128 targets, the HMM91501
minimax solve took about 2.00 seconds versus 31.39 seconds for the monolithic
comparison. A small weighted n=2 case was slower (0.259 versus 0.163 seconds).
These are bounded pilots on a shared machine, not a general speed guarantee.

The exact HMM91502 t=4, n=3, equal-weight 128-target problem that exhausted the
main pilot's monolithic budget was solved by decomposition in 17.93 seconds.
Its independently checked objective interval is
[0.015187220739322396, 0.015187379769563760]. This licenses investigation of the
larger library; it does not establish that its collector beats information or
Brier. The main comparison queue stays frozen. The next computational comparison
should pair both backends across the prescribed classes and target libraries,
including the observed slow case and the new eight-world classes, before using
the alternative for still longer horizons. The prototype does not implement the
reward-face controls, and it does not remove the exhaustive target-audit cost.

All preliminary timing mistakes, timeouts, corrected runs, source snapshots and
independent audits remain under `decomposition_research/`; use its corrected
`SUMMARY.csv` and `results_fair_timing/` rather than preliminary timing ratios.
