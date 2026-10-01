# Commission 06: completed budget and reward-compatibility review

24 September 2026. Independent review by Missing citations for the lead author and Introduction Edits. This is a new completion review; Commission 05 and all frozen sources/results remain unchanged. The only repository file written by this review is this note. No optimizer, training worker, manuscript/ledger edit, commit or push was run. Arithmetic replay used one low-priority CPU thread and local scratch files outside the repository.

**Recommendation:** integrate the budget comparison and compatibility diagnostic alongside the existing Figure 2, with the distinctions below built into the explanation. All 34 compatibility certificates passed replay: **22 have a positive numerical lower bound on reward cost, and 12 exhibit compatibility at negligible numerical cost**. The proposed three examples are supported. This strengthens the experimental account by separating a selected policy's missed capability from an unavoidable tradeoff at the optimum of its original reward. It does not establish universal native-objective superiority or a violation of Blackwell order preservation.

Two presentation corrections matter particularly. First, 22 positive comparisons are drawn from **four pilot classes**, not 22 classes; several comparisons share the same model, reward and even equivalent references. Second, the reported 0.47% and 6.4% divide by **maximum attainable Brier gain**, whereas the existing figure's sacrifice percentage divides by the **attainable reward range**. These percentages must not share an unlabeled scale.

There is also a useful new diagnosis of the four preserved uniform failures: the solver timed out on the uniform collector's own three-step uniform reference. An explicit prefix decoder reproduces that reference, with fresh numerical error below 1.25e-16 in every case. Preserve the failed runs and the 392/396 accepted-cell denominator; they are computational failures, not evidence that uniform behavior cannot reproduce its earlier record.

## 1. What is held fixed, optimized and measured

A **case** specifies a finite class of possible worlds. Each world is a transition/observation model with a hidden state initially at zero. A run stays in one unknown world. The collector sees its own actions and binary observations, not the hidden state or world label. All planners receive the same candidate model arrays and uniform, full-support prior over worlds. This is supplied-model planning, not training on sampled episodes or testing on unseen worlds.

A **policy** chooses an action distribution from the complete past action–observation history. Its **record** is that full history. Its **experiment** E is the list of record distributions, one distribution for each possible world. Six three-step reference policies were frozen per case before these new audits. Write F_j for reference j's experiment. A reference is one selected policy, not an optimizer set or a target specifying which world is true.

For a source policy selected at total collection budget t, the reported directional error is

\[
 d_{m,j}(t)=\delta(E_{m,t},F_j)
 =\inf_G\max_Q\frac12\sum_y
       |(E_{m,t}(Q)G)(y)-F_j(Q,y)|.
\]

The **decoder** G maps the observed source record to a simulated reference record, using private randomness. It must use the same rule in every world; it cannot learn Q from an external input, take more observations, or reset the environment. Low error means matching each world's reference-record distribution. Error .02 is a total-variation tolerance, not a 2% probability of guessing the world incorrectly. It also bounds the loss in expected utility for any [0,1]-valued decision made using that reference's evidence.

The **target horizon is always three**. The source collection budget is t=3,4,5. At t=3 the source is its frozen reference. At t=4 and t=5 a policy is selected afresh for that total budget. The three collectors need not extend one another. Consequently this is a budget-specific acquisition comparison, not the stopping time of a single continuing policy, and plotted errors need not decrease with budget. Transposing method names at t>3 does not reverse the same pair of experiments.

Information gain is expected reduction in the entropy of the **full world label**, in bits. Brier gain is expected increase in the squared norm of the **full-world posterior**:

\[
 R_{\rm IG,t}=\log_2 q-\mathbb E[H_2(p_h)],\qquad
 R_{B,t}=\mathbb E\sum_Q p_h(Q)^2-1/q.
\]

These are posterior objectives under the supplied uniform prior, not raw-observation predictive surprisal or squared next-observation prediction loss. Their source scope should stay as qualified in the current manuscript. The other primary methods retain their executed categorical count, uniform-action, native-mean and native-maximum definitions. The compatibility follow-up optimizes only the original information or Brier reward; it does not substitute a native scalar for that reward.

The native mean and maximum still use all 128 deterministic three-step observation trees. Every frozen randomized three-step reference belongs to that library's mixture closure, so this comparison is **within the native objective's covered target family**. It is useful for inspecting individual capabilities, but is not held-out-target transfer. The older figure instead collects for three steps and evaluates all 32,768 deterministic four-step targets. Keep these two target horizons and their meanings separate.

## 2. The completed primary coverage

The design attempted 22 classes × 6 methods × 3 budgets = 396 source-policy cells. Each accepted cell has six directed source-to-reference audits.

| Collection budget | Accepted policy cells | What the cells represent |
|---|---:|---|
| 3 | 132/132 | Replay of the frozen references; no new policy optimization |
| 4 | 131/132 | Fresh budget-four selection; one uniform decoder failure |
| 5 | 129/132 | Fresh budget-five selection; three uniform decoder failures |
| Total | **392/396** | **2,352 accepted directional reference comparisons** |

All five optimized method families have all 22 cases at all three budgets. Uniform has 22, 21 and 19 accepted cases respectively. The four omitted complete-cell checks are:

- `expanded_h4__case_05__uniform`: `fresh_hmm_2026096801_q4_s3_c0.2`.
- `expanded_h5__case_05__uniform`: the same class, budget five.
- `expanded_h5__case_10__uniform`: `fresh_hmm_2026100800_q8_s3_c0.2`.
- `expanded_h5__case_11__uniform`: `fresh_hmm_2026100801_q8_s3_c0.2`.

Each saved failure had already audited information, Brier and count references, then exhausted the registered recovery-decoder time allocation on the uniform reference. Those partial audits do not turn the cell into an accepted six-reference check. Use missing/computationally unresolved markers, not high-error or successful-cell substitutes. A uniform t-step policy's first three steps are exactly the frozen uniform three-step policy. I additionally replayed all four saved policies and this explicit prefix projection; their worst-world TV errors were, in the order above, 6.71e-17, 9.68e-17, 7.27e-17 and 1.25e-16 or less. This local diagnostic does not repair the remaining unaudited references or change the historical status.

The accepted cells can support statements about the particular selected policies and their independently checked error bounds. Frozen t=3 native policies retain their original optimization qualification. This review did not rerun all native master/cut certificates or reinterpret them as descriptions of every exact optimizer.

## 3. What the compatibility calculation establishes

Fix one case, one collection budget t, one of the two original rewards R, one frozen three-step reference F, and epsilon=.02. Define

\[
 R_t^*=\max_\pi R_t(\pi),\qquad
 R_t^{\rm cap}(F,.02)
 =\max_{\pi:\,\delta(K_{\pi,t},F)\le .02}R_t(\pi),\qquad
 \Delta=R_t^*-R_t^{\rm cap}(F,.02).
\]

The maximizations range over all randomized full-history policies at that finite budget. The question is **how much of the original reward must be sacrificed to reproduce this particular reference within .02**. It is not a minimum-deficiency calculation over exact reward optima, nor a replacement of the original primary collector. Feasibility is guaranteed: execute the frozen reference for three steps, then extend arbitrarily and let the decoder discard the suffix.

A genuinely positive lower bound on Delta rules out every exact reward optimum satisfying this cap. More generally, if a policy's reward gap is smaller than that bound, it cannot meet the cap. Here the evidence is numerical LP bounds with residual checks, not a new exact or Lean theorem. Thus say “the numerical bounds require positive reward sacrifice,” rather than presenting the saved float64 endpoints as formally verified real inequalities.

Conversely, a negligible upper bound exhibits one nearly reward-optimal compatible policy. It does not imply that all optimal policies, the original selected policy, or a typical learner preserve the reference. Each comparison may use a different favorable, reference-aware policy and decoder. The 12 compatible results do not establish one policy satisfying all 12 caps simultaneously.

### Why the formulation and bound direction are correct

For a leaf history h, its world-independent action realization weight is w_h and its environment likelihood in world Q is p_Q(h). The actual record probability is w_h p_Q(h). Action realization variables satisfy the causal branching-flow equations. Introducing z_hy=w_h G_hy and enforcing z_hy>=0 and sum_y z_hy=w_h makes the decoded distribution sum_h p_Q(h)z_hy linear. Zero-weight rows cause no difficulty: the joint row is zero and its conditional decoder can be chosen arbitrarily.

The posterior given a reachable h cancels the factor w_h, so terminal posterior rewards are linear functions of realization weights as well. The LP therefore represents joint policy/decoder selection over the stated policy family. Bounds 0<=variable<=1 do not exclude a feasible policy or decoder: realization weights and joint decoder masses are at most one, and absolute differences of probability coordinates are at most one.

The solver used a tightened cap .02-1e-7, then replayed the normalized physical policy and decoder. Their actual error must be at most .02-1e-9. This supplies a feasible **lower bound L on constrained maximum reward** at the requested .02 cap.

For clarity, write the LP in minimization form with cost vector c (negative reward), equalities Ax=b, inequalities Bx<=d, and box 0<=x<=1. Let y be unrestricted equality multipliers and u<=0 clipped inequality multipliers. The box-repaired dual expression is

\[
 D=b^\top y+d^\top u+
       \sum_i\min(0,c_i-(A^\top y+B^\top u)_i).
\]

It lower-bounds the minimization objective in exact arithmetic without assuming the residual reduced-cost vector is zero. Let u_cap<=0 be the multiplier of the cap constraint. Relaxing its RHS by eta=1e-7 gives D+eta*u_cap. Hence the constrained **maximum reward** at the requested cap is upper-bounded by U=-(D+eta*u_cap). The minus sign and relaxation direction in the executed checker are correct. Ignoring this correction would overstate reward sacrifice by certifying the stricter cap instead.

The independently reconstructed terminal-reward backward recurrence supplies R*. The reported regret bracket is [max(0,R*-U), max(0,R*-L)]. The 2e-7 threshold is used for numerical classification. The regret bracket can be wider than 2e-7 because it includes the explicit cap-relaxation correction; that is not itself a failed LP residual check. The widest observed bracket was about 5.30e-7, while the smallest positive lower cost was about 1.865e-4. None of the positive classifications is close to the classification threshold.

All these bounds remain floating-point calculations. My separate extended-precision replay of the saved dual expression is an arithmetic cross-check, not directed interval rounding or an exact rational proof.

## 4. Eligibility and the complete 34-comparison result

Eligibility screened 4 pilot classes × 3 budgets × 2 rewards × 6 references = **144 comparisons**. A comparison entered when its original selected policy's checked deficiency lower bound exceeded .02+1e-9. I reconstructed all eligibility decisions from the original primary results. Exactly 34 entered, all were completed, and the cap of 60 excluded none.

| Pilot class | Positive numerical reward-cost comparisons | Negligible-cost compatible witnesses |
|---|---:|---:|
| Sensors (.1,.1) | 0 | 6 |
| Delay (.1,.1) | 10 | 0 |
| Irreversible (.1,.1) | 0 | 6 |
| Generated pilot, seed 2026096800, q=4, c=.2 | 12 | 0 |
| Total | **22** | **12** |

The two rewards each contribute 11 positive comparisons. The six sensor witnesses occur at t=3; the six irreversible witnesses occur for information at t=5. These are selected, correlated comparisons of known pilot cases, not 34 independent trials, not a success rate across 22 environments, and not fresh confirmation. The other 110 screened comparisons had no trigger under the stated criterion; they are not 110 additional compatibility optimization results.

The complete numerical endpoints follow. “Mean” and “max” name the frozen native-mean and native-maximum **reference policy**, not the reward being maximized in this diagnostic. Units are bits for IG and squared-posterior gain for Brier. Displayed endpoints are rounded summaries; original CHECK files retain full precision.

| Class | t | Original reward | Three-step reference | Least-sacrifice bracket |
|---|---:|---|---|---|
| Sensors | 3 | Brier | Max | [0, 0] |
| Sensors | 3 | Brier | Uniform | [0, 0] |
| Sensors | 3 | Brier | Mean | [0, 0] |
| Sensors | 3 | IG | Max | [2.220446049e-16, 6.661338148e-16] |
| Sensors | 3 | IG | Uniform | [2.220446049e-16, 4.440892099e-16] |
| Sensors | 3 | IG | Mean | [0, 4.440892099e-16] |
| Delay | 3 | Brier | Uniform | [0.06864535769, 0.06864563227] |
| Delay | 3 | IG | Uniform | [0.06930245909, 0.0693027363] |
| Delay | 4 | Brier | Brier | [0.002282926829, 0.00228293122] |
| Delay | 4 | Brier | IG | [0.002282926829, 0.00228293122] |
| Delay | 4 | Brier | Max | [0.0001865033852, 0.0001865077754] |
| Delay | 4 | Brier | Mean | [0.0005470748157, 0.0005470792059] |
| Delay | 4 | IG | Brier | [0.01372029439, 0.01372032077] |
| Delay | 4 | IG | IG | [0.01372029439, 0.01372032077] |
| Delay | 4 | IG | Max | [0.001120877514, 0.001120903899] |
| Delay | 4 | IG | Mean | [0.003287896672, 0.003287923057] |
| Irreversible | 5 | IG | Brier | [0, 4.440892099e-16] |
| Irreversible | 5 | IG | IG | [0, 4.440892099e-16] |
| Irreversible | 5 | IG | Max | [0, 4.440892099e-16] |
| Irreversible | 5 | IG | Count | [0, 4.440892099e-16] |
| Irreversible | 5 | IG | Uniform | [0, 4.440892099e-16] |
| Irreversible | 5 | IG | Mean | [0, 6.661338148e-16] |
| Generated | 3 | Brier | Max | [0.02887826368, 0.0288783518] |
| Generated | 3 | Brier | Count | [0.01304367342, 0.01304380625] |
| Generated | 3 | Brier | Uniform | [0.01199299469, 0.01199301548] |
| Generated | 3 | Brier | Mean | [0.02176454061, 0.02176462873] |
| Generated | 3 | IG | Max | [0.1006128585, 0.1006130842] |
| Generated | 3 | IG | Count | [0.04825730221, 0.04825779454] |
| Generated | 3 | IG | Uniform | [0.04450997997, 0.0445100571] |
| Generated | 3 | IG | Mean | [0.07664987934, 0.07665010508] |
| Generated | 4 | Brier | Max | [0.02938032261, 0.02938056169] |
| Generated | 4 | Brier | Mean | [0.01403451697, 0.01403475582] |
| Generated | 4 | IG | Max | [0.06708936235, 0.06708989218] |
| Generated | 4 | IG | Mean | [0.03303488651, 0.03303541584] |

## 5. The proposed examples

### Delayed sensing: a real cost, despite its small size

In `delayed_0.1_0.1`, the four worlds are two independent fair hidden bits U,V. Action 0 must be taken twice consecutively before it reads U with error .1; its first delay observation is a fair uninformative bit. Further action-0 choices retain access. Action 1 reads V with error .1 and resets the delay. The states track this delay, not the unknown bits themselves.

The selected **four-step Brier policy** has deficiency to the frozen **three-step Brier reference** in

\[
 [0.07199999999999995,\ 0.07200000000000006].
\]

Its maximum attainable four-step Brier gain is 0.4863219512195122. The compatibility result `case_01__t4__brier__to_brier` gives

\[
 \Delta\in[0.0022829268292657856,\ 0.0022829312195121187].
\]

The saved compatible policy earns 0.4840390200000001 and its explicit decoder has error 0.01999990000000046. The cap-relaxed dual upper reward is approximately 0.4840390243902465. Dividing the regret interval by R* gives **0.46942706%–0.46942796% of maximum Brier gain**, supporting “about .47%.”

This establishes substantially more than a bad representative: under the numerical bounds, satisfying the .02 cap costs positive reward, so merely choosing another exactly maximizing policy cannot repair the .02 failure. It does **not** show that every optimum's error equals .072; .072 is the selected primary policy's error, while the constrained calculation only excludes all optima from error <=.02.

Preserve the favorable later-budget outcome: the selected five-step Brier policy has own-reference upper error below 3.85e-15. Its Brier gain is about .5834443. The three-step self-comparison is zero by construction. Thus the selected own-reference errors follow approximately 0, .072, 0 across budgets 3,4,5. This is compatible with separate budget-specific optimization, not evidence that one continuing record lost and regained information.

Suggested sentence: “On delayed sensing, a numerically optimal four-step Brier policy has .072 error to its frozen three-step Brier reference. Meeting error .02 requires a numerically bounded Brier-gain sacrifice of about .00228293, or .47% of its four-step maximum gain; at five steps, the selected Brier policy again reproduces that reference.”

### Generated pilot: a larger cost to a different objective's reference

The class `fresh_hmm_2026096800_q4_s3_c0.2` has four candidate worlds, three hidden states, binary actions/observations, and frozen randomly generated transition/observation rows. It is one already-used supplied class, not a fresh model draw for this analysis. The source is the selected **three-step Brier policy**; the target is the frozen **three-step native-mean policy's full record**.

The primary source-to-target error is approximately .1595675677. The maximum three-step Brier gain is .33887135572625665. Result `case_03__t3__brier__to_weighted128` gives

\[
 \Delta\in[0.021764540606072358,\ 0.021764628732207247].
\]

Its compatible policy earns .3171067269940494 with decoder error .019999900000000854. The cap-relaxed upper reward is approximately .31710681512018446. Relative to maximum Brier gain, the sacrifice is **6.42265575%–6.42268176%**, supporting “about 6.4%” and absolute cost “about .0217646.”

This is a cost of reproducing this particular reference record, not the cost of attaining the native-mean objective's optimum, matching the old four-step audit, or reproducing all references at once. Nor does it establish that native mean dominates Brier: the primary alternatives can prefer incomparable information tradeoffs. A positive compatibility cost is meaningful without declaring native mean or maximum the uniquely correct scalar objective.

### Irreversible sensing: the tie case really has a compatible alternative

In `irreversible_0.1_0.1`, the initial action commits permanently to observing either U or V through the same error-.1 binary channel. The bits are independent and fair. The selected five-step information policy commits to one branch and has error approximately .236 to the frozen three-step Brier reference. Result `case_02__t5__information__to_brier` instead exhibits a policy with decoder error below 3.82e-16 and information-gain sacrifice in [0,4.45e-16]. The independently replayed maximum gain is about .9569093770 bits.

The numerical witness starts with probabilities approximately [.51725515,.48274485]; it is not literally the balanced Brier policy. Do not relabel that saved witness. Commission 05 separately explains a balanced policy as an exact mathematical witness: whichever branch is chosen, it produces the same repeated noisy-bit channel under the symmetric prior. The unmeasured bit remains fair. Information reward is independent of the initial branch mixture, so selecting a balanced initial branch and retaining the appropriate prefix recovers the balanced short reference without sacrificing the original objective. That written symmetry argument and the new saved numerical witness have distinct evidence status.

Use this as the positive control for the distinction: a selected information maximizer misses a capability, but the objective does not require that particular miss. Exact-float tie handling can select sharply different capabilities. The saved diagnostic supplies an existential compatible policy, not a statement that every information optimum or one common policy for all six references succeeds.

Suggested sentence: “On symmetric irreversible sensing, the selected five-step information policy misses the short Brier reference by .236, but a separately selected, reference-aware policy reproduces it with negligible numerical information loss. This miss reflects selection among reward-equivalent tradeoffs.”

## 6. What this adds to the paper, and claims to avoid

The old four-step-target audit asks how finite objectives trade off an extensive target family at a fixed three-step collection budget. The new primary comparison instead fixes particular short records and asks how separately optimized collectors at larger budgets can replace them. The compatibility calculation then asks whether a missed reference reflects a positive original-reward cost or a choice among similarly rewarded policies. Those are complementary questions and a useful empirical ending for the paper's central comparison of objective-induced capabilities.

Finite full-support world information and Brier exclude strictly Blackwell-dominated exact optima at each fixed horizon. The compatibility findings do not contradict that fact. Preserving one reference within a chosen error can require giving up another information benefit; a positive cost is not a dominance violation. Nor do the native finite scores inherit every eventual rich-J_w guarantee. Native mean can lose an earlier reference, and native maximum need not reproduce every native target even when it reproduces the six selected references. Keep the original matched-reward losses and incomparability findings visible.

For the integrated figure/prose:

- Label every new panel “collection budget t; reference horizon 3,” and identify separate policy selection at each t. Do not call the first successful tested budget a minimum simulation time over all policies or a stopping time of one continuing collector.
- State epsilon=.02 for compatibility. Results at the primary .01/.05 reporting thresholds do not automatically have the same reward costs.
- Keep primary collectors and favorable compatibility witnesses visually distinct. The latter use the reference in selection; they do not replace inconvenient primary dots.
- Make the 144 screened / 34 eligible / 22 positive / 12 negligible denominator explicit, at least in the appendix. Several target records coincide or overlap substantially, so avoid statistical frequency language.
- Label .47% and 6.4% “fraction of maximum Brier gain,” or present the absolute regret instead. The old 1%/5% constraints and sacrifice plots use fraction of attainable reward range. In particular, zero range does not make a relative-range percentage meaningful.
- Keep all four primary timeouts as missing checks. The explicit uniform prefix diagnostic can be described separately; it does not retrospectively make all four cells complete.
- Say “numerical bounds” and “compatible within numerical tolerance.” The empirical .02-cap results are not Lean theorems, exact zero certificates, or eventual-sufficiency statements.
- Preserve the two directions of a genuine fixed experiment pair if discussing incomparability. Transposing source/target method labels in a budget-t versus three-step matrix is insufficient when t>3.

I found no substantive mismatch between the executed compatibility formulation and the stated finite posterior-reward/cap question. The requested numbers and classifications survive independent arithmetic checks. No new optimization is needed to support these three examples. The later figure/prose milestone should be reviewed for these distinctions and final-size legibility rather than treated as already approved by this numerical review.

## 7. Exact evidence and replay scope

The authoritative completed boundary is [the 04:00:36 checkpoint](../simulation_time_2026-09-24/release_checkpoints/2026-09-24_040036/HANDOFF.md), not the launch-era README's pending-status text. Its ALLOWLIST JSON SHA-256 is

`1a40a8d1174afc1ec2baa6bd9bc2b78c09f2cc0c42e70277788bdb84983d1684`.

I verified all 1,173 hashed entries in ALLOWLIST.json and all 3,562 entries in LOCAL_EVIDENCE.json: 4,735 unique paths, with no missing or changed content. Those counts refer to entries inside the inventories, not the additional files carrying the inventory itself. The compact prior Git push excluded research outputs at the lead author's request; this review uses the preserved local evidence and does not imply these numerical arrays are present in a fresh clone.

Read the primary [protocol](../simulation_time_2026-09-24/budget_campaign/PROTOCOL.md), compatibility [protocol](../simulation_time_2026-09-24/budget_campaign/compatibility/PROTOCOL.md), [eligibility jobs](../simulation_time_2026-09-24/budget_campaign/compatibility/JOBS.json), [worker](../simulation_time_2026-09-24/budget_campaign/compatibility/worker.py), [checker](../simulation_time_2026-09-24/budget_campaign/compatibility/verify.py), and parent [LP certificate checker](../simulation_time_2026-09-24/budget_campaign/check.py). The seven original known-answer/corruption tests were inspected as implementation evidence; I did not rerun their optimizer-based fixture generation.

The fresh arithmetic replay did the following without importing the planning module or invoking a numerical optimizer:

1. Verified frozen source/input/result/certificate SHA bindings and recomputed the 144 eligibility decisions.
2. Independently propagated hidden-state masses breadth-first through the literal T/Z arrays, multiplied by causal action weights, and reproduced all 132 reference kernels and all 392 accepted primary kernels. Recomputed both posterior rewards and backward-recursion reward values for all primary information/Brier policies, including their frozen t=3 references.
3. Replayed all 2,352 accepted primary decoder/decision witnesses against the independently reconstructed source/reference kernels. Checked decoder normalization, world-independent usage, dual witness feasibility, and lower/upper errors.
4. For all 34 compatibility jobs, reran the checker's pure `verify_arrays` routine, which reconstructs every LP flow/decoder/TV constraint and reward coefficient without writing files. Separately replayed the physical policies, normalized decoders and posterior returns with the breadth-first implementation, and recomputed the box-repaired/untightened dual expression in extended precision. This adds an independent arithmetic implementation for physical/reward/dual evaluation, while the full sparse-constraint reconstruction uses the existing independently authored checker; these are not two wholly independent verification systems.
5. Checked the four failed uniform policies using the explicit prefix decoder, separately from their preserved incomplete multi-reference audits.
6. Rehashed the full frozen inventory after the main replay; no frozen file changed.

The independently reconstructed accepted kernels and reference-witness endpoints matched their saved values exactly in the used arithmetic. The largest posterior-reward discrepancy was 4.45e-16. Compatibility checker scalar outputs reproduced their saved CHECK values; the largest recorded LP residual among those 34 checks was 7.65e-13 or less. Near-zero brackets sometimes clamp small negative floating-point differences to zero; this is another reason not to call them exact zero proofs. No new Lean proof, global all-optima range audit, solver optimization, or full-primary native-master replay is claimed here.

The three main examples are bound by these original result directories:

- [Delayed four-step Brier to Brier](../simulation_time_2026-09-24/budget_campaign/compatibility/results/case_01__t4__brier__to_brier/CHECK.json).
- [Generated three-step Brier to native mean](../simulation_time_2026-09-24/budget_campaign/compatibility/results/case_03__t3__brier__to_weighted128/CHECK.json).
- [Irreversible five-step information to Brier](../simulation_time_2026-09-24/budget_campaign/compatibility/results/case_02__t5__information__to_brier/CHECK.json).

This review's arithmetic scratch report has SHA-256 `5816bc7e3f2d568e1ce738d3093d7def00a44102ccc992e2505392287173d9ec`; it is not substituted for the frozen evidence. The durable conclusions and complete comparison table are recorded above, in the requested note only.
