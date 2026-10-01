# What the completed checks change

The broader 22-class comparison can now support the empirical ending. The earlier preference for twelve settings was partly about complete controls and interpretable reward costs, not just verification. This pass supplies those missing pieces for all 22 classes. Its main scientific value is comparing the capabilities selected by specified finite objectives, including cases unfavorable to the native objectives.

## Three comparisons, three questions

| Comparison | What is held fixed | Weighted-native outcome | What it supports |
|---|---|---|---|
| Ordinary world-posterior Brier | Model class, prior, policy space, collection length and audit | 18 wins, 2 ties, 2 losses | The selected finite mean often has lower worst-target error than maximizing Brier reward on these classes. |
| Native minimax with a 5%-Brier reward allowance | The above, and a control reward floor relative to its attainable range | 16 wins, 6 losses | A strong favorable near-optimal control changes the comparison; native frequently gives up more Brier reward. |
| Native minimax retaining the fixed native reference's Brier reward | The above, and at least the reference's actual reward, up to the declared allowance | 6 wins, 1 tie, 15 losses | A constrained finite maximum often gives lower error on longer targets than this particular finite mean while retaining its Brier reward. |

The first two rows compare envelopes of saved native representatives. The last compares one predetermined reference per class with its own constrained control; the counts must not be interpreted as the effect of changing a single constraint on otherwise identical paired policies. The native reference is selected by lexical cell ID, without the new held-out scores. This fixes selection for the diagnostic without making the already inspected classes fresh confirmation.

The last control is itself a native optimization: it minimizes the worst depth-three target error under a Brier floor. It does not maximize Brier or represent what an arbitrary Brier learner would choose. The reference is feasible, so the training maximum is guaranteed not to be worse at an exact optimum. The depth-four audit is a separate measurement; no such training guarantee supplies its result. The median control-minus-native depth-four error is −0.0030462851.

The original minimax objective also has favorable outcomes: against ordinary Brier its counts are 19 wins, 1 tie and 2 losses; against the 5% control they are 18 wins, 1 tie, 2 losses and 1 mixed comparison across representatives. The distinction between a mean and a maximum is consequential. These results do not select a uniquely correct native weighting.

## What the order check adds

A single worst-target error is a summary of many capabilities. It is not the experiment order. For 84 of 88 selected pairs in the original-method comparisons, both directed record deficiencies have positive numerical lower bounds. For the matched diagnostic, 21 of 22 selected pairs have this property. These pairs are numerically incomparable: each record lacks something available from the other. The remaining pairs are equivalent within the stated numerical tolerance. This concerns the collected three-interaction records, not all optimizers or later continuations.

One adverse delayed case now has exact Lean support. After interpreting the saved matrix entries as exact rationals and normalizing the rows exactly, native-to-Brier deficiency lies in [0.08782201, 0.08782202], and Brier-to-native deficiency lies in [0.02766393, 0.02766394]. Lean checks valid tables, real-decoder lower bounds and explicit stochastic upper decoders. It does not check the whole simulator, optimality of the archived policies, or every target in the figure. The separate exact physical replay after policy quantization is preserved. See FORMAL_SCOPE.md.

## Recommended presentation

Use the complete 22-class comparison as the main empirical example, with the reward-matched finding stated beside it. CANDIDATE_22_PAPER.pdf shows all six ordinary method families, the complete five-percent control comparison and actual reward sacrifice. CANDIDATE_22_MATCHED_PAPER.pdf is an alternative main image when the finite-mean versus constrained-maximum question is foregrounded; it keeps the same six-method comparison but pairs the fixed references with their matched controls.

The matched finding should not be hidden behind the more favorable sixteen-versus-six count. Present both in the empirical text, and retain the second figure as nearby supporting evidence if only one main image is used. The twelve-setting study remains a separate computation-budget and rich-background comparison. Do not pool its different target library, weights, model grid or witness accounting with these 22 classes.

The 5.5-inch renderings use the actual manuscript text width, with 7.3-point row labels, and retain all cases. Larger standalone versions help inspect small intervals. No manuscript integration or page-limit changes were made.

A defensible claim is: on these finite model classes, optimizing different rewards or different aggregations of native capability selects measurably different evidence; posterior reward constraints change the comparison, and a smaller worst-target error usually does not imply dominance of the full record experiment. These are descriptive, post-design findings about supplied models and model-based planning. They do not show eventual J_w superiority or failure, all-optima behavior, online learning performance, or a population-level effect.

## Validation and costs

The 18 missing posterior controls and one uniform audit are complete. Their fresh numerical replay checks 622,592 target witnesses and rejects four deliberately corrupted certificates. The matched pass adds 22 checked planners and 44 audits, with 1,441,792 retained and replayed target witnesses. Aggregate hashes were refreshed after the last replay; BINDING_REPAIR.json retains the prior reports and verifies unchanged scientific content.

The matched controls required 49.70 summed planning seconds. The control and reference audits required 3,255.58 and 4,056.60 summed worker wall-seconds respectively, under concurrent load. These totals are not elapsed wall time for the campaign or equal-compute budgets. Existing references, their original planning, and any model acquisition are additional costs. All numerical workers from this pass have finished.

The three isolated Lean modules compile, their explicit axiom reports use only standard Lean axioms, and the full build passes. The initial shared classification failure is preserved; after concurrent integration, the final paper-support and axiom audit passes. No shared support ledger, root imports or manuscript files were changed in this pass. The modules are classified as supporting research with no selected manuscript claim. This is not a claim that the complete empirical figure is Lean-verified.

A new numerical campaign is not needed to freeze this descriptive result. A future confirmation should fix which of the comparisons above it tests, retain favorable baseline cases, declare the weighting and selection rule in advance, and draw genuinely new classes. More compute on the same already inspected grid cannot turn it into independent confirmation.
