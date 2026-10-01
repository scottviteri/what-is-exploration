# Scientific scope revision — 24 September 2026

This note supersedes the main-figure placement recommendations in the frozen README and ASSESSMENT. Those files remain unchanged as part of the completed historical checkpoint. The numerical results, proofs, certificates, failures and artifact bindings are not withdrawn.

the lead author identified the governing issue: the paper's exploration order does not choose a minimax compromise between incomparable policies. Selecting on depth-three targets and evaluating a depth-four maximum tests a finite approximation and transfer between target horizons. It does not itself test which intrinsic objective better respects the order, or eventual native sufficiency. Alternative policies at the same horizon already supply counterfactual experiments; the extra target step has no necessary role in the paper's central argument.

The revised [independent completion review](MISSING_CITATIONS_COMPLETION_REVIEW.md), particularly its substantive reassessment, supports these distinctions:

- Max aggregation is generally only weakly order-preserving. The checked exact/noisy-bit example retains the same worst-target error despite a strict capability improvement.
- On finite world classes with a full-support prior, exact whole-world information and Brier optimization already exclude strictly Blackwell-dominated fixed-horizon record experiments. These are positive controls for order-respect under those assumptions.
- The measured pairwise incomparabilities describe compromises. They establish neither order violations nor membership in the full feasible frontier; an unexamined third policy could dominate a selected policy.
- The finite 128-target mean is not the rich eventual J_w construction. Neither its wins nor its losses on the chosen maximum establish the latter's success or failure.
- The exact Lean archived-table result concerns one weighted-native/ordinary-Brier pair. It does not formalize all matched policies, optimizer selection, or eventual continuation.

The completed package should therefore remain supporting research about finite objective preferences, longer-target transfer and computational verification. No replacement main figure is selected. A future main experiment needs a stated order-level or capability-acquisition question before choosing horizons, aggregation or plotting conventions. Candidate questions include actual dominated objective optima under faithful source specifications, or quantitative capability guarantees under approximate optimization with a known feasible sufficient reference. These are design directions, not approved protocols or announced findings.

An exact domination demonstration requires a valid forward simulation and positive reverse deficiency, together with optimality evidence if the claim concerns an objective optimizer. Approximate forward simulation must be labelled approximate. A process-level claim additionally requires the appropriate growing-record or all-continuations argument. No additional optimization on the current inspected grid will turn scalar comparisons into those claims.

This is a new interpretive note outside the earlier CHECKS_FREEZE file list. It modifies no frozen artifact, manuscript, shared formal record, or Git state.
