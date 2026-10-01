# Post-experiment mechanism analysis

15 September 2026. the lead author asked for a detailed explanation and analysis of why the
fixed objective benchmark gave mixed results. These are exploratory follow-up
diagnostics, not changes to the frozen design, objective or screening criterion.
Original numerical outputs and their audits are preserved.

Questions:

1. What posterior score does the seven-question zero-one evaluation compute?
   How does its squared-loss counterpart relate to the Brier baseline?
2. In each environment, can the BEST native-optimal collector catch the Brier
   guarantee, or is the observed gap more than an unfavorable tie choice?
3. Which target errors increase when a Brier-optimal record replaces the saved
   native-optimal record? Check both complete-record deficiency directions.
4. Why do delayed and irreversible examples give different comparison outcomes?
   Inspect simple schedules and root-choice probabilities.
5. What normalized Brier regret do the native 1%-regret worst-mean witnesses
   actually have, and vice versa? Equal regret percentages are different policy
   constraints; this diagnostic does not make optimization difficulties equal.

Use the frozen saved models. Add best-mean native selected-set LPs at the same
saved thresholds, with exact full-history linear decision coefficients (never
maximize an upper-bound epigraph). Independently replay new policies and
certificates using the existing auditor, and evaluate their actual native loss
with separately assembled fixed-source decoder LPs. Report floating-point scope.
Any interpretation that is not established by these diagnostics stays labelled
as a hypothesis. No stronger main-paper claim is introduced by this analysis.
