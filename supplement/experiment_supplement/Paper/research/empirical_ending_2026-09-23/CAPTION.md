# Standalone candidate caption

**Finite objectives select different reusable evidence.** Every policy collects
three action–observation pairs. The audit `A_{3,4}` is its largest, over all
four-step target policies, smallest worst-world total-variation error achievable by a world-independent
randomized decoder; smaller is better. Each case supplies four or eight candidate hidden-state models, with the
actual model unknown. All policies can depend on their full observation/action
history. Native planning uses 131 targets of length at most three; the 32,768
four-step targets are evaluated only after planning.

(a) All twelve model settings at the forty-second planning allowance. Information
gain and posterior Brier concern the entire world label. Fixed native weights
minimize a retained weighted target loss; finite minimax minimizes the largest
training-target loss. Uniform actions are a control. Symbols show numerical
interval midpoints; checked interval widths are at most 2.1e-8, below the plotting
scale. A/B mark two independent generator seeds reused across the parameter grid.
The parameter alpha is the Dirichlet concentration used to generate model rows.

(b) Held-out improvement of fixed native weights over information/Brier at planning
allowances of two, ten, and forty seconds. Each thin curve is one setting; thick
curves are descriptive medians. Positive values favor fixed native weights.
Posterior dynamic programming takes approximately 5 ms, so equal planning
allowances do not mean equal work. Evaluation and witness verification are
additional to planning.

(c) The same comparison against policies selected to improve the training-target
maximum while sacrificing at most 0%, 1%, or 5% of the attainable posterior reward
range. The x-axis shows the **actual** reward loss. These are selected constrained
policies, not all near-optimal policies. All use forty-second planning endpoints.
Thick points pair the median actual reward loss with the median audit difference
at each allowed tolerance; the connecting curves are guides, not a proved frontier.
For perspective, fixed native weights themselves sacrifice a median 21.17% of the
attainable Brier range.

These finite numerical comparisons show capability/reward/computation tradeoffs,
not general dominance or optimization of eventual `J_w`. Every tested native and
baseline record pair is numerically incomparable at collection time three.
Numerical intervals are floating-point witness bounds, not statistical confidence
intervals or exact outward-rounded certificates. The twelve settings share only
two independent seed families. The figure is a proposed presentation of completed
data and has not been inserted into the paper.
