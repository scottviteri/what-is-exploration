# SAFE/FAST controlled computation protocol

Frozen before outcomes, 23 September 2026. This study separates scoring horizon,
finite objective truncation, and optimizer computation. It is not learner training
and does not claim a practical advantage on general environments.

The existing Lean environment has binary stream worlds, SAFE observations
`theta[0],0,theta[1],0,...`, FAST observations `theta[1],theta[2],...`, and
an irreversible root action. Later actions are retained in complete records.
The infinite-world calculations use exact finite-coordinate quotients of this
one fixed infinite environment. Separate finite controls fix d in {1,2,4,8,16},
allow all 2^d independent assignments to bits 0,...,d-1, and set later bits to 0.
A curve never increases d with H.

## Objectives fixed prospectively

The rich background samples target depth n>=1 with weight 2^-n, precision m>=0
with weight 3/4^(m+1), and uniformly samples every depth-n behavioral policy tree
whose action-row probabilities lie on {0,1/2^m,...,1}. Off-depth rows are fixed.
All such finite trees have positive weight, and dyadic row approximation is dense
in full finite native records. Each target retains its full action-observation
record. The new written reduction in DERIVATION.md collapses this background
for this particular environment to its dyadic root probabilities; this reduction
is independently checked numerically, not claimed Lean-formalized.

For epsilon in {1/100,1/20,1/4}, compare

- fixed: epsilon*b + (1-epsilon)*point_mass_FAST_1;
- moving: epsilon*b + (1-epsilon)*point_mass_FAST_H.

They coincide at H=1. Every compared collector uses the same realized weights.
The collector root SAFE probability q is optimized over [0,1]. The written
full-record equivalence justifies this reduction for this interface; it is not a
restriction to observation-independent later policies.

Primary H: 1,...,32,48,64,96,128, for infinite worlds and all five fixed finite d.
Primary target truncation N=12,M=4. Retain original coefficients. Exact omitted
background mass is beta=1-(1-2^-N)*(1-4^(-M-1)); full-objective tail is epsilon*beta.
The heavy target is retained exactly even when its depth exceeds N.

Sensitivity uses H in {1,2,4,8,16,32,64,128}, all the same worlds/epsilons/schedules,
and (N,M) in {(8,4),(16,4),(12,2),(12,6)}. No outcome-dependent cells are omitted.

For each cell report retained-objective optimum numerical primal/dual values,
exact-rational global lower and feasible candidate upper bounds, the full-value
interval after charging the tail once, and an outer interval containing every
full-objective optimizer's q. The latter optimizes q in a retained-loss sublevel
set using candidate full upper bound plus an explicitly charged 1e-9 numerical
slack; exact-rational dual bounds certify its outer endpoints. It is an enclosure,
not an assertion that every enclosed q is optimal. The resulting SAFE_1 deficiency
interval is [(1-q_max)/2,(1-q_min)/2]. Finite-face ties are reported rather than
selecting the most favorable optimum. Exact all-optima assertions come only from
the existing Lean theorem or explicitly given analytic finite-cube arguments.

## Independent checks before the primary grid

Compare the four-flow compressed deficiency LP with a literal full-record decoder
LP at t,n in {1,2,3}, d in {1,2,3}, and q,p in {0,1/2,1}: 243 cases.
Also check the infinite-prefix quotient d=max(t,n)+1: 81 cases.
Another 32 fixed-seed cases use observation-dependent randomized later action rows
on {0,1/4,1/2,3/4,1}, t,n in {2,3}, d in {2,3}, and root probabilities including
quarter points. Store both LP witnesses and compare values within 1e-8, retaining
any failure. Replay literal decoder rows and worldwise TV errors independently.
The full independent bit cube is essential to the symmetrization argument;
correlated world subsets are outside this compressed solver's scope.

## Information-gain controls

For each finite d, use the uniform prior on its 2^d actual worlds and the literal
finite-horizon expected posterior KL gain. Its value is
q*min(ceil(H/2),d)+(1-q)*min(H,d-1) bits. Record every optimal q, including [0,1]
on ties. This uses finite alphabets, a finite positive-prior model class and the
source-permitted finite-horizon discount (Orseau et al., pinned author PDF pp3-5).
An uncountable fair-product prior is not substituted for the source's countable
class. No predictive-surprisal control is labeled information gain.

## Resources and integrity

At most four CPU workers, pinned to CPUs 12-15, with BLAS/HiGHS threads held to one;
no GPU. Record wall time and solver time separately from H. Initial compute budget
approximately 15 minutes. Save all outcomes/failures, compressed primal/dual
witnesses, exact tail/bound certificates, source hashes and reproducible plots.
No shared manuscript, Lean, support ledger, frozen historical data or Git mutation.
