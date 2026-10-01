# Written reduction and certification boundary

This is a new written derivation, independently checked on finite examples. It is
not an additional Lean theorem. The existing Lean SAFE/FAST all-optima theorem
avoids this reduction and remains the authority for its infinite-world claim.

At positive collection time t, a policy's acquired record is Blackwell-equivalent
to `(root branch, bits observed on that branch)`. Projection gives one decoder.
For the reverse decoder, given the root and the entire branch observation stream,
sample the later actions sequentially using the original policy's conditional
rows. The environment ignores those later actions, so this recreates the full
record law in every world. The same argument applies independently to each target
policy. Its experiment therefore depends, up to exact equivalence, only on its
root SAFE probability p and depth n. This does not discard action randomness:
the reverse decoder reconstructs it.

Write A_S={0,...,ceil(t/2)-1}, A_F={1,...,t}; target sets B_S and B_F use n in place
of t. For a finite-d control intersect each set with {0,...,d-1}. All other bits
are fixed constants. Each calculation on infinite worlds depends on only the
finite union of these sets, and the infinite class contains every assignment to
that union. Thus the finite independent bit cube is an exact quotient for this
particular pair of finite experiments, not a finite-world replacement theorem.

Average an arbitrary decoder over the group that flips each relevant independent
bit. Convexity of TV and invariance of both experiments do not increase its worst
world error. The averaged source-to-target branch allocation is independent of
observed bit values. Given source branch r and output target branch s, copying
known target bits is optimal; each unknown target bit must be guessed uniformly.
The probability of the one correct target output is
`a_rs=2^(-|B_s minus A_r|)`. Missing-bit guesses can be generated independently.

Let x_rs be unconditional source-branch mass allocated to target branch s. Its row
sums are q and 1-q. Correct output mass for target branch s is c_s=sum_r a_rs*x_rs.
The target places mass p on its correct SAFE output and 1-p on its correct FAST
output. TV equals one minus the overlap, so exact deficiency is

```
1 - max (y_S+y_F)
x_rs >= 0; sum_s x_Ss=q; sum_s x_Fs=1-q;
0 <= y_S <= p; 0 <= y_F <= 1-p;
y_s <= sum_r a_rs*x_rs.
```

This supplies both an achievable equivariant decoder and a lower bound against
all decoders, including value-dependent branch allocations before symmetrization.
It need not hold on a correlated subset of the bit cube.

For each positive depth n there are finitely many policy rows before n. Giving
every row an independent uniform dyadic-grid probability assigns positive mass
to every finite dyadic tree. Rounding each of the finitely many rows, with the
usual per-step TV telescoping bound, uniformly approximates any depth-n record.
Hence the background is genuinely rich on full record alphabets. The preceding
Blackwell equivalence makes every non-root row integrate out of its weighted
loss. Only the uniform dyadic root remains. Repeated root probabilities from
different precision levels are aggregated with their original exact weights.

All losses lie in [0,1]. Retaining n<=N and m<=M gives beta as in PROTOCOL.md.
For retained master lower B and feasible candidate upper U, the full optimum is
in [B,U+epsilon*beta]; the candidate's full regret is at most U+epsilon*beta-B.
The tail is never renormalized or charged twice.

For any genuine full optimizer q*, retained loss(q*) <= U+epsilon*beta.
Therefore minimizing/maximizing q on that retained-loss sublevel set gives outer
bounds for ALL full optima. The computation additionally permits 1e-9 slack,
records that slack, and certifies the resulting bounds by exact rational dual
calculations. These are generally wider than the exact retained-optimum face.

At H>=2d-1 on a fixed finite cube, SAFE knows every unknown bit and has zero loss
to every native target. The background gives positive weight to the actual SAFE_1
target. Its exact loss is (1-q)/2, so every full objective optimum has q=1.
Every information-gain optimizer also chooses SAFE initially at those horizons;
all later actions are arbitrary. This saturation explains why
fixed-d controls cannot perpetuate the infinite-world moving-emphasis failure.
The infinite-world all-H failure is already Lean-checked, not inferred from this
finite grid. Fixed-weight convergence likewise remains a rate-free Lean result;
finite numerical curves alone cannot prove asymptotic or runtime claims.
