# Noisy-diagnostic transfer theory

[Nine-page proof note](theory.pdf) ([source](theory.tex)). Written research with exact finite certificates, 13 September 2026. No Lean or selected-paper claim is changed.

The note proves three complementary results:

- **A reusable finite transfer LP.** A common randomized decoder must handle every joint distribution of separately decoded noisy diagnostics. Checking the vertices of marginal-sign cells proves an affine inequality `δ(E,T) ≤ b + κ L(E)` for every finite-signal acquired experiment, regardless of the collection horizon. This handles unknown dependence between diagnostic outputs. It is stronger than merely composing through one diagnostic, but can remain conservative relative to a decoder tailored to the full source experiment.
- **Explicit stochastic residuals.** For two BSC(e) diagnostics and an independent joint target at the same noise, the optimal common-repair residual is `e(1−2e)` for `e≤1/3`; the note gives the remaining range too. For more accurate equal diagnostic noise `d≤min(e,1/4)`, it is `d(1−2e)²/(1−2d)`. Majority-of-three diagnostics reduce the residual from .08 to 28/1475 at physical noise .1, before accounting for their acquisition cost.
- **A pilot-feasible exact obstruction.** A specified four-step randomized collector exactly simulates both noisy singles and their tagged mixture but has joint LR deficiency `2[e(1−e)(1−2e)]²`. An explicit bitwise decoder and a parity-guessing decision attain matching upper/lower bounds. Adding LR to a positive-weight target loss excludes this collector at exact optimality because the enlarged minimum remains zero. Repeated targets still expose further losses.

A padding proposition also explains why a longer collection budget can enlarge a fixed objective's near-optimal experiment set when its optimum stays unchanged, worsening the worst permitted capability without making any one policy lose evidence.

The near-optimal bound retains the finite-budget diagnostic minimum, optimization gap, and any supplied target-generation/model/evaluation approximation errors. A lower noise residual does not automatically improve the final guarantee when stronger diagnostics have a positive acquisition minimum.

## Certificate artifacts

`certificates.py` implements the two-binary-diagnostic case. It runs floating-point LP searches, reconstructs an exact rational decoder, and recomputes a valid exact rational intercept. The saved inequalities are therefore exactly feasible; search optimality is not thereby certified.

`certificates.json` has 180 rows: three physical noise pairs, two diagnostic sources, six requested targets, and five design losses. All 9,120 rational vertex checks passed. A separate audit reconstructed the sign-cell vertices independently and replayed the same 9,120 inequalities. Four external correlated-noise channel controls and the pilot's exact four-step identities are retained separately from production-policy outcomes.

Each row has:

- `eps`: physical sensor error pair defining the requested target;
- `diagnostic_eps`: the two diagnostic error rates;
- `diagnostic_source`: `singles` or `majority3`;
- `word`: LR, LLR, LRR, LLL, RRR, or the protocol's adaptive target;
- `weights`: normalized diagnostic weights, currently 1/2 each;
- `intercept`, `slope`, `decoder`: exact rational common-repair certificate;
- `at_loss`: design point used to select that affine certificate, not a restriction on where it is valid.

Use the minimum of the applicable affine bounds at the actual loss bound. For protocol weighted sum S, single-diagnostic average loss is at most S/.4. For `native_repeats`, majority-of-three diagnostic average loss is at most S/.2. Near-optimal-set substitution uses S*+η, retaining any positive S*. These conversions do not apply an objective gap from IG or Brier directly to a native diagnostic loss.

## Reproduction

From this directory:

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 certificates.py
pdflatex -interaction=nonstopmode -halt-on-error theory.tex
pdflatex -interaction=nonstopmode -halt-on-error theory.tex
```

The final note builds to nine pages without LaTeX warnings. The broader study's independent audit and production results are owned by the parent directory; this theory note makes no completion claim for that grid.
