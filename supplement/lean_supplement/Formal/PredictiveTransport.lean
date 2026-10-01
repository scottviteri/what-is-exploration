import Formal.DualCertificate

/-!
# Predictive simulators: local response error gives a horizon-linear audit bound

**Relevance:** direct support for the current predictive-state investigation.

The paper-level argument says that a world-independent learned causal simulator whose
one-step response rows are uniformly within `ε` in total variation has rollout error at
most `n * ε` at horizon `n`.  This file checks the finite algebra behind that claim.

We work with a fixed finite state type `X` and time-dependent Markov kernels.  A fully
history-dependent finite-horizon causal process is an instance: take `X` to be the finite
type of padded histories and let each transition append one response.  Keeping this
generic fixed-state form makes the result reusable for predictive states, observable
features, and full-history states alike.

The final theorem, `finiteDeficiency_modelRollout_le`, includes the acquired experiment.
Each acquired signal selects one estimated initial law and transition family; if every
selected model is within `ε₀` initially and `ε` locally of every compatible true world,
then rolling it out is one stochastic decoder with directed deficiency at most
`ε₀ + n * ε`.  The final high-probability theorem also performs the acquired-signal
mixture split: if bad signals have probability at most `δ`, the bound is
`δ + ε₀ + n * ε`.
-/

set_option linter.unusedSectionVars false

namespace IdExp
namespace PredictiveTransport

open Finset Set

variable {X Y Θ S : Type*} [Fintype X] [Fintype Y]

/-- Push a finite law through a finite stochastic rule.  This is
`finiteDecisionLaw` with the parameter row already selected. -/
noncomputable def finiteBind (p : X → ℝ) (G : X → Y → ℝ) : Y → ℝ :=
  fun y => ∑ x, p x * G x y

/-- Binding a probability vector through a stochastic rule gives a probability vector. -/
theorem isDist_finiteBind (p : X → ℝ) (hp : IsDist p)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) :
    IsDist (finiteBind p G) := by
  constructor
  · intro y
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (hp.1 x) ((hG x (Set.mem_univ x)).1 y)
  · unfold finiteBind
    rw [Finset.sum_comm]
    calc
      ∑ x, ∑ y, p x * G x y = ∑ x, p x * ∑ y, G x y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
      _ = ∑ x, p x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [(hG x (Set.mem_univ x)).2, mul_one]
      _ = 1 := hp.2

/-- Convexity of TV with common source weights.  Changing a response kernel row by row
costs at most the source-weighted average of the row TV distances. -/
theorem finiteTV_finiteBind_same_source_le_sum
    (p : X → ℝ) (hp : IsDist p) (G H : X → Y → ℝ) :
    finiteTV (finiteBind p G) (finiteBind p H) ≤
      ∑ x, p x * finiteTV (G x) (H x) := by
  unfold finiteTV finiteBind
  have hdiff : ∀ y,
      (∑ x, p x * G x y) - (∑ x, p x * H x y) =
        ∑ x, p x * (G x y - H x y) := by
    intro y
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [hdiff]
  calc
    (1 / 2 : ℝ) * ∑ y, |∑ x, p x * (G x y - H x y)| ≤
        (1 / 2 : ℝ) * ∑ y, ∑ x, |p x * (G x y - H x y)| := by
      refine mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ = (1 / 2 : ℝ) * ∑ y, ∑ x, p x * |G x y - H x y| := by
      congr 2 with y
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (hp.1 x)]
    _ = ∑ x, p x * ((1 / 2 : ℝ) * ∑ y, |G x y - H x y|) := by
      rw [Finset.sum_comm]
      calc
        (1 / 2 : ℝ) * ∑ x, ∑ y, p x * |G x y - H x y| =
            (1 / 2 : ℝ) * ∑ x, p x * ∑ y, |G x y - H x y| := by
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
        _ = ∑ x, p x * ((1 / 2 : ℝ) * ∑ y, |G x y - H x y|) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring

/-- Uniform form of `finiteTV_finiteBind_same_source_le_sum`. -/
theorem finiteTV_finiteBind_same_source_le
    (p : X → ℝ) (hp : IsDist p) (G H : X → Y → ℝ) {ε : ℝ}
    (hlocal : ∀ x, finiteTV (G x) (H x) ≤ ε) :
    finiteTV (finiteBind p G) (finiteBind p H) ≤ ε := by
  calc
    finiteTV (finiteBind p G) (finiteBind p H) ≤
        ∑ x, p x * finiteTV (G x) (H x) :=
      finiteTV_finiteBind_same_source_le_sum p hp G H
    _ ≤ ∑ x, p x * ε :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hlocal x) (hp.1 x)
    _ = ε := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- One-step perturbation bound: source-law error plus response-kernel error. -/
theorem finiteTV_finiteBind_le
    (p q : X → ℝ) (hp : IsDist p) (G H : X → Y → ℝ)
    (hH : H ∈ stochasticRules X Y) {ε : ℝ}
    (hlocal : ∀ x, finiteTV (G x) (H x) ≤ ε) :
    finiteTV (finiteBind p G) (finiteBind q H) ≤ ε + finiteTV p q := by
  calc
    finiteTV (finiteBind p G) (finiteBind q H) ≤
        finiteTV (finiteBind p G) (finiteBind p H) +
          finiteTV (finiteBind p H) (finiteBind q H) :=
      finiteTV_triangle _ _ _
    _ ≤ ε + finiteTV p q := add_le_add
      (finiteTV_finiteBind_same_source_le p hp G H hlocal)
      (finiteTV_postprocess_le p q H hH)

section Iterate

variable [Fintype S]

/-- Time-inhomogeneous finite-state rollout. -/
noncomputable def markovIterate (p : S → ℝ) (K : ℕ → S → S → ℝ) :
    ℕ → S → ℝ
  | 0 => p
  | n + 1 => finiteBind (markovIterate p K n) (K n)

@[simp] theorem markovIterate_zero (p : S → ℝ) (K : ℕ → S → S → ℝ) :
    markovIterate p K 0 = p := rfl

@[simp] theorem markovIterate_succ (p : S → ℝ) (K : ℕ → S → S → ℝ) (n : ℕ) :
    markovIterate p K (n + 1) = finiteBind (markovIterate p K n) (K n) := rfl

/-- A rollout of stochastic kernels remains a probability vector. -/
theorem isDist_markovIterate (p : S → ℝ) (hp : IsDist p)
    (K : ℕ → S → S → ℝ) (hK : ∀ t, K t ∈ stochasticRules S S) :
    ∀ n, IsDist (markovIterate p K n)
  | 0 => hp
  | n + 1 => isDist_finiteBind _ (isDist_markovIterate p hp K hK n) _ (hK n)

theorem finiteTV_self (p : S → ℝ) : finiteTV p p = 0 := by
  simp [finiteTV]

/-- **Finite trajectory telescoping.** Initial TV error plus the sum of uniform local
response errors controls the full rollout.  To make the final state contain the entire
trajectory, instantiate `S` with padded finite histories. -/
theorem finiteTV_markovIterate_le
    (p q : S → ℝ) (hp : IsDist p)
    (P Q : ℕ → S → S → ℝ)
    (hP : ∀ t, P t ∈ stochasticRules S S)
    (hQ : ∀ t, Q t ∈ stochasticRules S S)
    {ε : ℝ} (hlocal : ∀ t s, finiteTV (P t s) (Q t s) ≤ ε) :
    ∀ n, finiteTV (markovIterate p P n) (markovIterate q Q n) ≤
      finiteTV p q + (n : ℝ) * ε
  | 0 => by simp
  | n + 1 => by
      calc
        finiteTV (markovIterate p P (n + 1)) (markovIterate q Q (n + 1)) ≤
            ε + finiteTV (markovIterate p P n) (markovIterate q Q n) := by
          rw [markovIterate_succ, markovIterate_succ]
          exact finiteTV_finiteBind_le
            (markovIterate p P n) (markovIterate q Q n)
            (isDist_markovIterate p hp P hP n) (P n) (Q n) (hQ n) (hlocal n)
        _ ≤ ε + (finiteTV p q + (n : ℝ) * ε) := by
          have ih := finiteTV_markovIterate_le p q hp P Q hP hQ hlocal n
          linarith
        _ = finiteTV p q + ((n + 1 : ℕ) : ℝ) * ε := by
          push_cast
          ring

/-- Same-initial-law specialization. -/
theorem finiteTV_markovIterate_same_initial_le
    (p : S → ℝ) (hp : IsDist p)
    (P Q : ℕ → S → S → ℝ)
    (hP : ∀ t, P t ∈ stochasticRules S S)
    (hQ : ∀ t, Q t ∈ stochasticRules S S)
    {ε : ℝ} (hlocal : ∀ t s, finiteTV (P t s) (Q t s) ≤ ε)
    (n : ℕ) :
    finiteTV (markovIterate p P n) (markovIterate p Q n) ≤ (n : ℝ) * ε := by
  simpa [finiteTV_self] using
    finiteTV_markovIterate_le p p hp P Q hP hQ hlocal n

end Iterate

/-! ### From per-signal simulators to directed deficiency -/

variable [Fintype S]

/-- Decoder error is bounded by the acquired-law-weighted average of the TV errors of
its individual signal rows. -/
theorem decodeErr_le_weighted_rowTV
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (F : FiniteExperiment Θ Y) (G : X → Y → ℝ) (θ : Θ) :
    decodeErr E F G θ ≤ ∑ x, E θ x * finiteTV (G x) (F θ) := by
  let H : X → Y → ℝ := fun _ => F θ
  have hconst : finiteBind (E θ) H = F θ := by
    funext y
    unfold finiteBind H
    rw [← Finset.sum_mul, (hE θ).2, one_mul]
  change finiteTV (finiteBind (E θ) G) (F θ) ≤ _
  have hmix := finiteTV_finiteBind_same_source_le_sum (E θ) (hE θ) G H
  simpa only [hconst, H] using hmix

/-- If every acquired signal selects a target-law approximation within `c`, mixing those
rows with the acquired experiment is still within `c`. -/
theorem decodeErr_le_of_rowwise
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (F : FiniteExperiment Θ Y) (G : X → Y → ℝ)
    (θ : Θ) {c : ℝ} (hrow : ∀ x, finiteTV (G x) (F θ) ≤ c) :
    decodeErr E F G θ ≤ c := by
  let H : X → Y → ℝ := fun _ => F θ
  have hconst : finiteBind (E θ) H = F θ := by
    funext y
    unfold finiteBind H
    rw [← Finset.sum_mul, (hE θ).2, one_mul]
  change finiteTV (finiteBind (E θ) G) (F θ) ≤ c
  rw [← hconst]
  exact finiteTV_finiteBind_same_source_le (E θ) (hE θ) G H hrow

/-- **Good-signal simulator bound.**  Suppose the acquired signal `x` selects a valid
target-law approximation `G x`.  If, in every world, the total probability of signals
whose selected row is not certified is at most `δ`, and every certified row is within
`ε` of the target law, then the selected-row decoder witnesses deficiency at most
`δ + ε`.

This is the finite-experiment translation of a high-probability all-policy model-estimation
guarantee: fix one target policy, let `G x` be the learned model's rollout law, and use the
same learned model for every target to obtain coherent simulation. -/
theorem finiteDeficiency_good_rows_le
    [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
    (Good : Θ → X → Prop) [∀ θ x, Decidable (Good θ x)]
    {δ ε : ℝ} (hε : 0 ≤ ε)
    (hbad : ∀ θ, (∑ x, if Good θ x then (0 : ℝ) else E θ x) ≤ δ)
    (hgood : ∀ θ x, Good θ x → finiteTV (G x) (F θ) ≤ ε) :
    finiteDeficiency E F ≤ δ + ε := by
  classical
  apply finiteDeficiency_le_of_decoder E F G hG (δ + ε)
  intro θ
  calc
    decodeErr E F G θ ≤ ∑ x, E θ x * finiteTV (G x) (F θ) :=
      decodeErr_le_weighted_rowTV E hE F G θ
    _ ≤ ∑ x, E θ x * (if Good θ x then ε else 1) := by
      apply Finset.sum_le_sum
      intro x _
      refine mul_le_mul_of_nonneg_left ?_ ((hE θ).1 x)
      by_cases hx : Good θ x
      · simpa [hx] using hgood θ x hx
      · simp only [hx, if_false]
        exact finiteTV_le_one_of_isDist _ _
          (hG x (Set.mem_univ x)) (hF θ)
    _ ≤ ∑ x, (E θ x * ε + if Good θ x then 0 else E θ x) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : Good θ x
      · simp [hx]
      · simp only [hx, if_false, mul_one]
        exact le_add_of_nonneg_left (mul_nonneg ((hE θ).1 x) hε)
    _ = ε + ∑ x, if Good θ x then 0 else E θ x := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, (hE θ).2, one_mul]
    _ ≤ ε + δ := by linarith [hbad θ]
    _ = δ + ε := by ring

/-- **Model-rollout decoder bound.** Every acquired signal chooses one valid estimated
Markov model.  Uniform initial error `ε₀` and uniform one-step error `ε` imply that
rolling out the chosen model for `n` steps is a valid world-independent decoder with
directed deficiency at most `ε₀ + n * ε`.

For causal native tests, use a padded-history state and put the target intervention's
action choice into the transition kernels.  Taking the maximum over the finite plan family
then gives the paper's `Γ_{≤n}` bound. -/
theorem finiteDeficiency_modelRollout_le
    [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (pHat : X → S → ℝ) (hPHat : ∀ x, IsDist (pHat x))
    (KHat : X → ℕ → S → S → ℝ)
    (hKHat : ∀ x t, KHat x t ∈ stochasticRules S S)
    (pTrue : Θ → S → ℝ)
    (KTrue : Θ → ℕ → S → S → ℝ)
    (hKTrue : ∀ θ t, KTrue θ t ∈ stochasticRules S S)
    {ε₀ ε : ℝ}
    (hinit : ∀ θ x, finiteTV (pHat x) (pTrue θ) ≤ ε₀)
    (hlocal : ∀ θ x t s, finiteTV (KHat x t s) (KTrue θ t s) ≤ ε)
    (n : ℕ) :
    finiteDeficiency E
      (fun θ => markovIterate (pTrue θ) (KTrue θ) n) ≤
        ε₀ + (n : ℝ) * ε := by
  let G : X → S → ℝ := fun x => markovIterate (pHat x) (KHat x) n
  have hG : G ∈ stochasticRules X S := by
    intro x _
    exact isDist_markovIterate (pHat x) (hPHat x) (KHat x) (hKHat x) n
  apply finiteDeficiency_le_of_decoder E
    (fun θ => markovIterate (pTrue θ) (KTrue θ) n)
    G hG (ε₀ + (n : ℝ) * ε)
  intro θ
  apply decodeErr_le_of_rowwise E hE
  intro x
  exact (finiteTV_markovIterate_le
    (pHat x) (pTrue θ) (hPHat x)
    (KHat x) (KTrue θ) (hKHat x) (hKTrue θ)
    (hlocal θ x) n).trans (by
      have hi := hinit θ x
      linarith)

/-- **High-probability predictive-simulator bound.**  The acquired signal need only
select a good model with high probability in each world.  If the bad-signal mass is at
most `δ`, while good signals have initial error at most `ε₀` and one-step error at most
`ε`, then the same world-independent rollout decoder has deficiency at most
`δ + ε₀ + n * ε`.

The explicit `IsDist` premise on the true initial laws is needed only to charge a bad
signal the universal TV bound one.  No estimator correctness is assumed on bad signals. -/
theorem finiteDeficiency_modelRollout_good_le
    [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (pHat : X → S → ℝ) (hPHat : ∀ x, IsDist (pHat x))
    (KHat : X → ℕ → S → S → ℝ)
    (hKHat : ∀ x t, KHat x t ∈ stochasticRules S S)
    (pTrue : Θ → S → ℝ) (hPTrue : ∀ θ, IsDist (pTrue θ))
    (KTrue : Θ → ℕ → S → S → ℝ)
    (hKTrue : ∀ θ t, KTrue θ t ∈ stochasticRules S S)
    (Good : Θ → X → Prop) [∀ θ x, Decidable (Good θ x)]
    {δ ε₀ ε : ℝ} (hε₀ : 0 ≤ ε₀) (hε : 0 ≤ ε)
    (hbad : ∀ θ, (∑ x, if Good θ x then (0 : ℝ) else E θ x) ≤ δ)
    (hinit : ∀ θ x, Good θ x → finiteTV (pHat x) (pTrue θ) ≤ ε₀)
    (hlocal : ∀ θ x, Good θ x → ∀ t s,
      finiteTV (KHat x t s) (KTrue θ t s) ≤ ε)
    (n : ℕ) :
    finiteDeficiency E
      (fun θ => markovIterate (pTrue θ) (KTrue θ) n) ≤
        δ + ε₀ + (n : ℝ) * ε := by
  classical
  let G : X → S → ℝ := fun x => markovIterate (pHat x) (KHat x) n
  have hG : G ∈ stochasticRules X S := by
    intro x _
    exact isDist_markovIterate (pHat x) (hPHat x) (KHat x) (hKHat x) n
  have hc : 0 ≤ ε₀ + (n : ℝ) * ε :=
    add_nonneg hε₀ (mul_nonneg (Nat.cast_nonneg n) hε)
  apply finiteDeficiency_le_of_decoder E
    (fun θ => markovIterate (pTrue θ) (KTrue θ) n)
    G hG (δ + ε₀ + (n : ℝ) * ε)
  intro θ
  calc
    decodeErr E (fun θ => markovIterate (pTrue θ) (KTrue θ) n) G θ ≤
        ∑ x, E θ x * finiteTV (G x)
          (markovIterate (pTrue θ) (KTrue θ) n) :=
      decodeErr_le_weighted_rowTV E hE _ G θ
    _ ≤ ∑ x, E θ x *
          (if Good θ x then ε₀ + (n : ℝ) * ε else 1) := by
      apply Finset.sum_le_sum
      intro x _
      refine mul_le_mul_of_nonneg_left ?_ ((hE θ).1 x)
      by_cases hx : Good θ x
      · simp only [hx, if_true]
        exact (finiteTV_markovIterate_le
          (pHat x) (pTrue θ) (hPHat x)
          (KHat x) (KTrue θ) (hKHat x) (hKTrue θ)
          (hlocal θ x hx) n).trans (by
            have hi := hinit θ x hx
            linarith)
      · simp only [hx, if_false]
        exact finiteTV_le_one_of_isDist _ _
          (isDist_markovIterate (pHat x) (hPHat x) (KHat x) (hKHat x) n)
          (isDist_markovIterate (pTrue θ) (hPTrue θ)
            (KTrue θ) (hKTrue θ) n)
    _ ≤ ∑ x, (E θ x * (ε₀ + (n : ℝ) * ε) +
          if Good θ x then 0 else E θ x) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : Good θ x
      · simp [hx]
      · simp only [hx, if_false, mul_one]
        exact le_add_of_nonneg_left (mul_nonneg ((hE θ).1 x) hc)
    _ = ε₀ + (n : ℝ) * ε +
          ∑ x, if Good θ x then 0 else E θ x := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, (hE θ).2, one_mul]
    _ ≤ ε₀ + (n : ℝ) * ε + δ := by
      linarith [hbad θ]
    _ = δ + ε₀ + (n : ℝ) * ε := by ring

end PredictiveTransport
end IdExp
