import Formal.FiniteBayesInformation
import Formal.DecoderRounding
import Formal.DeficiencyTriangle
import Formal.CausalBehaviorCapability

/-!
# Entropy-gap calibration when every world has positive prior mass

The entropy convention in this file is nats, as in `FiniteProbability`.
A posterior-sampling decoder (with a valid fallback on null signals) gives
an explicit uniform simulation bound. No optimizing-policy assumption is
needed; the entropy gap is conditional entropy of the acquired experiment.
-/

namespace IdExp

open Finset Set

variable {Θ X : Type*} [Fintype Θ] [Fintype X]

/-- Pointwise log inequality behind the posterior-sampling error bound. -/
theorem mul_one_sub_le_negMulLog {x : ℝ} (hx : 0 ≤ x) :
    x * (1 - x) ≤ Real.negMulLog x := by
  by_cases hz : x = 0
  · simp [hz]
  · have hl := Real.log_le_sub_one_of_pos (lt_of_le_of_ne hx (Ne.symm hz))
    rw [Real.negMulLog]
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hl)]

/-- Collision error is bounded by Shannon entropy, in nats. -/
theorem one_sub_collision_le_ent (p : Θ → ℝ) (hp : IsDist p) :
    1 - ∑ θ, p θ ^ 2 ≤ ent p := by
  have heq : 1 - ∑ θ, p θ ^ 2 = ∑ θ, p θ * (1 - p θ) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hp.2, pow_two]
  rw [heq]
  exact Finset.sum_le_sum fun θ _ => mul_one_sub_le_negMulLog (hp.1 θ)

/-- Posterior sampling with the prior used on null observations. -/
noncomputable def finitePosteriorSamplingRule (α : Θ → ℝ) (E : FiniteExperiment Θ X) :
    X → Θ → ℝ := fun x =>
  if finiteBayesMass α E x = 0 then α else finiteBayesPosterior α E x

theorem finitePosteriorSamplingRule_valid (α : Θ → ℝ) (hα : IsDist α)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) :
    finitePosteriorSamplingRule α E ∈ stochasticRules X Θ := by
  intro x _
  by_cases hx : finiteBayesMass α E x = 0
  · simpa [finitePosteriorSamplingRule, hx, stdSimplex, IsDist] using hα
  · simpa [finitePosteriorSamplingRule, hx] using
      finiteBayesPosterior_mem_simplex α E hα.1 (fun θ x => (hE θ).1 x) x hx

/-- Null observations contribute zero to the joint law, so the fallback
has no effect on any Bayes-risk identity. -/
theorem finitePosteriorSamplingRule_mass (α : Θ → ℝ) (hα : IsDist α)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) (x : X) (θ : Θ) :
    finiteBayesMass α E x * finitePosteriorSamplingRule α E x θ = α θ * E θ x := by
  have h := finiteBayesPosterior_mul_mass α E hα.1 (fun θ x => (hE θ).1 x) x θ
  change finiteBayesPosterior α E x θ * finiteBayesMass α E x = _ at h
  by_cases hx : finiteBayesMass α E x = 0
  ·
    simpa [finitePosteriorSamplingRule, hx] using h
  · simpa [finitePosteriorSamplingRule, hx, mul_comm] using h

/-- The prior-averaged decoder error is the expected posterior collision
error; its entropy upper bound includes boundary and null observations. -/
theorem finitePosteriorSamplingRule_bayes_error_le_entropy [DecidableEq Θ]
    (α : Θ → ℝ) (hα : IsDist α) (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) :
    (∑ θ, α θ * decodeErr E (finiteLabelExperiment Θ) (finitePosteriorSamplingRule α E) θ) ≤
      finiteBayesPotential ent α E := by
  let G := finitePosteriorSamplingRule α E
  have hG := finitePosteriorSamplingRule_valid α hα E hE
  have hsum :
      (∑ θ, α θ * decodeErr E (finiteLabelExperiment Θ) G θ) =
        ∑ x, finiteBayesMass α E x * (1 - ∑ θ, G x θ ^ 2) := by
    simp_rw [decodeErr_finiteLabel_eq_weighted_error E hE G hG, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    calc
      (∑ θ, α θ * (E θ x * (1 - G x θ))) =
          ∑ θ, finiteBayesMass α E x * (G x θ * (1 - G x θ)) := by
        apply Finset.sum_congr rfl
        intro θ _
        rw [← mul_assoc, ← finitePosteriorSamplingRule_mass α hα E hE x θ]
        ring
      _ = finiteBayesMass α E x * (1 - ∑ θ, G x θ ^ 2) := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, pow_two]
        rw [show (∑ θ, G x θ) = 1 from (hG x trivial).2]
  rw [hsum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : finiteBayesMass α E x = 0
  · simp [hx]
  · have hp := finiteBayesPosterior_mem_simplex α E hα.1 (fun θ x => (hE θ).1 x) x hx
    change finiteBayesMass α E x * (1 - ∑ θ, G x θ ^ 2) ≤
      finiteBayesMass α E x * ent (finiteBayesPosterior α E x)
    simp only [G, finitePosteriorSamplingRule, if_neg hx]
    exact mul_le_mul_of_nonneg_left
      (one_sub_collision_le_ent _ hp)
      (finiteBayesMass_nonneg α E hα.1 (fun θ x => (hE θ).1 x) x)

/-- A lower bound `a` on every atom of the prior upgrades averaged entropy
control to one common decoder's worst-world error bound. -/
theorem finitePosteriorSamplingRule_uniform_error [DecidableEq Θ]
    (α : Θ → ℝ) (hα : IsDist α) (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    {a : ℝ} (ha : 0 < a) (hmin : ∀ θ, a ≤ α θ) (θ : Θ) :
    decodeErr E (finiteLabelExperiment Θ) (finitePosteriorSamplingRule α E) θ ≤
      finiteBayesPotential ent α E / a := by
  have hnon (η : Θ) : 0 ≤ decodeErr E (finiteLabelExperiment Θ)
      (finitePosteriorSamplingRule α E) η := decodeErr_nonneg _ _ _ _
  have hsingle : α θ * decodeErr E (finiteLabelExperiment Θ) (finitePosteriorSamplingRule α E) θ ≤
      ∑ η, α η * decodeErr E (finiteLabelExperiment Θ) (finitePosteriorSamplingRule α E) η :=
    Finset.single_le_sum (fun η _ => mul_nonneg (hα.1 η) (hnon η)) (Finset.mem_univ θ)
  have htotal := finitePosteriorSamplingRule_bayes_error_le_entropy α hα E hE
  apply (le_div_iff₀ ha).2
  nlinarith [mul_nonneg (sub_nonneg.mpr (hmin θ)) (hnon θ)]

/-- Actual optimized full-label deficiency is bounded by conditional
entropy divided by the minimum prior mass. -/
theorem finiteLabelDeficiency_le_entropy_div_minPrior [Nonempty Θ] [DecidableEq Θ]
    (α : Θ → ℝ) (hα : IsDist α) (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    {a : ℝ} (ha : 0 < a) (hmin : ∀ θ, a ≤ α θ) :
    finiteDeficiency E (finiteLabelExperiment Θ) ≤ finiteBayesPotential ent α E / a := by
  exact finiteDeficiency_le_of_decoder E _ (finitePosteriorSamplingRule α E)
    (finitePosteriorSamplingRule_valid α hα E hE) _
    (finitePosteriorSamplingRule_uniform_error α hα E hE ha hmin)

/-- The same entropy bound controls simulation of every finite target,
not just recovery of the world label. -/
theorem finiteDeficiency_le_entropy_div_minPrior [Nonempty Θ] [DecidableEq Θ]
    {Y : Type*} [Fintype Y] [Nonempty Y]
    (α : Θ → ℝ) (hα : IsDist α) (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F)
    {a : ℝ} (ha : 0 < a) (hmin : ∀ θ, a ≤ α θ) :
    finiteDeficiency E F ≤ min 1 ((ent α - finiteBayesInformation α E) / a) := by
  have hblackwell : FiniteBlackwellLE F (finiteLabelExperiment Θ) := by
    refine ⟨F, fun θ _ => hF θ, ?_⟩
    funext θ y
    simp [finiteDecisionLaw, finiteLabelExperiment, diracExp]
  have hlabel : finiteDeficiency (finiteLabelExperiment Θ) F = 0 :=
    finiteDeficiency_eq_zero_of_finiteBlackwellLE _ _ hblackwell
  have htri := finiteDeficiency_triangle E (finiteLabelExperiment Θ) F hE
    (diracExp_valid id) hF
  rw [hlabel, add_zero] at htri
  apply le_min (finiteDeficiency_le_one_of_valid E F hE hF)
  have hh := finiteLabelDeficiency_le_entropy_div_minPrior α hα E hE ha hmin
  simpa [finiteBayesInformation] using htri.trans hh

/-- The literal native audit inherits the entropy calibration uniformly
over all native plans through the requested depth. -/
theorem causalBehaviorNativeAudit_le_entropy_div_minPrior [Nonempty Θ] [DecidableEq Θ]
    {A O : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
    (α : Θ → ℝ) (hα : IsDist α) (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (ps : Θ → CausalBehavior A O) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (hmin : ∀ θ, a ≤ α θ) :
    causalBehaviorNativeDeficiencyUpTo E ps n ≤
      min 1 ((ent α - finiteBayesInformation α E) / a) := by
  classical
  let σ : CausalObservationPlan A O 0 := Classical.arbitrary _
  have hne : (causalBehaviorNativeDeficiencyValuesUpTo E ps n).Nonempty :=
    ⟨_, 0, Nat.zero_le _, σ, rfl⟩
  apply csSup_le hne
  rintro d ⟨m, _, τ, rfl⟩
  exact finiteDeficiency_le_entropy_div_minPrior α hα E hE _
    (CausalObservationPlan.behaviorPlanExperiment_valid τ ps) ha hmin

/-- The bits convention gives the note's stated bound. The nats bound above
is slightly stronger because `log 2 ≤ 1`. -/
theorem causalBehaviorNativeAudit_le_informationGap_bits [Nonempty Θ] [DecidableEq Θ]
    {A O : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
    (α : Θ → ℝ) (hα : IsDist α) (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (ps : Θ → CausalBehavior A O) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (hmin : ∀ θ, a ≤ α θ) :
    causalBehaviorNativeDeficiencyUpTo E ps n ≤
      min 1 (((ent α - finiteBayesInformation α E) / Real.log 2) / a) := by
  have hH : 0 ≤ ent α - finiteBayesInformation α E := by
    have hbound := finitePosteriorSamplingRule_bayes_error_le_entropy α hα E hE
    have hnon : 0 ≤ ∑ θ, α θ * decodeErr E (finiteLabelExperiment Θ)
        (finitePosteriorSamplingRule α E) θ :=
      Finset.sum_nonneg fun θ _ => mul_nonneg (hα.1 θ) (decodeErr_nonneg _ _ _ _)
    simpa [finiteBayesInformation] using hnon.trans hbound
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hbits : ent α - finiteBayesInformation α E ≤
      (ent α - finiteBayesInformation α E) / Real.log 2 := by
    apply (le_div_iff₀ hlog).2
    exact mul_le_of_le_one_right hH hlogle
  exact (causalBehaviorNativeAudit_le_entropy_div_minPrior α hα E hE ps n ha hmin).trans
    (min_le_min le_rfl (div_le_div_of_nonneg_right hbits ha.le))

end IdExp
