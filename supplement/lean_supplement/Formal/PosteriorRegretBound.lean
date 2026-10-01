import Formal.QuantitativeStrictness
import Formal.StrictFinitaryObjective

/-!
# Complete posterior regret bounds eventual experimental loss

A finite reverse bound is passed through two finite-prefix limits. First the
comparator's horizon tends to infinity while the acquired prefix is fixed;
then the acquired prefix grows. This preserves the reverse-bound constant
exactly and never replaces a policy-dependent convergence time by a common
acquisition deadline.

The reusable inequality compares any finitarily ordered pair and any finite
experiment. Native sufficiency makes the comparator's residual target loss
zero, giving the main-paper calibration rate.
-/

namespace IdExp

open Finset Set Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

/-- A nonnegative vanishing modulus sends every nonnegative sequence tending
to zero to another sequence tending to zero. No continuity away from zero is
required. -/
theorem tendsto_zero_of_vanishingModulus {ω : ℝ → ℝ}
    (hω : VanishingModulus ω) (hω0 : ∀ r, 0 ≤ r → 0 ≤ ω r)
    {r : ℕ → ℝ} (hr0 : ∀ k, 0 ≤ r k) (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k => ω (r k)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall fun k => hb.trans_le (hω0 _ (hr0 k))
  · intro ε hε
    obtain ⟨η, hη, hbound⟩ := hω (ε/2) (half_pos hε)
    filter_upwards [(tendsto_order.1 hr).2 η hη] with k hk
    exact (hbound _ (hr0 k) hk).trans_lt (half_lt_self hε)

universe u

variable {A O Θ : Type u} [Fintype A] [Fintype O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]
  [Nonempty A] [Nonempty O] [Fintype Θ] [Nonempty Θ]
  [DecidableEq Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

variable (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))

include hQ

/-- Finitary dominance as convergence to each fixed actual target prefix. -/
theorem tendsto_prefixDeficiency_zero_of_finitaryDominates
    {σ π : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs σ π) (k : ℕ) :
    Tendsto (fun m => finiteDeficiency (causalFiniteExperiment σ.1 Qs m)
      (causalFiniteExperiment π.1 Qs k)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall fun m => hb.trans_le
      (finiteDeficiency_nonneg_of_valid _ _ (causalFiniteExperiment_valid σ.1 σ.2 Qs hQ m)
        (causalFiniteExperiment_valid π.1 π.2 Qs hQ k))
  · intro ε hε
    exact eventually_atTop.2 (hdom k ε hε)

/-- Fixed acquired prefix, arbitrarily long comparator records. This first
limit removes the forward simulation error and its alphabet-dependent modulus
without changing the reverse-bound constant. -/
theorem eventualLoss_le_sqrt_terminal_sub_prefix_add
    {Y : Type u} [Fintype Y] [Nonempty Y]
    (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (c : ℝ) (hc : 0 ≤ c) (hrev : HasReverseBound.{u,u} Φ α c)
    (π σ : ValidCausalPolicy A O) (hdom : CausalFinitaryDominates Qs σ π)
    (T : FiniteExperiment Θ Y) (hT : IsFiniteExperiment T) (k : ℕ) :
    eventualLoss Qs π T ≤
      Real.sqrt (c * (causalTerminalPotential Φ α Qs hQ σ -
        finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs k)) / a) +
      eventualLoss Qs σ T := by
  let r := fun m => finiteDeficiency (causalFiniteExperiment σ.1 Qs m)
    (causalFiniteExperiment π.1 Qs k)
  let ω := potentialModulus Φ α (CausalFiniteTrace A O k)
  have hπk := causalFiniteExperiment_valid π.1 π.2 Qs hQ k
  have hr0 : ∀ m, 0 ≤ r m := fun m => finiteDeficiency_nonneg_of_valid _ _
    (causalFiniteExperiment_valid σ.1 σ.2 Qs hQ m) hπk
  have hr : Tendsto r atTop (𝓝 0) :=
    tendsto_prefixDeficiency_zero_of_finitaryDominates Qs hQ hdom k
  have hω : Tendsto (fun m => ω (r m)) atTop (𝓝 0) :=
    tendsto_zero_of_vanishingModulus (potentialModulus_vanishing Φ hΦc α hα)
      (fun d _ => potentialModulus_nonneg Φ hΦc α hα d) hr0 hr
  have hrad : Tendsto (fun m => c * (causalTerminalPotential Φ α Qs hQ σ -
      finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs k) + ω (r m)) / a)
      atTop (𝓝 (c * (causalTerminalPotential Φ α Qs hQ σ -
        finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs k)) / a)) := by
    simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.add hω)).div_const a
  have hlim := (hr.add (Real.continuous_sqrt.continuousAt.tendsto.comp hrad)).add
    (tendsto_eventualLoss Qs hQ σ T hT)
  simp only [zero_add] at hlim
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro m
  have hσm := causalFiniteExperiment_valid σ.1 σ.2 Qs hQ m
  have hstep := finiteDeficiency_le_of_potential_gap Φ hΦc α hα a ha hlow c hc hrev
    _ hπk _ hσm
  have hupper := prefixPotential_le_causalTerminalPotential Qs hQ Φ hΦc hΦ α hα σ m
  have hroot :
      Real.sqrt (c * (finiteBayesPotential Φ α (causalFiniteExperiment σ.1 Qs m) -
          finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs k) + ω (r m)) / a) ≤
        Real.sqrt (c * (causalTerminalPotential Φ α Qs hQ σ -
          finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs k) + ω (r m)) / a) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ ha.le
    apply mul_le_mul_of_nonneg_left _ hc
    linarith
  have htri := finiteDeficiency_triangle (causalFiniteExperiment π.1 Qs k)
    (causalFiniteExperiment σ.1 Qs m) T hπk hσm hT
  have hloss := eventualLoss_le Qs hQ π T hT k
  change finiteDeficiency (causalFiniteExperiment π.1 Qs k)
    (causalFiniteExperiment σ.1 Qs m) ≤ r m + _ at hstep
  exact hloss.trans (htri.trans
    (add_le_add (hstep.trans (add_le_add (le_refl (r m)) hroot)) le_rfl))

/-- **Quantitative finitary comparison.** A complete posterior gap bounds the
increase in eventual deficiency to every fixed finite experiment. The
comparator may itself retain nonzero residual target loss. -/
theorem eventualLoss_le_sqrt_potential_gap_add
    {Y : Type u} [Fintype Y] [Nonempty Y]
    (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (c : ℝ) (hc : 0 ≤ c) (hrev : HasReverseBound.{u,u} Φ α c)
    (π σ : ValidCausalPolicy A O) (hdom : CausalFinitaryDominates Qs σ π)
    (T : FiniteExperiment Θ Y) (hT : IsFiniteExperiment T) :
    eventualLoss Qs π T ≤
      Real.sqrt (c * (causalPotentialObjective Φ α Qs hQ σ -
        causalPotentialObjective Φ α Qs hQ π) / a) + eventualLoss Qs σ T := by
  have hpot : Tendsto
      (fun k => finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs k))
      atTop (𝓝 (causalTerminalPotential Φ α Qs hQ π)) :=
    tendsto_causalBayesPotential α hα Qs hQ π Φ hΦc
  have hrad : Tendsto (fun k => c * (causalTerminalPotential Φ α Qs hQ σ -
      finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs k)) / a)
      atTop (𝓝 (c * (causalTerminalPotential Φ α Qs hQ σ -
        causalTerminalPotential Φ α Qs hQ π) / a)) :=
    (tendsto_const_nhds.mul (tendsto_const_nhds.sub hpot)).div_const a
  have hlim := (Real.continuous_sqrt.continuousAt.tendsto.comp hrad).add_const
    (eventualLoss Qs σ T)
  have hbound := ge_of_tendsto hlim (Eventually.of_forall fun k =>
    eventualLoss_le_sqrt_terminal_sub_prefix_add Qs hQ Φ hΦc hΦ α hα a ha hlow
      c hc hrev π σ hdom T hT k)
  simpa only [causalPotentialObjective, sub_sub_sub_cancel_right] using hbound

/-- A zero-residual comparator gives the exact square-root regret bound. -/
theorem eventualLoss_le_sqrt_potential_gap
    {Y : Type u} [Fintype Y] [Nonempty Y]
    (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (c : ℝ) (hc : 0 ≤ c) (hrev : HasReverseBound.{u,u} Φ α c)
    (π σ : ValidCausalPolicy A O) (hdom : CausalFinitaryDominates Qs σ π)
    (T : FiniteExperiment Θ Y) (hT : IsFiniteExperiment T)
    (hzero : eventualLoss Qs σ T = 0) :
    eventualLoss Qs π T ≤
      Real.sqrt (c * (causalPotentialObjective Φ α Qs hQ σ -
        causalPotentialObjective Φ α Qs hQ π) / a) := by
  simpa only [hzero, add_zero] using eventualLoss_le_sqrt_potential_gap_add Qs hQ
    Φ hΦc hΦ α hα a ha hlow c hc hrev π σ hdom T hT

/-- A sufficient policy has zero eventual loss to every randomized native
record, including the empty record at horizon zero. -/
theorem eventualLoss_nativeRecord_eq_zero_of_sufficient
    (σ : ValidCausalPolicy A O) (hσ : CausalNativelySufficient Qs σ)
    (ρ : ValidCausalPolicy A O) (n : ℕ) :
    eventualLoss Qs σ (causalFiniteExperiment ρ.1 Qs n) = 0 := by
  exact tendsto_nhds_unique
    (tendsto_eventualLoss Qs hQ σ _ (causalFiniteExperiment_valid ρ.1 ρ.2 Qs hQ n))
    (tendsto_prefixDeficiency_zero_of_finitaryDominates Qs hQ
      ((causalNativelySufficient_iff_finitarilyGreatest Qs hQ σ).1 hσ ρ) n)

/-- The same zero loss for the observation-only deterministic native target. -/
theorem eventualLoss_nativePlan_eq_zero_of_sufficient
    (σ : ValidCausalPolicy A O) (hσ : CausalNativelySufficient Qs σ)
    (n : ℕ) (τ : CausalPlan A O n) :
    eventualLoss Qs σ (causalPlanObservationExperiment n τ Qs) = 0 := by
  have heq : eventualLoss Qs σ (causalPlanObservationExperiment n τ Qs) =
      eventualLoss Qs σ (causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n) := by
    unfold eventualLoss
    congr 1
    funext t
    exact finiteDeficiency_causalPlanObservation_eq_full _
      (causalFiniteExperiment_valid σ.1 σ.2 Qs hQ t) Qs hQ n τ
  rw [heq]
  exact eventualLoss_nativeRecord_eq_zero_of_sufficient Qs hQ σ hσ
    ⟨causalPolicyOfPlan n τ, isCausalPolicy_causalPolicyOfPlan n τ⟩ n

/-- **Native posterior-regret bound.** A sufficient comparator gives the
square-root guarantee for every randomized native record. The constant is
`c/a`, with neither a margin-halving loss nor an acquisition deadline. -/
theorem eventualLoss_nativeRecord_le_sqrt_potential_gap
    (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (c : ℝ) (hc : 0 ≤ c) (hrev : HasReverseBound.{u,u} Φ α c)
    (π σ : ValidCausalPolicy A O) (hσ : CausalNativelySufficient Qs σ)
    (ρ : ValidCausalPolicy A O) (n : ℕ) :
    eventualLoss Qs π (causalFiniteExperiment ρ.1 Qs n) ≤
      Real.sqrt (c * (causalPotentialObjective Φ α Qs hQ σ -
        causalPotentialObjective Φ α Qs hQ π) / a) :=
  eventualLoss_le_sqrt_potential_gap Qs hQ Φ hΦc hΦ α hα a ha hlow c hc hrev π σ
    ((causalNativelySufficient_iff_finitarilyGreatest Qs hQ σ).1 hσ π)
    _ (causalFiniteExperiment_valid ρ.1 ρ.2 Qs hQ n)
    (eventualLoss_nativeRecord_eq_zero_of_sufficient Qs hQ σ hσ ρ n)

/-- Unit total variation caps the quantitative guarantee at one. -/
theorem eventualLoss_nativeRecord_le_min_sqrt_potential_gap
    (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (c : ℝ) (hc : 0 ≤ c) (hrev : HasReverseBound.{u,u} Φ α c)
    (π σ : ValidCausalPolicy A O) (hσ : CausalNativelySufficient Qs σ)
    (ρ : ValidCausalPolicy A O) (n : ℕ) :
    eventualLoss Qs π (causalFiniteExperiment ρ.1 Qs n) ≤
      min 1 (Real.sqrt (c * (causalPotentialObjective Φ α Qs hQ σ -
        causalPotentialObjective Φ α Qs hQ π) / a)) :=
  le_min (eventualLoss_le_one Qs hQ π _ (causalFiniteExperiment_valid ρ.1 ρ.2 Qs hQ n))
    (eventualLoss_nativeRecord_le_sqrt_potential_gap Qs hQ Φ hΦc hΦ α hα a ha hlow
      c hc hrev π σ hσ ρ n)

/-- The bound also applies directly to observation-only native plans. -/
theorem eventualLoss_nativePlan_le_min_sqrt_potential_gap
    (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (c : ℝ) (hc : 0 ≤ c) (hrev : HasReverseBound.{u,u} Φ α c)
    (π σ : ValidCausalPolicy A O) (hσ : CausalNativelySufficient Qs σ)
    (n : ℕ) (τ : CausalPlan A O n) :
    eventualLoss Qs π (causalPlanObservationExperiment n τ Qs) ≤
      min 1 (Real.sqrt (c * (causalPotentialObjective Φ α Qs hQ σ -
        causalPotentialObjective Φ α Qs hQ π) / a)) := by
  have hT := causalPlanObservationExperiment_valid n τ Qs hQ
  exact le_min (eventualLoss_le_one Qs hQ π _ hT)
    (eventualLoss_le_sqrt_potential_gap Qs hQ Φ hΦc hΦ α hα a ha hlow c hc hrev π σ
      ((causalNativelySufficient_iff_finitarilyGreatest Qs hQ σ).1 hσ π) _ hT
      (eventualLoss_nativePlan_eq_zero_of_sufficient Qs hQ σ hσ n τ))

end
end IdExp
