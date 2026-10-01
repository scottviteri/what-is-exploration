import Formal.QuantitativeStrictness
import Formal.QuadraticPosterior

/-!
# The quadratic potential has a reverse bound

`posteriorQuadraticPotential p = ∑ θ, p θ ^ 2` is the potential of complete
expected squared-posterior movement, the second objective named in
`prop:finite-world-strict-finitary`.  This file checks its reverse bound with
constant `1 / (4 a)` for a prior with floor `a`: the Bayes reverse channel of
an exact garbling `F ↦ FG` has prior-weighted squared row-TV error at most
`(J(F) − J(FG)) / (4 a)`.

The argument is finite.  Writing `w(s,t) = m(s) G(s,t)` for the joint law of a
signal and its garbled symbol, `p_s` for the posterior of `F` and `q_t` for the
posterior of `FG`, the prior-weighted rows satisfy
`α_θ (F_θ(s) − (FG R)_θ(s)) = ∑_t w(s,t) (p_s(θ) − q_t(θ))`, so the weighted
row TV is at most half the `w`-expected absolute posterior movement; Jensen's
inequality bounds its square by the `w`-expected squared movement, whose sum
over worlds is exactly `J(F) − J(FG)` for the quadratic potential.

Consequently complete expected squared-posterior movement is strictly
finitarily monotone for every policy pair on a finite class with a
full-support prior, and its maximizers are exactly the natively sufficient
policies whenever one exists.
-/

namespace IdExp

open Finset

universe u v

section Finite

variable {Θ : Type v} [Fintype Θ] {S T : Type u} [Fintype S] [Fintype T]

omit [Fintype S] in
theorem finiteBayesPosterior_eq_div (α : Θ → ℝ) (E : Θ → S → ℝ) (s : S) (θ : Θ) :
    finiteBayesPosterior α E s θ = α θ * E θ s / finiteBayesMass α E s := rfl

omit [Fintype S] in
theorem finiteBayesMass_mul_posterior (α : Θ → ℝ) (hα : ∀ θ, 0 ≤ α θ) (E : Θ → S → ℝ)
    (hE : ∀ θ s, 0 ≤ E θ s) (s : S) (θ : Θ) :
    finiteBayesMass α E s * finiteBayesPosterior α E s θ = α θ * E θ s := by
  rw [mul_comm]
  exact finiteBayesPosterior_mul_mass α E hα hE s θ

/-- The prior-weighted joint law of a signal and its garbled symbol. -/
def garbleJoint (α : Θ → ℝ) (F : FiniteExperiment Θ S) (G : S → T → ℝ) (s : S) (t : T) : ℝ :=
  finiteBayesMass α F s * G s t

theorem garbleJoint_nonneg (α : Θ → ℝ) (hα : ∀ θ, 0 ≤ α θ) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (s : S) (t : T) :
    0 ≤ garbleJoint α F G s t :=
  mul_nonneg (finiteBayesMass_nonneg α F hα (fun θ s => (hF θ).1 s) s) ((hG s (Set.mem_univ s)).1 t)

omit [Fintype S] in
theorem sum_garbleJoint_right (α : Θ → ℝ) (F : FiniteExperiment Θ S) (G : S → T → ℝ)
    (hG : G ∈ stochasticRules S T) (s : S) :
    ∑ t, garbleJoint α F G s t = finiteBayesMass α F s := by
  unfold garbleJoint
  rw [← Finset.mul_sum, (hG s (Set.mem_univ s)).2, mul_one]

theorem sum_garbleJoint_left (α : Θ → ℝ) (F : FiniteExperiment Θ S) (G : S → T → ℝ) (t : T) :
    ∑ s, garbleJoint α F G s t = finiteBayesMass α (finiteDecisionLaw F G) t := by
  rw [finiteBayesMass_decisionLaw]
  rfl

theorem sum_garbleJoint (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) :
    ∑ s, ∑ t, garbleJoint α F G s t = 1 := by
  simp_rw [sum_garbleJoint_right α F G hG]
  exact (finiteBayesMass_isDist α hα F hF).2

/-- The prior-weighted forward row, as a `w`-average of the signal posterior. -/
theorem forward_row_eq (α : Θ → ℝ) (hα : ∀ θ, 0 ≤ α θ) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (θ : Θ) (s : S) :
    α θ * F θ s = ∑ t, garbleJoint α F G s t * finiteBayesPosterior α F s θ := by
  have h1 : ∑ t, garbleJoint α F G s t * finiteBayesPosterior α F s θ =
      (finiteBayesMass α F s * finiteBayesPosterior α F s θ) * ∑ t, G s t := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold garbleJoint
    ring
  rw [h1, (hG s (Set.mem_univ s)).2, mul_one,
    finiteBayesMass_mul_posterior α hα F (fun θ s => (hF θ).1 s) s θ]

/-- The prior-weighted reverse row, as a `w`-average of the garbled posterior. -/
theorem reverse_row_eq [Nonempty S] (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (θ : Θ) (s : S) :
    α θ * finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ s =
      ∑ t, garbleJoint α F G s t * finiteBayesPosterior α (finiteDecisionLaw F G) t θ := by
  have hFG : IsFiniteExperiment (finiteDecisionLaw F G) := finiteDecisionLaw_valid F hF G hG
  show α θ * ∑ t, finiteDecisionLaw F G θ t * bayesReverseChannel α F G t s = _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [bayesReverseChannel]
  split_ifs with h0
  · have hz : α θ * finiteDecisionLaw F G θ t = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun c _ => mul_nonneg (hα.1 c) ((hFG c).1 t)).1 h0 θ
        (Finset.mem_univ θ)
    rw [finiteBayesPosterior_eq_div, hz, zero_div, mul_zero, ← mul_assoc, hz, zero_mul]
  · rw [finiteBayesPosterior_eq_div]
    unfold garbleJoint
    field_simp

theorem weighted_row_diff_eq [Nonempty S] (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (θ : Θ) (s : S) :
    α θ * (F θ s - finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ s) =
      ∑ t, garbleJoint α F G s t *
        (finiteBayesPosterior α F s θ - finiteBayesPosterior α (finiteDecisionLaw F G) t θ) := by
  rw [mul_sub, forward_row_eq α hα.1 F hF G hG θ s, reverse_row_eq α hα F hF G hG θ s,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- The weighted row TV of the Bayes reverse channel is at most half the
`w`-expected absolute posterior movement. -/
theorem weighted_tv_le_movement [Nonempty S] (α : Θ → ℝ) (hα : IsDist α)
    (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F) (G : S → T → ℝ)
    (hG : G ∈ stochasticRules S T) (θ : Θ) :
    α θ * finiteTV (F θ) (finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ) ≤
      (1 / 2) * ∑ s, ∑ t, garbleJoint α F G s t *
        |finiteBayesPosterior α F s θ - finiteBayesPosterior α (finiteDecisionLaw F G) t θ| := by
  unfold finiteTV
  rw [← mul_assoc, mul_comm (α θ) (1 / 2), mul_assoc, Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => ?_) (by norm_num)
  calc α θ * |F θ s - finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ s|
      = |α θ * (F θ s - finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ s)| := by
        rw [abs_mul, abs_of_nonneg (hα.1 θ)]
    _ = |∑ t, garbleJoint α F G s t *
          (finiteBayesPosterior α F s θ - finiteBayesPosterior α (finiteDecisionLaw F G) t θ)| := by
        rw [weighted_row_diff_eq α hα F hF G hG θ s]
    _ ≤ ∑ t, |garbleJoint α F G s t *
          (finiteBayesPosterior α F s θ - finiteBayesPosterior α (finiteDecisionLaw F G) t θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t, garbleJoint α F G s t *
          |finiteBayesPosterior α F s θ - finiteBayesPosterior α (finiteDecisionLaw F G) t θ| := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [abs_mul, abs_of_nonneg (garbleJoint_nonneg α hα.1 F hF G hG s t)]

/-- Jensen: the square of a weighted absolute average is at most the weighted
average of squares. -/
theorem sq_weighted_abs_le (w : S → T → ℝ) (hw : ∀ s t, 0 ≤ w s t)
    (h1 : ∑ s, ∑ t, w s t = 1) (d : S → T → ℝ) :
    (∑ s, ∑ t, w s t * |d s t|) ^ 2 ≤ ∑ s, ∑ t, w s t * d s t ^ 2 := by
  have hJ := (convexOn_pow 2 : ConvexOn ℝ (Set.Ici 0) fun x : ℝ => x ^ 2).map_sum_le
    (t := (Finset.univ : Finset (S × T))) (w := fun x => w x.1 x.2) (p := fun x => |d x.1 x.2|)
    (fun x _ => hw x.1 x.2) (by rw [Fintype.sum_prod_type]; exact h1)
    (fun x _ => Set.mem_Ici.2 (abs_nonneg _))
  simp only [smul_eq_mul, Fintype.sum_prod_type, sq_abs] at hJ
  exact hJ

/-- Per world: the weighted squared row TV is at most the `w`-expected
squared posterior movement over `4 a`. -/
theorem weighted_sq_tv_le_movement [Nonempty S] (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a)
    (hlow : ∀ θ, a ≤ α θ) (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (θ : Θ) :
    α θ * (finiteTV (F θ)
        (finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ)) ^ 2 ≤
      (1 / (4 * a)) * ∑ s, ∑ t, garbleJoint α F G s t *
        (finiteBayesPosterior α F s θ - finiteBayesPosterior α (finiteDecisionLaw F G) t θ) ^ 2 := by
  set TV := finiteTV (F θ)
    (finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ) with hTV
  set X := ∑ s, ∑ t, garbleJoint α F G s t *
    |finiteBayesPosterior α F s θ - finiteBayesPosterior α (finiteDecisionLaw F G) t θ| with hX
  set Y := ∑ s, ∑ t, garbleJoint α F G s t *
    (finiteBayesPosterior α F s θ - finiteBayesPosterior α (finiteDecisionLaw F G) t θ) ^ 2 with hY
  have hTV0 : 0 ≤ TV := finiteTV_nonneg _ _
  have hαθ : 0 < α θ := ha.trans_le (hlow θ)
  have h1 : α θ * TV ≤ (1 / 2) * X := weighted_tv_le_movement α hα F hF G hG θ
  have hJ : X ^ 2 ≤ Y :=
    sq_weighted_abs_le (garbleJoint α F G) (garbleJoint_nonneg α hα.1 F hF G hG)
      (sum_garbleJoint α hα F hF G hG) _
  have hY0 : 0 ≤ Y := (sq_nonneg X).trans hJ
  have h2 : (α θ * TV) ^ 2 ≤ ((1 / 2) * X) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hαθ.le hTV0) h1 2
  have h3 : α θ * TV ^ 2 = (α θ * TV) ^ 2 / α θ := by
    field_simp
  rw [h3]
  calc (α θ * TV) ^ 2 / α θ ≤ ((1 / 2) * X) ^ 2 / α θ := div_le_div_of_nonneg_right h2 hαθ.le
    _ ≤ (1 / 4 * Y) / α θ := by
        apply div_le_div_of_nonneg_right _ hαθ.le
        nlinarith [hJ]
    _ ≤ (1 / 4 * Y) / a := div_le_div_of_nonneg_left (by positivity) ha (hlow θ)
    _ = (1 / (4 * a)) * Y := by
        field_simp

/-! ## The squared-movement identity -/

theorem sum_garbleJoint_sq_left (α : Θ → ℝ) (F : FiniteExperiment Θ S) (G : S → T → ℝ)
    (hG : G ∈ stochasticRules S T) :
    ∑ s, ∑ t, garbleJoint α F G s t * ∑ θ, finiteBayesPosterior α F s θ ^ 2 =
      finiteBayesPotential posteriorQuadraticPotential α F := by
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_mul, sum_garbleJoint_right α F G hG s]
  rfl

theorem sum_garbleJoint_sq_right (α : Θ → ℝ) (F : FiniteExperiment Θ S) (G : S → T → ℝ) :
    ∑ s, ∑ t, garbleJoint α F G s t * ∑ θ, finiteBayesPosterior α (finiteDecisionLaw F G) t θ ^ 2 =
      finiteBayesPotential posteriorQuadraticPotential α (finiteDecisionLaw F G) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_mul, sum_garbleJoint_left α F G t]
  rfl

theorem sum_garbleJoint_cross (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) :
    ∑ s, ∑ t, garbleJoint α F G s t *
        ∑ θ, finiteBayesPosterior α F s θ * finiteBayesPosterior α (finiteDecisionLaw F G) t θ =
      finiteBayesPotential posteriorQuadraticPotential α (finiteDecisionLaw F G) := by
  have hFG : IsFiniteExperiment (finiteDecisionLaw F G) := finiteDecisionLaw_valid F hF G hG
  have hinner : ∀ t θ, ∑ s, garbleJoint α F G s t * finiteBayesPosterior α F s θ =
      finiteBayesMass α (finiteDecisionLaw F G) t *
        finiteBayesPosterior α (finiteDecisionLaw F G) t θ := by
    intro t θ
    rw [finiteBayesMass_mul_posterior α hα.1 (finiteDecisionLaw F G) (fun θ t => (hFG θ).1 t) t θ]
    show _ = α θ * ∑ s, F θ s * G s t
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold garbleJoint
    rw [mul_comm (finiteBayesMass α F s) (G s t), mul_assoc,
      finiteBayesMass_mul_posterior α hα.1 F (fun θ s => (hF θ).1 s) s θ]
    ring
  calc ∑ s, ∑ t, garbleJoint α F G s t *
        ∑ θ, finiteBayesPosterior α F s θ * finiteBayesPosterior α (finiteDecisionLaw F G) t θ
      = ∑ t, ∑ θ, finiteBayesPosterior α (finiteDecisionLaw F G) t θ *
          ∑ s, garbleJoint α F G s t * finiteBayesPosterior α F s θ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun θ _ => Finset.sum_congr rfl fun s _ => ?_
        ring
    _ = ∑ t, finiteBayesMass α (finiteDecisionLaw F G) t *
          ∑ θ, finiteBayesPosterior α (finiteDecisionLaw F G) t θ ^ 2 := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun θ _ => ?_
        rw [hinner t θ]
        ring
    _ = finiteBayesPotential posteriorQuadraticPotential α (finiteDecisionLaw F G) := rfl

/-- **Expected squared posterior movement is the quadratic potential lost by
the garbling.** -/
theorem sum_garbleJoint_sq_dist (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) :
    ∑ s, ∑ t, garbleJoint α F G s t *
        ∑ θ, (finiteBayesPosterior α F s θ - finiteBayesPosterior α (finiteDecisionLaw F G) t θ) ^ 2 =
      finiteBayesPotential posteriorQuadraticPotential α F -
        finiteBayesPotential posteriorQuadraticPotential α (finiteDecisionLaw F G) := by
  have hexp : ∀ s t, ∑ θ, (finiteBayesPosterior α F s θ -
      finiteBayesPosterior α (finiteDecisionLaw F G) t θ) ^ 2 =
      ∑ θ, finiteBayesPosterior α F s θ ^ 2 -
        2 * ∑ θ, finiteBayesPosterior α F s θ * finiteBayesPosterior α (finiteDecisionLaw F G) t θ +
        ∑ θ, finiteBayesPosterior α (finiteDecisionLaw F G) t θ ^ 2 := by
    intro s t
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    ring
  have hsplit : ∀ s t, garbleJoint α F G s t * ∑ θ, (finiteBayesPosterior α F s θ -
      finiteBayesPosterior α (finiteDecisionLaw F G) t θ) ^ 2 =
      garbleJoint α F G s t * ∑ θ, finiteBayesPosterior α F s θ ^ 2 -
        2 * (garbleJoint α F G s t * ∑ θ, finiteBayesPosterior α F s θ *
          finiteBayesPosterior α (finiteDecisionLaw F G) t θ) +
        garbleJoint α F G s t * ∑ θ, finiteBayesPosterior α (finiteDecisionLaw F G) t θ ^ 2 := by
    intro s t
    rw [hexp s t]
    ring
  simp_rw [hsplit]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_garbleJoint_sq_left α F G hG, sum_garbleJoint_sq_right α F G,
    sum_garbleJoint_cross α hα F hF G hG]
  ring

/-- **The quadratic potential has reverse constant `1 / (4 a)`** for a prior
with floor `a`. -/
theorem quadratic_hasReverseBound (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a)
    (hlow : ∀ θ, a ≤ α θ) :
    HasReverseBound.{u, v} posteriorQuadraticPotential α (1 / (4 * a)) := by
  intro S T _ _ _ F hF G hG
  refine ⟨bayesReverseChannel α F G, bayesReverseChannel_stochastic α hα F hF G hG, ?_⟩
  calc ∑ θ, α θ * (finiteTV (F θ)
        (finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ)) ^ 2
      ≤ ∑ θ, (1 / (4 * a)) * ∑ s, ∑ t, garbleJoint α F G s t *
          (finiteBayesPosterior α F s θ - finiteBayesPosterior α (finiteDecisionLaw F G) t θ) ^ 2 :=
        Finset.sum_le_sum fun θ _ => weighted_sq_tv_le_movement α hα a ha hlow F hF G hG θ
    _ = (1 / (4 * a)) * ∑ s, ∑ t, garbleJoint α F G s t * ∑ θ,
          (finiteBayesPosterior α F s θ - finiteBayesPosterior α (finiteDecisionLaw F G) t θ) ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.mul_sum]
    _ = (1 / (4 * a)) * (finiteBayesPotential posteriorQuadraticPotential α F -
          finiteBayesPotential posteriorQuadraticPotential α (finiteDecisionLaw F G)) := by
        rw [sum_garbleJoint_sq_dist α hα F hF G hG]

end Finite

/-! ## Complete expected squared-posterior movement -/

section Causal

set_option linter.unusedSectionVars false

variable {A O Θ : Type u} [Fintype A] [Fintype O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]
  [Nonempty A] [Nonempty O] [Fintype Θ] [Nonempty Θ]
  [DecidableEq Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

variable (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))

/-- **Complete expected squared-posterior movement is strictly finitarily
monotone** on a finite class with a full-support prior. -/
theorem causalQuadraticObjective_lt_of_strict_finitaryDominates (α : Θ → ℝ) (hα : IsDist α)
    (hfs : FullSupport α) {π σ : ValidCausalPolicy A O}
    (hdom : CausalFinitaryDominates Qs π σ) (hnot : ¬ CausalFinitaryDominates Qs σ π) :
    causalPotentialObjective posteriorQuadraticPotential α Qs hQ σ <
      causalPotentialObjective posteriorQuadraticPotential α Qs hQ π := by
  obtain ⟨a, ha, hlow⟩ := exists_prior_floor α hfs
  exact causalPotentialObjective_lt_of_reverseBound Qs hQ posteriorQuadraticPotential
    continuous_posteriorQuadraticPotential.continuousOn convexOn_posteriorQuadraticPotential
    α hα a ha hlow (1 / (4 * a)) (by positivity) (quadratic_hasReverseBound α hα a ha hlow) hdom hnot

/-- A policy with the complete squared-posterior movement of a natively
sufficient policy is natively sufficient. -/
theorem causalNativelySufficient_of_quadratic_eq (α : Θ → ℝ) (hα : IsDist α)
    (hfs : FullSupport α) {π σ : ValidCausalPolicy A O} (hπns : CausalNativelySufficient Qs π)
    (heq : causalPotentialObjective posteriorQuadraticPotential α Qs hQ σ =
      causalPotentialObjective posteriorQuadraticPotential α Qs hQ π) :
    CausalNativelySufficient Qs σ := by
  obtain ⟨a, ha, hlow⟩ := exists_prior_floor α hfs
  exact causalNativelySufficient_of_reverseBound_objective_eq Qs hQ posteriorQuadraticPotential
    continuous_posteriorQuadraticPotential.continuousOn convexOn_posteriorQuadraticPotential
    α hα a ha hlow (1 / (4 * a)) (by positivity) (quadratic_hasReverseBound α hα a ha hlow) hπns heq

/-- **Squared-movement maximizers are exactly the natively sufficient
policies** whenever one natively sufficient policy exists. -/
theorem causalQuadraticObjective_maximizer_iff_nativelySufficient (α : Θ → ℝ)
    (hα : IsDist α) (hfs : FullSupport α) {π : ValidCausalPolicy A O}
    (hπns : CausalNativelySufficient Qs π) (σ : ValidCausalPolicy A O) :
    (∀ ρ : ValidCausalPolicy A O,
        causalPotentialObjective posteriorQuadraticPotential α Qs hQ ρ ≤
          causalPotentialObjective posteriorQuadraticPotential α Qs hQ σ) ↔
      CausalNativelySufficient Qs σ := by
  obtain ⟨a, ha, hlow⟩ := exists_prior_floor α hfs
  exact causalPotentialObjective_maximizer_iff_nativelySufficient_of_reverseBound Qs hQ
    posteriorQuadraticPotential continuous_posteriorQuadraticPotential.continuousOn
    convexOn_posteriorQuadraticPotential α hα a ha hlow (1 / (4 * a)) (by positivity)
    (quadratic_hasReverseBound α hα a ha hlow) hπns σ

/-- **Both objectives named in the proposition are strictly finitarily
monotone**: complete information gain and complete expected squared-posterior
movement, for every policy pair, on a finite class with a full-support prior. -/
theorem namedObjectives_strictlyFinitaryMonotone (α : Θ → ℝ) (hα : IsDist α)
    (hfs : FullSupport α) {π σ : ValidCausalPolicy A O}
    (hdom : CausalFinitaryDominates Qs π σ) (hnot : ¬ CausalFinitaryDominates Qs σ π) :
    causalInformationObjective α Qs hQ σ < causalInformationObjective α Qs hQ π ∧
      causalPotentialObjective posteriorQuadraticPotential α Qs hQ σ <
        causalPotentialObjective posteriorQuadraticPotential α Qs hQ π :=
  ⟨causalInformationObjective_lt_of_strict_finitaryDominates Qs hQ α hα hfs hdom hnot,
    causalQuadraticObjective_lt_of_strict_finitaryDominates Qs hQ α hα hfs hdom hnot⟩

end Causal

end IdExp
