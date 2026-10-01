import Formal.CountableBrierGarbling
import Mathlib.Algebra.Order.Chebyshev

/-! Finite prior heads give a reverse modulus for countable full-label Brier.
The retained finite head is independent of the two signal alphabets. -/
namespace IdExp.CountableBrier
open MeasureTheory Finset Set Filter Topology
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {Θ S T : Type*} [Countable Θ] [MeasurableSpace Θ]
  [MeasurableSingletonClass Θ] [Fintype S] [Fintype T]
variable (μ : Measure Θ) [IsProbabilityMeasure μ]

theorem forward_row (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (θ : Θ) (s : S) :
    μ.real {θ} * E θ s = ∑ t, joint μ E G s t * posterior μ E hE s θ := by
  rw [← sum_mul, sum_joint_right μ E G hG, mass_mul_posterior]

theorem reverse_row [Nonempty S] (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (θ : Θ) (s : S) :
    μ.real {θ} * finiteDecisionLaw (finiteDecisionLaw E G) (measurableBayesReverse μ E G) θ s =
      ∑ t, joint μ E G s t * posterior μ (finiteDecisionLaw E G)
        (finiteDecisionLaw_valid E hE G hG) t θ := by
  have hEG := finiteDecisionLaw_valid E hE G hG
  change μ.real {θ} * (∑ t, finiteDecisionLaw E G θ t * measurableBayesReverse μ E G t s) = _
  rw [mul_sum]
  apply sum_congr rfl
  intro t _
  have hm := sum_joint_left μ E hE G t
  change (∑ s, priorSignalMass μ E s * G s t) = _ at hm
  simp only [measurableBayesReverse, reverseOfMass, hm]
  by_cases ht : priorSignalMass μ (finiteDecisionLaw E G) t = 0
  · have hz : μ.real {θ} * finiteDecisionLaw E G θ t = 0 := by
      have hl := weighted_likelihood_le_mass μ _ hEG t θ
      have hn := mul_nonneg (show 0 ≤ μ.real {θ} from measureReal_nonneg) ((hEG θ).1 t)
      rw [ht] at hl
      linarith
    have hw : joint μ E G s t = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun s _ => joint_nonneg μ E hE G hG s t)).1
        ((sum_joint_left μ E hE G t).trans ht) s (mem_univ s)
    simp only [if_pos ht, hw, zero_mul]
    rw [← mul_assoc, hz, zero_mul]
  · simp only [if_neg ht, posterior_apply, priorSignalDensity, if_neg ht, joint]
    field_simp

theorem weighted_row_diff [Nonempty S] (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (θ : Θ) (s : S) :
    μ.real {θ} * (E θ s - finiteDecisionLaw (finiteDecisionLaw E G)
      (measurableBayesReverse μ E G) θ s) =
      ∑ t, joint μ E G s t * (posterior μ E hE s θ -
        posterior μ (finiteDecisionLaw E G) (finiteDecisionLaw_valid E hE G hG) t θ) := by
  rw [mul_sub, forward_row μ E hE G hG θ s, reverse_row μ E hE G hG θ s,
    ← sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  ring

theorem weighted_error_le [Nonempty S] (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (θ : Θ) :
    μ.real {θ} * decodeErr (finiteDecisionLaw E G) E (measurableBayesReverse μ E G) θ ≤
      (1/2) * ∑ s, ∑ t, joint μ E G s t * |posterior μ E hE s θ -
        posterior μ (finiteDecisionLaw E G) (finiteDecisionLaw_valid E hE G hG) t θ| := by
  change μ.real {θ} * finiteTV (finiteDecisionLaw (finiteDecisionLaw E G)
    (measurableBayesReverse μ E G) θ) (E θ) ≤ _
  unfold finiteTV
  simp_rw [abs_sub_comm]
  rw [← mul_assoc, mul_comm (μ.real {θ}) (1/2), mul_assoc, mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply sum_le_sum
  intro s _
  calc μ.real {θ} * |E θ s - finiteDecisionLaw (finiteDecisionLaw E G) (measurableBayesReverse μ E G) θ s| =
      |μ.real {θ} * (E θ s - finiteDecisionLaw (finiteDecisionLaw E G)
        (measurableBayesReverse μ E G) θ s)| := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ μ.real {θ} from measureReal_nonneg)]
    _ = |∑ t, joint μ E G s t * (posterior μ E hE s θ -
        posterior μ (finiteDecisionLaw E G) (finiteDecisionLaw_valid E hE G hG) t θ)| := by
      rw [weighted_row_diff μ E hE G hG θ s]
    _ ≤ ∑ t, |joint μ E G s t * (posterior μ E hE s θ -
        posterior μ (finiteDecisionLaw E G) (finiteDecisionLaw_valid E hE G hG) t θ)| :=
      abs_sum_le_sum_abs _ _
    _ = _ := by
      apply sum_congr rfl
      intro t _
      rw [abs_mul, abs_of_nonneg (joint_nonneg μ E hE G hG s t), abs_sub_comm]

/-- Squared distances between full countable probability reports are summable. -/
theorem square_distance_summable (p q : FullLabelBrierReport Θ) :
    Summable (fun θ => (p θ - q θ)^2) := by
  apply Summable.of_nonneg_of_le (fun θ => sq_nonneg _)
    (f := fun θ => 2 * (p θ + q θ)) _ ((p.summable.add q.summable).mul_left 2)
  intro θ
  have hp0 := p.nonneg θ
  have hp1 := p.le_one θ
  have hq0 := q.nonneg θ
  have hq1 := q.le_one θ
  nlinarith [mul_nonneg hp0 hq0]

theorem weighted_squared_estimate (w : S → T → ℝ) (hw : ∀ s t, 0 ≤ w s t)
    (h1 : ∑ s, ∑ t, w s t = 1) (d : S → T → ℝ) :
    (∑ s, ∑ t, w s t * |d s t|)^2 ≤ ∑ s, ∑ t, w s t * (d s t)^2 := by
  have hJ := (convexOn_pow 2 : ConvexOn ℝ (Set.Ici 0) fun x : ℝ => x^2).map_sum_le
    (t := (univ : Finset (S × T))) (w := fun x => w x.1 x.2) (p := fun x => |d x.1 x.2|)
    (fun x _ => hw x.1 x.2) (by rw [Fintype.sum_prod_type]; exact h1)
    (fun x _ => Set.mem_Ici.2 (abs_nonneg _))
  simpa only [smul_eq_mul, Fintype.sum_prod_type, sq_abs] using hJ

/-- Finite-head average reconstruction error is controlled by the complete Brier loss. -/
theorem head_error_le [Nonempty S] (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (F : Finset Θ) :
    (∑ θ ∈ F, μ.real {θ} * decodeErr (finiteDecisionLaw E G) E (measurableBayesReverse μ E G) θ) ≤
      (1/2) * Real.sqrt ((F.card : ℝ) * movement μ E hE G hG) := by
  let d := fun s t θ => posterior μ E hE s θ -
    posterior μ (finiteDecisionLaw E G) (finiteDecisionLaw_valid E hE G hG) t θ
  let a := fun θ => ∑ s, ∑ t, joint μ E G s t * |d s t θ|
  let b := fun θ => ∑ s, ∑ t, joint μ E G s t * (d s t θ)^2
  have hab θ : (a θ)^2 ≤ b θ :=
    weighted_squared_estimate (joint μ E G) (joint_nonneg μ E hE G hG)
      (sum_joint μ E hE G hG) (fun s t => d s t θ)
  have hsum : ∑ θ ∈ F, b θ ≤ movement μ E hE G hG := by
    unfold b movement
    rw [sum_comm]
    apply sum_le_sum
    intro s _
    rw [sum_comm]
    apply sum_le_sum
    intro t _
    rw [← mul_sum]
    apply mul_le_mul_of_nonneg_left _ (joint_nonneg μ E hE G hG s t)
    exact (square_distance_summable (posterior μ E hE s)
      (posterior μ (finiteDecisionLaw E G) (finiteDecisionLaw_valid E hE G hG) t)).sum_le_tsum
        F (fun θ _ => sq_nonneg _)
  have hs : (∑ θ ∈ F, a θ)^2 ≤ (F.card : ℝ) * movement μ E hE G hG := by
    calc _ ≤ (F.card : ℝ) * ∑ θ ∈ F, (a θ)^2 :=
        sq_sum_le_card_mul_sum_sq
      _ ≤ (F.card : ℝ) * ∑ θ ∈ F, b θ := by
        exact mul_le_mul_of_nonneg_left (sum_le_sum fun θ _ => hab θ) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
  calc _ ≤ ∑ θ ∈ F, (1/2) * a θ := sum_le_sum fun θ _ => weighted_error_le μ E hE G hG θ
    _ = (1/2) * ∑ θ ∈ F, a θ := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le hs) (by norm_num)

/-- A literal Bayes decoder: prior tail plus square root of head size times Brier loss. -/
theorem reverse_error_le_head_tail [Nonempty S] (E : FiniteExperiment Θ S)
    (hE : IsFiniteExperiment E) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T)
    (F : Finset Θ) :
    priorAverageDecodeErr μ (finiteDecisionLaw E G) E (measurableBayesReverse μ E G) ≤
      μ.real ((F : Set Θ)ᶜ) + (1/2) * Real.sqrt ((F.card : ℝ) *
        (potential μ E hE - potential μ (finiteDecisionLaw E G) (finiteDecisionLaw_valid E hE G hG))) := by
  have hEG := finiteDecisionLaw_valid E hE G hG
  have hR := measurableBayesReverse_stochastic μ E hE (fun _ => measurable_of_countable _) G hG
  have hi := integrable_finiteDecodeErr μ (finiteDecisionLaw E G) E hEG hE
    (fun _ => measurable_of_countable _) (fun _ => measurable_of_countable _) _ hR
  have ht : (∫ θ in (F : Set Θ)ᶜ, decodeErr (finiteDecisionLaw E G) E
      (measurableBayesReverse μ E G) θ ∂μ) ≤ μ.real ((F : Set Θ)ᶜ) := by
    have h := integral_mono (μ := μ.restrict ((F : Set Θ)ᶜ)) hi.integrableOn (integrable_const (1 : ℝ))
      (decodeErr_le_one _ _ hEG hE _ hR)
    simpa using h
  have hh := head_error_le μ E hE G hG F
  rw [movement_eq] at hh
  unfold priorAverageDecodeErr
  rw [← integral_add_compl F.measurableSet hi, setIntegral_finset F hi.integrableOn]
  simp only [smul_eq_mul]
  linarith

/-- The same countable bound holds for the infimum over all randomized decoders. -/
theorem reverse_deficiency_le_head_tail [Nonempty S] (E : FiniteExperiment Θ S)
    (hE : IsFiniteExperiment E) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T)
    (F : Finset Θ) :
    priorAverageDeficiency μ (finiteDecisionLaw E G) E ≤
      μ.real ((F : Set Θ)ᶜ) + (1/2) * Real.sqrt ((F.card : ℝ) *
        (potential μ E hE - potential μ (finiteDecisionLaw E G) (finiteDecisionLaw_valid E hE G hG))) :=
  priorAverageDeficiency_le_of_decoder μ _ _ _
    (measurableBayesReverse_stochastic μ E hE (fun _ => measurable_of_countable _) G hG) _
    (reverse_error_le_head_tail μ E hE G hG F)

/-- Every countable probability prior has finite heads with arbitrarily small tails. -/
theorem exists_small_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset Θ, μ.real ((F : Set Θ)ᶜ) < ε := by
  let p := FullLabelBrierReport.ofMeasure μ
  have ht := p.summable.hasSum
  rw [p.sum_one] at ht
  have hh : 1 - ε < (1 : ℝ) := by linarith
  obtain ⟨F, hF⟩ := (ht.eventually (eventually_gt_nhds hh)).exists
  refine ⟨F, ?_⟩
  have he : ∑ θ ∈ F, p θ = μ.real (F : Set Θ) := by
    change (∑ θ ∈ F, μ.real {θ}) = μ.real (F : Set Θ)
    exact sum_measureReal_singleton F
  rw [he] at hF
  rw [measureReal_compl F.measurableSet]
  simp only [probReal_univ]
  linarith

/-- Small Brier loss uniformly permits reversal, on arbitrary finite alphabets.
The modulus uses only the prior and the desired error, not a prior entropy bound. -/
theorem vanishing_reverse_modulus (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ {S T : Type*} [Fintype S] [Fintype T] [Nonempty S]
      (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
      (G : S → T → ℝ) (hG : G ∈ stochasticRules S T),
      potential μ E hE - potential μ (finiteDecisionLaw E G) (finiteDecisionLaw_valid E hE G hG) < η →
      priorAverageDeficiency μ (finiteDecisionLaw E G) E < ε := by
  obtain ⟨F, hF⟩ := exists_small_tail μ (ε/2) (half_pos hε)
  refine ⟨ε^2 / ((F.card : ℝ) + 1), by positivity, ?_⟩
  intro S T _ _ _ E hE G hG hsmall
  have hD : 0 ≤ potential μ E hE -
      potential μ (finiteDecisionLaw E G) (finiteDecisionLaw_valid E hE G hG) :=
    sub_nonneg.mpr (potential_mono_garbling μ E hE G hG)
  have hn : 0 ≤ (F.card : ℝ) := Nat.cast_nonneg _
  have hden : 0 < (F.card : ℝ) + 1 := by positivity
  have hprod := (lt_div_iff₀ hden).mp hsmall
  have hsq : (F.card : ℝ) * (potential μ E hE -
      potential μ (finiteDecisionLaw E G) (finiteDecisionLaw_valid E hE G hG)) < ε^2 := by
    nlinarith
  have hr := (Real.sqrt_lt' hε).2 hsq
  have hb := reverse_deficiency_le_head_tail μ E hE G hG F
  linarith

end
end IdExp.CountableBrier
