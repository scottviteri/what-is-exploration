import Formal.MeasurableInformationForms

/-!
# A single Bayes reverse decoder for arbitrary measurable worlds

Finite signal alphabets make the reverse matrix explicit. Predictive-null
coordinates vanish almost everywhere under the prior, which suffices for the
integrated KL identity and squared-TV bound. No full support or world topology
is needed for this information-theoretic step.
-/

namespace IdExp

open MeasureTheory Set Finset

noncomputable section

variable {S T : Type*} [Fintype S] [Fintype T] [Nonempty S]

def reverseOfMass (p : S → ℝ) (G : S → T → ℝ) : T → S → ℝ :=
  fun t s => if (∑ s', p s' * G s' t) = 0 then uniformPrior S s
    else p s * G s t / (∑ s', p s' * G s' t)

theorem reverseOfMass_stochastic (p : S → ℝ) (hp : IsDist p)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) :
    reverseOfMass p G ∈ stochasticRules T S := by
  classical
  intro t _
  by_cases hq : (∑ s, p s * G s t) = 0
  · change IsDist (reverseOfMass p G t)
    have he : reverseOfMass p G t = uniformPrior S := funext fun s => by simp [reverseOfMass, hq]
    rw [he]
    exact isDist_uniformPrior
  · constructor
    · intro s
      simp only [reverseOfMass, if_neg hq]
      exact div_nonneg (mul_nonneg (hp.1 s) ((hG s (mem_univ s)).1 t))
        (sum_nonneg fun s _ => mul_nonneg (hp.1 s) ((hG s (mem_univ s)).1 t))
    · simp only [reverseOfMass, if_neg hq, ← sum_div, div_self hq]

omit [Nonempty S] in
theorem jointReverseOfMass_ac (p f : S → ℝ) (hp : IsDist p) (hf : IsDist f)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T)
    (hsupp : ∀ s, p s = 0 → f s = 0) :
    ∀ z : S × T, (∑ s, f s * G s z.2) * reverseOfMass p G z.2 z.1 = 0 →
      f z.1 * G z.1 z.2 = 0 := by
  rintro ⟨s, t⟩ hz
  have hzero : (∑ s', f s' * G s' t) = 0 → f s * G s t = 0 := fun h =>
    (sum_eq_zero_iff_of_nonneg (fun s' _ =>
      mul_nonneg (hf.1 s') ((hG s' (mem_univ s')).1 t))).1 h s (mem_univ s)
  by_cases hq : (∑ s', p s' * G s' t) = 0
  · have h := (sum_eq_zero_iff_of_nonneg (fun s' _ =>
      mul_nonneg (hp.1 s') ((hG s' (mem_univ s')).1 t))).1 hq s (mem_univ s)
    rcases mul_eq_zero.mp h with h | h
    · rw [hsupp s h, zero_mul]
    · rw [h, mul_zero]
  · simp only [reverseOfMass, if_neg hq] at hz
    rcases mul_eq_zero.mp hz with h | h
    · exact hzero h
    · have h := (div_eq_zero_iff.mp h).resolve_right hq
      rcases mul_eq_zero.mp h with h | h
      · rw [hsupp s h, zero_mul]
      · rw [h, mul_zero]

omit [Nonempty S] in
/-- The rowwise joint KL identity uses only support inclusion in the predictive row. -/
theorem finiteKL_joint_reverseOfMass (p f : S → ℝ) (hp : IsDist p) (hf : IsDist f)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T)
    (hsupp : ∀ s, p s = 0 → f s = 0) :
    finiteKL (fun z : S × T => f z.1 * G z.1 z.2)
      (fun z => (∑ s, f s * G s z.2) * reverseOfMass p G z.2 z.1) =
    finiteKL f p - finiteKL (fun t => ∑ s, f s * G s t) (fun t => ∑ s, p s * G s t) := by
  have hkey (s : S) (t : T) :
      f s * G s t * Real.log (f s * G s t /
        ((∑ s', f s' * G s' t) * reverseOfMass p G t s)) =
      f s * G s t * Real.log (f s / p s) -
        f s * G s t * Real.log ((∑ s', f s' * G s' t) / (∑ s', p s' * G s' t)) := by
    by_cases h : f s * G s t = 0
    · simp [h]
    · have hf0 := (mul_ne_zero_iff.mp h).1
      have hG0 := (mul_ne_zero_iff.mp h).2
      have hp0 : p s ≠ 0 := fun hz => hf0 (hsupp s hz)
      have hfpos : 0 < f s := lt_of_le_of_ne (hf.1 s) (Ne.symm hf0)
      have hppos : 0 < p s := lt_of_le_of_ne (hp.1 s) (Ne.symm hp0)
      have hGpos : 0 < G s t := lt_of_le_of_ne ((hG s (mem_univ s)).1 t) (Ne.symm hG0)
      have hfg : (∑ s', f s' * G s' t) ≠ 0 := ne_of_gt ((mul_pos hfpos hGpos).trans_le
        (single_le_sum (fun s' _ => mul_nonneg (hf.1 s') ((hG s' (mem_univ s')).1 t)) (mem_univ s)))
      have hpg : (∑ s', p s' * G s' t) ≠ 0 := ne_of_gt ((mul_pos hppos hGpos).trans_le
        (single_le_sum (fun s' _ => mul_nonneg (hp.1 s') ((hG s' (mem_univ s')).1 t)) (mem_univ s)))
      simp only [reverseOfMass, if_neg hpg]
      have he : f s * G s t / ((∑ s', f s' * G s' t) *
          (p s * G s t / (∑ s', p s' * G s' t))) =
          (f s / p s) / ((∑ s', f s' * G s' t) / (∑ s', p s' * G s' t)) := by
        field_simp
      rw [he, Real.log_div (div_ne_zero hf0 hp0) (div_ne_zero hfg hpg)]
      ring
  unfold finiteKL
  rw [Fintype.sum_prod_type]
  simp_rw [hkey, sum_sub_distrib]
  congr 1
  · apply sum_congr rfl
    intro s _
    calc (∑ t, f s * G s t * Real.log (f s / p s)) =
        (f s * Real.log (f s / p s)) * ∑ t, G s t := by
          rw [mul_sum]; apply sum_congr rfl; intro t _; ring
      _ = _ := by rw [(hG s (mem_univ s)).2, mul_one]
  · rw [sum_comm]
    apply sum_congr rfl
    intro t _
    rw [← sum_mul]

variable {Θ : Type*} [MeasurableSpace Θ]

def measurableBayesReverse (μ : Measure Θ) (F : FiniteExperiment Θ S) (G : S → T → ℝ) :
    T → S → ℝ := reverseOfMass (priorSignalMass μ F) G

theorem measurableBayesReverse_stochastic (μ : Measure Θ) [IsProbabilityMeasure μ]
    (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F)
    (hm : ∀ s, Measurable (fun θ => F θ s)) (G : S → T → ℝ)
    (hG : G ∈ stochasticRules S T) : measurableBayesReverse μ F G ∈ stochasticRules T S :=
  reverseOfMass_stochastic _
    (priorSignalMass_isDist μ F hF (integrable_measurableFiniteExperiment_coordinate μ F hF hm)) G hG

omit [Nonempty S] in
/-- Null predictive signals vanish simultaneously outside one prior-null set. -/
theorem ae_priorSignalMass_support (μ : Measure Θ) [IsFiniteMeasure μ]
    (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F)
    (hm : ∀ s, Measurable (fun θ => F θ s)) :
    ∀ᵐ θ ∂μ, ∀ s, priorSignalMass μ F s = 0 → F θ s = 0 := by
  rw [ae_all_iff]
  intro s
  by_cases hs : priorSignalMass μ F s = 0
  · filter_upwards [priorSignalMass_zero_ae μ F hF hm s hs] with θ hθ
    exact fun _ => hθ
  · exact Filter.Eventually.of_forall fun _ h => (hs h).elim

/-- Integrated forward/reverse joint KL equals the information lost by garbling. -/
theorem integral_finiteKL_joint_eq_information_gap
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F)
    (hm : ∀ s, Measurable (fun θ => F θ s)) (G : S → T → ℝ)
    (hG : G ∈ stochasticRules S T) :
    (∫ θ, finiteKL (jointForward F G θ) (jointReverse F G (measurableBayesReverse μ F G) θ) ∂μ) =
      infinitePriorInformation μ F - infinitePriorInformation μ (finiteDecisionLaw F G) := by
  have hFG := finiteDecisionLaw_valid F hF G hG
  have hFGm := measurable_finiteDecisionLaw F hm G
  have hp := priorSignalMass_isDist μ F hF (integrable_measurableFiniteExperiment_coordinate μ F hF hm)
  have he : (fun θ => finiteKL (jointForward F G θ)
      (jointReverse F G (measurableBayesReverse μ F G) θ)) =ᵐ[μ]
      (fun θ => finiteKL (F θ) (priorSignalMass μ F) -
        finiteKL (finiteDecisionLaw F G θ) (priorSignalMass μ (finiteDecisionLaw F G))) := by
    filter_upwards [ae_priorSignalMass_support μ F hF hm] with θ hθ
    have h := finiteKL_joint_reverseOfMass (priorSignalMass μ F) (F θ) hp (hF θ) G hG hθ
    have hq : (fun t => ∑ s, priorSignalMass μ F s * G s t) =
        priorSignalMass μ (finiteDecisionLaw F G) := funext fun t =>
      priorSignalMass_garbling μ F _
        (integrable_measurableFiniteExperiment_coordinate μ F hF hm) G rfl t
    rw [hq] at h
    exact h
  rw [integral_congr_ae he, integral_sub]
  · rw [← infinitePriorInformation_eq_integral_finiteKL μ F hF hm,
      ← infinitePriorInformation_eq_integral_finiteKL μ _ hFG hFGm]
  · exact integrable_finsetSum _ fun s _ => integrable_finiteExperiment_log_ratio μ F hF hm s _
  · exact integrable_finsetSum _ fun t _ => integrable_finiteExperiment_log_ratio μ _ hFG hFGm t _

/-- The explicit prior-dependent matrix has mean-square reverse error at most
half the information loss, for any measurable finite-output experiment. -/
theorem integral_reverse_sq_le_information_gap
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F)
    (hm : ∀ s, Measurable (fun θ => F θ s)) (G : S → T → ℝ)
    (hG : G ∈ stochasticRules S T) :
    (∫ θ, (decodeErr (finiteDecisionLaw F G) F (measurableBayesReverse μ F G) θ)^2 ∂μ) ≤
      (infinitePriorInformation μ F - infinitePriorInformation μ (finiteDecisionLaw F G)) / 2 := by
  have hR := measurableBayesReverse_stochastic μ F hF hm G hG
  have hp := priorSignalMass_isDist μ F hF (integrable_measurableFiniteExperiment_coordinate μ F hF hm)
  have hpoint : ∀ᵐ θ ∂μ,
      (decodeErr (finiteDecisionLaw F G) F (measurableBayesReverse μ F G) θ)^2 ≤
      finiteKL (jointForward F G θ) (jointReverse F G (measurableBayesReverse μ F G) θ) / 2 := by
    filter_upwards [ae_priorSignalMass_support μ F hF hm] with θ hθ
    have hpin := finiteTV_sq_le_finiteKL_half _ _ (jointForward_isDist (fun _ : Unit => F θ) (fun _ => hF θ) G hG ())
      (jointReverse_isDist (fun _ : Unit => F θ) (fun _ => hF θ) G hG _ hR ())
      (jointReverseOfMass_ac _ _ hp (hF θ) G hG hθ)
    change (finiteTV (jointForward F G θ) (jointReverse F G (measurableBayesReverse μ F G) θ))^2 ≤
      finiteKL (jointForward F G θ) (jointReverse F G (measurableBayesReverse μ F G) θ) / 2 at hpin
    have hcon := finiteTV_marginal_fst_le (jointForward F G θ)
      (jointReverse F G (measurableBayesReverse μ F G) θ)
    have he1 : (fun s => ∑ t, jointForward F G θ (s, t)) = F θ :=
      funext fun s => jointForward_marginal (fun _ : Unit => F θ) G hG () s
    have he2 : (fun s => ∑ t, jointReverse F G (measurableBayesReverse μ F G) θ (s, t)) =
        finiteDecisionLaw (finiteDecisionLaw F G) (measurableBayesReverse μ F G) θ := rfl
    rw [he1, he2] at hcon
    have hs : decodeErr (finiteDecisionLaw F G) F (measurableBayesReverse μ F G) θ =
        finiteTV (F θ) (finiteDecisionLaw (finiteDecisionLaw F G) (measurableBayesReverse μ F G) θ) :=
      finiteTV_symm _ _
    rw [hs]
    have h0 := finiteTV_nonneg (F θ)
      (finiteDecisionLaw (finiteDecisionLaw F G) (measurableBayesReverse μ F G) θ)
    nlinarith
  have hFG := finiteDecisionLaw_valid F hF G hG
  have hFGm := measurable_finiteDecisionLaw F hm G
  have hJi : Integrable (fun θ => finiteKL (jointForward F G θ)
      (jointReverse F G (measurableBayesReverse μ F G) θ)) μ := by
    have hi := (integrable_finsetSum univ fun s _ =>
      integrable_finiteExperiment_log_ratio μ F hF hm s (priorSignalMass μ F s)).sub
      (integrable_finsetSum univ fun t _ =>
        integrable_finiteExperiment_log_ratio μ _ hFG hFGm t (priorSignalMass μ (finiteDecisionLaw F G) t))
    apply hi.congr
    filter_upwards [ae_priorSignalMass_support μ F hF hm] with θ hθ
    have h := finiteKL_joint_reverseOfMass (priorSignalMass μ F) (F θ) hp (hF θ) G hG hθ
    symm
    have hq : (fun t => ∑ s, priorSignalMass μ F s * G s t) =
        priorSignalMass μ (finiteDecisionLaw F G) := funext fun t =>
      priorSignalMass_garbling μ F _
        (integrable_measurableFiniteExperiment_coordinate μ F hF hm) G rfl t
    rw [hq] at h
    change finiteKL (jointForward F G θ)
      (jointReverse F G (measurableBayesReverse μ F G) θ) =
      finiteKL (F θ) (priorSignalMass μ F) -
        finiteKL (finiteDecisionLaw F G θ) (priorSignalMass μ (finiteDecisionLaw F G))
    exact h
  have h := integral_mono_ae
    (integrable_sq_finiteDecodeErr μ _ F hFG hF hFGm hm _ hR) (hJi.div_const 2) hpoint
  rw [integral_div, integral_finiteKL_joint_eq_information_gap μ F hF hm G hG] at h
  exact h

end
end IdExp
