import Formal.CountableBrierScore
import Formal.MeasurableReversePinsker

/-! Literal full-label posterior KL and information loss under finite garbling
on countable worlds, with positive prior atoms. -/
namespace IdExp.CountablePosteriorKL
open MeasureTheory Finset Set
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {Θ S T : Type*} [Countable Θ] [MeasurableSpace Θ]
  [MeasurableSingletonClass Θ] [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
  (μ : Measure Θ) [IsProbabilityMeasure μ]
  (hp : ∀ θ, 0 < μ.real {θ})
  (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
  (G : S → T → ℝ) (hG : G ∈ stochasticRules S T)

def term (s : S) (t : T) (θ : Θ) : ℝ :=
  E θ s * G s t * Real.log ((E θ s / priorSignalMass μ E s) /
    (finiteDecisionLaw E G θ t / priorSignalMass μ (finiteDecisionLaw E G) t))

include hE hG in
lemma entry_le (θ : Θ) (s : S) (t : T) :
    E θ s * G s t ≤ finiteDecisionLaw E G θ t :=
  single_le_sum (fun z _ => mul_nonneg ((hE θ).1 z) ((hG z (mem_univ z)).1 t)) (mem_univ s)

include hp hE in
lemma mass_ne_zero (s : S) (θ : Θ) (he : E θ s ≠ 0) : priorSignalMass μ E s ≠ 0 := by
  have hn := CountableBrier.weighted_likelihood_le_mass μ E hE s θ
  have hpos : 0 < E θ s := lt_of_le_of_ne ((hE θ).1 s) (Ne.symm he)
  exact ne_of_gt ((mul_pos (hp θ) hpos).trans_le hn)

include hE hG in
lemma cross_integrable (s : S) (t : T) (m : ℝ) :
    Integrable (fun θ => E θ s * G s t * Real.log (finiteDecisionLaw E G θ t / m)) μ := by
  have hF := finiteDecisionLaw_valid E hE G hG
  have hmF := measurable_finiteDecisionLaw E (fun _ => measurable_of_countable _) G
  have hi := integrable_finiteExperiment_log_ratio μ (finiteDecisionLaw E G) hF hmF t m
  apply hi.norm.mono' (measurable_of_countable _).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro θ
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg ((hE θ).1 s), abs_of_nonneg ((hG s (mem_univ s)).1 t),
    abs_of_nonneg ((hF θ).1 t)]
  exact mul_le_mul_of_nonneg_right (entry_le E hE G hG θ s t) (abs_nonneg _)

include hp hE hG in
lemma term_eq_difference (s : S) (t : T) (θ : Θ) :
    term μ E G s t θ =
      G s t * (E θ s * Real.log (E θ s / priorSignalMass μ E s)) -
      E θ s * G s t * Real.log (finiteDecisionLaw E G θ t /
        priorSignalMass μ (finiteDecisionLaw E G) t) := by
  by_cases he : E θ s = 0
  · simp [term, he]
  by_cases hg : G s t = 0
  · simp [term, hg]
  have hm := mass_ne_zero μ hp E hE s θ he
  have hF := finiteDecisionLaw_valid E hE G hG
  have hf : finiteDecisionLaw E G θ t ≠ 0 := ne_of_gt
    ((mul_pos (lt_of_le_of_ne ((hE θ).1 s) (Ne.symm he))
      (lt_of_le_of_ne ((hG s (mem_univ s)).1 t) (Ne.symm hg))).trans_le
        (entry_le E hE G hG θ s t))
  have hn := mass_ne_zero μ hp (finiteDecisionLaw E G) hF t θ hf
  unfold term
  rw [Real.log_div (div_ne_zero he hm) (div_ne_zero hf hn)]
  ring

include hp hE hG in
lemma term_integrable (s : S) (t : T) : Integrable (term μ E G s t) μ := by
  have hi := (integrable_finiteExperiment_log_ratio μ E hE
    (fun _ => measurable_of_countable _) s (priorSignalMass μ E s)).const_mul (G s t)
  apply (hi.sub (cross_integrable μ E hE G hG s t _)).congr
  exact Filter.Eventually.of_forall fun θ => (term_eq_difference μ hp E hE G hG s t θ).symm

include hp hE hG in
lemma integral_sum_term :
    (∫ θ, ∑ s, ∑ t, term μ E G s t θ ∂μ) =
      infinitePriorInformation μ E - infinitePriorInformation μ (finiteDecisionLaw E G) := by
  have hF := finiteDecisionLaw_valid E hE G hG
  have hmE := fun s => (measurable_of_countable (fun θ => E θ s))
  have hmF := measurable_finiteDecisionLaw E hmE G
  have heq (θ : Θ) : (∑ s, ∑ t, term μ E G s t θ) =
      finiteKL (E θ) (priorSignalMass μ E) -
        finiteKL (finiteDecisionLaw E G θ) (priorSignalMass μ (finiteDecisionLaw E G)) := by
    simp_rw [term_eq_difference μ hp E hE G hG, sum_sub_distrib]
    congr 1
    · unfold finiteKL
      apply sum_congr rfl
      intro s _
      rw [← sum_mul, (hG s (mem_univ s)).2, one_mul]
    · rw [sum_comm]
      unfold finiteKL
      apply sum_congr rfl
      intro t _
      rw [← sum_mul]
      rfl
  simp_rw [heq]
  rw [integral_sub]
  · rw [← infinitePriorInformation_eq_integral_finiteKL μ E hE hmE,
      ← infinitePriorInformation_eq_integral_finiteKL μ _ hF hmF]
  · exact integrable_finsetSum _ fun s _ => integrable_finiteExperiment_log_ratio μ E hE hmE s _
  · exact integrable_finsetSum _ fun t _ => integrable_finiteExperiment_log_ratio μ _ hF hmF t _


include hp hE hG in
lemma posterior_coordinate (s : S) (t : T) (θ : Θ) :
    (priorSignalMass μ E s * G s t) *
      (CountableBrier.posterior μ E hE s θ * Real.log
        (CountableBrier.posterior μ E hE s θ /
          CountableBrier.posterior μ (finiteDecisionLaw E G)
            (finiteDecisionLaw_valid E hE G hG) t θ)) =
    μ.real {θ} * term μ E G s t θ := by
  by_cases hm : priorSignalMass μ E s = 0
  · have he : E θ s = 0 := by
      by_contra he
      exact mass_ne_zero μ hp E hE s θ he hm
    simp [hm, term, he]
  by_cases hg : G s t = 0
  · simp [hg, term]
  by_cases he : E θ s = 0
  · have hpz : CountableBrier.posterior μ E hE s θ = 0 := by
      simp [CountableBrier.posterior_apply, priorSignalDensity, hm, he]
    simp [hpz, term, he]
  have hF := finiteDecisionLaw_valid E hE G hG
  have hf : finiteDecisionLaw E G θ t ≠ 0 := ne_of_gt
    ((mul_pos (lt_of_le_of_ne ((hE θ).1 s) (Ne.symm he))
      (lt_of_le_of_ne ((hG s (mem_univ s)).1 t) (Ne.symm hg))).trans_le
        (entry_le E hE G hG θ s t))
  have hn := mass_ne_zero μ hp (finiteDecisionLaw E G) hF t θ hf
  simp only [CountableBrier.posterior_apply, priorSignalDensity, if_neg hm, if_neg hn]
  rw [mul_div_mul_right _ _ (ne_of_gt (hp θ))]
  unfold term
  field_simp

/-- Integrability on a countable space supplies genuine summability of the
atomic contributions; the real tsum does not use its divergent default. -/
lemma atomic_summable {f : Θ → ℝ} (hf : Integrable f μ) :
    Summable (fun θ => μ.real {θ} * f θ) := by
  have hi : Integrable f (Measure.sum (fun θ => μ {θ} • Measure.dirac θ)) := by
    simpa only [Measure.sum_smul_dirac] using hf
  have hs := (hasSum_integral_measure hi).summable
  simpa only [integral_smul_measure, integral_dirac, measureReal_def, smul_eq_mul] using hs

include hp hE hG in
/-- Every positive-probability source/garbled pair has a finite, absolutely
summable full-label posterior log-ratio series. -/
theorem posteriorKL_summable (s : S) (t : T)
    (hj : 0 < priorSignalMass μ E s * G s t) :
    Summable (fun θ => CountableBrier.posterior μ E hE s θ * Real.log
      (CountableBrier.posterior μ E hE s θ /
        CountableBrier.posterior μ (finiteDecisionLaw E G)
          (finiteDecisionLaw_valid E hE G hG) t θ)) := by
  apply (summable_mul_left_iff (ne_of_gt hj)).mp
  simpa only [posterior_coordinate μ hp E hE G hG] using
    atomic_summable μ (term_integrable μ hp E hE G hG s t)

include hp hE hG in
/-- A posterior after a positive-probability refined signal puts no positive
mass where its garbled predecessor has zero mass. -/
theorem posteriorKL_support (s : S) (t : T)
    (hj : 0 < priorSignalMass μ E s * G s t) (θ : Θ)
    (hz : CountableBrier.posterior μ (finiteDecisionLaw E G)
      (finiteDecisionLaw_valid E hE G hG) t θ = 0) :
    CountableBrier.posterior μ E hE s θ = 0 := by
  have hm0 := (CountableBrier.mass_valid μ E hE).1 s
  have hg0 := (hG s (mem_univ s)).1 t
  have hm : priorSignalMass μ E s ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hj)).1
  have hg : G s t ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hj)).2
  have hc := CountableBrier.mass_mul_posterior μ (finiteDecisionLaw E G)
    (finiteDecisionLaw_valid E hE G hG) t θ
  rw [hz, mul_zero] at hc
  have hf : finiteDecisionLaw E G θ t = 0 :=
    (mul_eq_zero.mp hc.symm).resolve_left (ne_of_gt (hp θ))
  have hx := entry_le E hE G hG θ s t
  rw [hf] at hx
  have he : E θ s = 0 := (mul_eq_zero.mp
    (le_antisymm hx (mul_nonneg ((hE θ).1 s) hg0))).resolve_right hg
  have hb := CountableBrier.mass_mul_posterior μ E hE s θ
  rw [he, mul_zero] at hb
  exact (mul_eq_zero.mp hb).resolve_left hm

include hp hE hG in
/-- Literal expected posterior KL equals information lost by the finite
stochastic garbling. Logarithms and information are both in nats. -/
theorem information_gap_eq_expected_posteriorKL :
    infinitePriorInformation μ E - infinitePriorInformation μ (finiteDecisionLaw E G) =
      ∑ s, ∑ t, (priorSignalMass μ E s * G s t) *
        ∑' θ, CountableBrier.posterior μ E hE s θ * Real.log
          (CountableBrier.posterior μ E hE s θ /
            CountableBrier.posterior μ (finiteDecisionLaw E G)
              (finiteDecisionLaw_valid E hE G hG) t θ) := by
  rw [← integral_sum_term μ hp E hE G hG]
  rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _
    (fun t _ => term_integrable μ hp E hE G hG s t))]
  apply sum_congr rfl
  intro s _
  rw [integral_finsetSum _ (fun t _ => term_integrable μ hp E hE G hG s t)]
  apply sum_congr rfl
  intro t _
  rw [integral_countable (term_integrable μ hp E hE G hG s t), ← tsum_mul_left]
  apply tsum_congr
  intro θ
  simpa only [smul_eq_mul] using (posterior_coordinate μ hp E hE G hG s t θ).symm

end
end IdExp.CountablePosteriorKL
