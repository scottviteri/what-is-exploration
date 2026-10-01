import Formal.PulseBrierPosterior
import Formal.PriorAverageDeficiency

/-! Countable full-label Brier scores for arbitrary finite experiments.
No finite Shannon entropy or positive-atom premise is imposed. -/
namespace IdExp.CountableBrier
open MeasureTheory Finset Set Filter Topology
noncomputable section
set_option maxHeartbeats 1000000
variable {Θ S T : Type*} [Countable Θ] [MeasurableSpace Θ]
  [MeasurableSingletonClass Θ] [Fintype S] [Fintype T]
variable (μ : Measure Θ) [IsProbabilityMeasure μ]

theorem likelihood_integrable (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (s : S) : Integrable (fun θ => E θ s) μ :=
  integrable_measurableFiniteExperiment_coordinate μ E hE (fun _ => measurable_of_countable _) s

def posterior (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (s : S) : FullLabelBrierReport Θ := by
  letI := priorPosteriorMeasure_probability μ E hE (likelihood_integrable μ E hE) s
  exact FullLabelBrierReport.ofMeasure (priorPosteriorMeasure μ E s)

theorem posterior_apply (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (s : S) (θ : Θ) :
    posterior μ E hE s θ = priorSignalDensity μ E s θ * μ.real {θ} := by
  change (priorPosteriorMeasure μ E s).real {θ} = _
  rw [measureReal_def, priorPosteriorMeasure,
    withDensity_apply _ (measurableSet_singleton θ), lintegral_singleton,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (priorSignalDensity_nonneg μ E hE s θ)]
  rfl

theorem weighted_likelihood_le_mass (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (s : S) (θ : Θ) : μ.real {θ} * E θ s ≤ priorSignalMass μ E s := by
  have h := setIntegral_le_integral (likelihood_integrable μ E hE s)
    (Eventually.of_forall fun θ => (hE θ).1 s) (s := {θ})
  simpa [integral_singleton, smul_eq_mul, priorSignalMass, measureReal_def] using h

/-- Bayes' joint-law identity, including null records and zero-prior worlds. -/
theorem mass_mul_posterior (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (s : S) (θ : Θ) :
    priorSignalMass μ E s * posterior μ E hE s θ = μ.real {θ} * E θ s := by
  rw [posterior_apply]
  by_cases hs : priorSignalMass μ E s = 0
  · have hn := mul_nonneg (show 0 ≤ μ.real {θ} from measureReal_nonneg) ((hE θ).1 s)
    have hz := weighted_likelihood_le_mass μ E hE s θ
    rw [hs] at hz ⊢
    linarith
  · simp only [priorSignalDensity, if_neg hs]
    field_simp

def potential (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E) : ℝ :=
  ∑ s, priorSignalMass μ E s * (posterior μ E hE s).potential

theorem mass_valid (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E) :
    IsDist (priorSignalMass μ E) :=
  priorSignalMass_isDist μ E hE (likelihood_integrable μ E hE)

theorem potential_bounds (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E) :
    0 ≤ potential μ E hE ∧ potential μ E hE ≤ 1 := by
  have hm := mass_valid μ E hE
  constructor
  · exact sum_nonneg fun s _ => mul_nonneg (hm.1 s) (posterior μ E hE s).potential_bounds.1
  · calc
      potential μ E hE ≤ ∑ s, priorSignalMass μ E s * 1 :=
        sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
          (posterior μ E hE s).potential_bounds.2 (hm.1 s)
      _ = 1 := by simpa using hm.2

def rulePayoff (E : FiniteExperiment Θ S) (q : S → FullLabelBrierReport Θ)
    (θ : Θ) : ℝ := ∑ s, E θ s * (q s).score θ

def ruleValue (E : FiniteExperiment Θ S) (q : S → FullLabelBrierReport Θ) : ℝ :=
  ∫ θ, rulePayoff E q θ ∂μ

theorem likelihood_score_integrable (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (s : S) (q : FullLabelBrierReport Θ) : Integrable (fun θ => E θ s * q.score θ) μ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  apply Eventually.of_forall
  intro θ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((hE θ).1 s)]
  calc E θ s * |q.score θ| ≤ E θ s * 1 :=
        mul_le_mul_of_nonneg_left (abs_le.mpr (q.score_bounds θ)) ((hE θ).1 s)
    _ ≤ 1 := by
      simpa using (single_le_sum (fun x _ => (hE θ).1 x) (mem_univ s)).trans_eq (hE θ).2

theorem likelihood_score_posterior (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (s : S) (q : FullLabelBrierReport Θ) :
    (∫ θ, E θ s * q.score θ ∂μ) =
      priorSignalMass μ E s * (∑' θ, posterior μ E hE s θ * q.score θ) := by
  rw [integral_countable (likelihood_score_integrable μ E hE s q), ← tsum_mul_left]
  apply tsum_congr
  intro θ
  simp only [smul_eq_mul]
  conv_lhs => rw [← mul_assoc, ← mass_mul_posterior μ E hE s θ]
  ring

/-- Reporting the posterior is optimal, with exact squared-error regret. -/
theorem ruleValue_identity (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (q : S → FullLabelBrierReport Θ) :
    ruleValue μ E q = potential μ E hE -
      ∑ s, priorSignalMass μ E s * ∑' θ, (posterior μ E hE s θ - q s θ)^2 := by
  unfold ruleValue rulePayoff
  rw [integral_finsetSum _ (fun s _ => likelihood_score_integrable μ E hE s (q s))]
  simp_rw [likelihood_score_posterior μ E hE, FullLabelBrierReport.proper_identity, mul_sub]
  rw [sum_sub_distrib]
  rfl

theorem ruleValue_le_potential (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (q : S → FullLabelBrierReport Θ) : ruleValue μ E q ≤ potential μ E hE := by
  rw [ruleValue_identity μ E hE]
  exact sub_le_self _ (sum_nonneg fun s _ =>
    mul_nonneg ((mass_valid μ E hE).1 s) (tsum_nonneg fun θ => sq_nonneg _))

theorem posterior_value (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E) :
    ruleValue μ E (posterior μ E hE) = potential μ E hE := by
  rw [ruleValue_identity μ E hE]
  simp

theorem ruleValue_integrable (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (q : S → FullLabelBrierReport Θ) : Integrable (rulePayoff E q) μ :=
  integrable_finsetSum _ (fun s _ => likelihood_score_integrable μ E hE s (q s))

/-- Bounded scoring rules see average conditional TV, not only predictive mixtures. -/
theorem ruleValue_sub_le (E F : FiniteExperiment Θ S)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (q : S → FullLabelBrierReport Θ) :
    ruleValue μ E q - ruleValue μ F q ≤ 2 * ∫ θ, finiteTV (E θ) (F θ) ∂μ := by
  have hiTV : Integrable (fun θ => finiteTV (E θ) (F θ)) μ := by
    apply (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
    exact Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (finiteTV_nonneg _ _)]
      exact finiteTV_le_one_of_isDist _ _ (hE θ) (hF θ)
  rw [ruleValue, ruleValue, ← integral_sub (ruleValue_integrable μ E hE q)
    (ruleValue_integrable μ F hF q), ← integral_const_mul]
  apply integral_mono ((ruleValue_integrable μ E hE q).sub (ruleValue_integrable μ F hF q))
    (hiTV.const_mul 2)
  intro θ
  calc rulePayoff E q θ - rulePayoff F q θ =
      ∑ s, (E θ s - F θ s) * (q s).score θ := by
        simp [rulePayoff, sub_mul, sum_sub_distrib]
    _ ≤ ∑ s, |E θ s - F θ s| := by
      apply sum_le_sum
      intro s _
      calc _ ≤ |(E θ s - F θ s) * (q s).score θ| := le_abs_self _
        _ = |E θ s - F θ s| * |(q s).score θ| := abs_mul _ _
        _ ≤ |E θ s - F θ s| := mul_le_of_le_one_right (abs_nonneg _)
          (abs_le.mpr ((q s).score_bounds θ))
    _ = 2 * finiteTV (E θ) (F θ) := by unfold finiteTV; ring

/-- Full countable Brier potential is 2-Lipschitz in prior-average row TV. -/
theorem potential_sub_le (E F : FiniteExperiment Θ S)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    potential μ E hE - potential μ F hF ≤ 2 * ∫ θ, finiteTV (E θ) (F θ) ∂μ := by
  have hb := ruleValue_sub_le μ E F hE hF (posterior μ E hE)
  rw [posterior_value] at hb
  have hl := ruleValue_le_potential μ F hF (posterior μ E hE)
  linarith

end
end IdExp.CountableBrier
