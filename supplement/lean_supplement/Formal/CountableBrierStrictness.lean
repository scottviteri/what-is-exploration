import Formal.CountableBrierReverse
import Formal.AverageFiniteExperimentScore

/-! Complete countable Brier equals reverse-average capability, not necessarily
uniform capability. Boundedness removes infinity saturation automatically. -/
namespace IdExp.CountableBrier
open MeasureTheory Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1000000
variable {Θ P : Type*} [Countable Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  {S : ℕ → Type*} [∀ n, Fintype (S n)] [∀ n, Nonempty (S n)]
  (μ : Measure Θ) [IsProbabilityMeasure μ]

/-- The generic finite-record score premises hold for the actual countable Brier potential. -/
def finiteScore : AverageFiniteExperimentScore Θ S μ where
  value E := potential μ E.2.1 E.2.2.1
  nonneg E := (potential_bounds μ E.2.1 E.2.2.1).1
  data_processing := by
    intro E F ⟨G, hG, he⟩
    have h := potential_mono_garbling μ E.2.1 E.2.2.1 G hG
    simpa only [he] using h
  continuous_output := by
    intro n η hη
    refine ⟨η/2, half_pos hη, ?_⟩
    intro E F hdist
    apply abs_lt.mpr
    have he := potential_sub_le μ E.1 F.1 E.2.1 F.2.1
    have hf := potential_sub_le μ F.1 E.1 F.2.1 E.2.1
    have hs : (∫ θ, finiteTV (F.1 θ) (E.1 θ) ∂μ) =
        ∫ θ, finiteTV (E.1 θ) (F.1 θ) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun θ => finiteTV_symm _ _
    rw [hs] at hf
    constructor <;> change _ < _ <;> linarith

theorem fixed_target_cost (M : MeasurableFiniteProcess Θ P S) :
    (finiteScore (S := S) μ).toScoreExperimentSystem.HasFixedTargetCost
      (AverageFiniteExperimentScore.records M) := by
  intro π n ε hε
  obtain ⟨η, hη, hrev⟩ := vanishing_reverse_modulus μ ε hε
  refine ⟨η, hη, ?_⟩
  intro E H htarget hgarble hfar
  change η ≤ potential μ E.2.1 E.2.2.1 - potential μ H.2.1 H.2.2.1
  by_contra hn
  have hsmall := lt_of_not_ge hn
  obtain ⟨G, hG, he⟩ := hgarble
  have hr : priorAverageDeficiency μ H.2.1 E.2.1 < ε := by
    have hloss : potential μ E.2.1 E.2.2.1 -
        potential μ (finiteDecisionLaw E.2.1 G) (finiteDecisionLaw_valid _ E.2.2.1 G hG) < η := by
      simpa only [he] using hsmall
    simpa only [he] using hrev E.2.1 E.2.2.1 G hG hloss
  have hz := priorAverageDeficiency_eq_zero_of_blackwell μ E.2.1 (M.experiment π n) htarget
  have ht := priorAverageDeficiency_triangle μ H.2.1 E.2.1 (M.experiment π n)
    H.2.2.1 E.2.2.1 (M.valid π n) H.2.2.2 E.2.2.2 (M.measurable π n)
  rw [hz, add_zero] at ht
  change ε ≤ priorAverageDeficiency μ H.2.1 (M.experiment π n) at hfar
  linarith

/-- Supremum of actual expected squared posterior norms on retained prefixes. -/
def totalPotential (M : MeasurableFiniteProcess Θ P S) (π : P) : ℝ≥0∞ :=
  ⨆ n, ENNReal.ofReal (potential μ (M.experiment π n) (M.valid π n))

theorem score_bounded (M : MeasurableFiniteProcess Θ P S) (π : P) :
    (finiteScore (S := S) μ).toScoreExperimentSystem.ScoreBounded
      (AverageFiniteExperimentScore.records M) π := by
  refine ⟨1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (potential_bounds μ (M.experiment π n) (M.valid π n)).2

theorem totalPotential_le_one (M : MeasurableFiniteProcess Θ P S) (π : P) :
    totalPotential μ M π ≤ 1 := by
  apply iSup_le
  intro n
  simpa using ENNReal.ofReal_le_ofReal (potential_bounds μ (M.experiment π n) (M.valid π n)).2

theorem totalPotential_mono (M : MeasurableFiniteProcess Θ P S) {π ρ : P}
    (h : M.AverageDominates μ π ρ) : totalPotential μ M ρ ≤ totalPotential μ M π :=
  (finiteScore (S := S) μ).toScoreExperimentSystem.totalScore_mono
    (AverageFiniteExperimentScore.records M) h

/-- Equality characterizes reverse average finitary recovery, with no finite-entropy premise. -/
theorem totalPotential_eq_iff_reverse (M : MeasurableFiniteProcess Θ P S) {π ρ : P}
    (h : M.AverageDominates μ π ρ) :
    totalPotential μ M π = totalPotential μ M ρ ↔ M.AverageDominates μ ρ π :=
  (finiteScore (S := S) μ).totalScore_eq_iff_reverse_average M (fixed_target_cost μ M)
    (ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) (totalPotential_le_one μ M π)) h

/-- The only remaining obstruction is failure to lift reverse average recovery to uniform recovery. -/
theorem totalPotential_uniform_strictness_iff [Nonempty Θ]
    (M : MeasurableFiniteProcess Θ P S) :
    StrictlyMonotoneFor M.UniformDominates (totalPotential μ M) ↔
      ReverseDominanceLifts M.UniformDominates (M.AverageDominates μ) :=
  (finiteScore (S := S) μ).toScoreExperimentSystem.totalScore_strictness_iff_of_finite
    (AverageFiniteExperimentScore.records M) ((finiteScore μ).records_refines M)
    (fixed_target_cost μ M) (score_bounded μ M) M.UniformDominates
    (fun _ _ h => M.averageDominates_of_uniform μ h)

end
end IdExp.CountableBrier
