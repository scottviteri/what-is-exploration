import Formal.ScoreExperimentSystem
import Formal.FinitaryInformationEquality

/-!
# Actual prior-average finite-experiment score systems

The generic calculus is instantiated by measurable stochastic experiments and
world-independent randomized matrices. The infimum over decoders is retained;
neither decoder attainment nor a finite world class is assumed.
-/
namespace IdExp
open MeasureTheory Set
open scoped ENNReal
noncomputable section

abbrev IndexedMeasurableFiniteExperiment (Θ : Type*) [MeasurableSpace Θ]
    (S : ℕ → Type*) [∀ n, Fintype (S n)] :=
  Σ n, {E : FiniteExperiment Θ (S n) //
    IsFiniteExperiment E ∧ ∀ x, Measurable (fun θ => E θ x)}

variable {Θ : Type*} [MeasurableSpace Θ] {S : ℕ → Type*}
  [∀ n, Fintype (S n)] [∀ n, Nonempty (S n)]

/-- The fixed-output score continuity needed by the process theorem. Its
modulus is allowed to depend on the output alphabet, not on the source. -/
structure AverageFiniteExperimentScore (Θ : Type*) [MeasurableSpace Θ]
    (S : ℕ → Type*) [∀ n, Fintype (S n)] (μ : Measure Θ) where
  value : IndexedMeasurableFiniteExperiment Θ S → ℝ
  nonneg : ∀ E, 0 ≤ value E
  data_processing : ∀ E F, FiniteBlackwellLE F.2.1 E.2.1 → value F ≤ value E
  continuous_output : ∀ n η, 0 < η → ∃ δ, 0 < δ ∧
    ∀ (E F : {E : FiniteExperiment Θ (S n) //
      IsFiniteExperiment E ∧ ∀ x, Measurable (fun θ => E θ x)}),
      (∫ θ, finiteTV (E.1 θ) (F.1 θ) ∂μ) < δ →
        |value ⟨n, E⟩ - value ⟨n, F⟩| < η

namespace AverageFiniteExperimentScore
variable {μ : Measure Θ} [IsProbabilityMeasure μ]
  (SCORE : AverageFiniteExperimentScore Θ S μ)

/-- Actual average row-TV decoder deficiency and exact Blackwell garbling. -/
def toScoreExperimentSystem : ScoreExperimentSystem (IndexedMeasurableFiniteExperiment Θ S) where
  deficiency E F := priorAverageDeficiency μ E.2.1 F.2.1
  score := SCORE.value
  exact E F := FiniteBlackwellLE F.2.1 E.2.1
  score_nonneg := SCORE.nonneg
  score_exact_le := fun {E F} h => SCORE.data_processing E F h
  deficiency_nonneg E F := priorAverageDeficiency_nonneg μ E.2.1 F.2.1
  deficiency_triangle E F T := priorAverageDeficiency_triangle μ _ _ _
    E.2.2.1 F.2.2.1 T.2.2.1 E.2.2.2 F.2.2.2 T.2.2.2
  deficiency_exact_zero := fun {E F} h => priorAverageDeficiency_eq_zero_of_blackwell μ _ _ h
  approximation := by
    intro F η hη r hr
    obtain ⟨δ, hδ, hc⟩ := SCORE.continuous_output F.1 η hη
    refine ⟨min δ r, lt_min hδ hr, ?_⟩
    intro E he
    obtain ⟨G, hG, hg⟩ := exists_decoder_lt_of_priorAverageDeficiency_lt μ E.2.1 F.2.1 he
    let H : {H : FiniteExperiment Θ (S F.1) //
        IsFiniteExperiment H ∧ ∀ x, Measurable (fun θ => H θ x)} :=
      ⟨finiteDecisionLaw E.2.1 G, finiteDecisionLaw_valid _ E.2.2.1 G hG,
        measurable_finiteDecisionLaw _ E.2.2.2 G⟩
    refine ⟨⟨F.1, H⟩, ⟨G, hG, rfl⟩, ?_, ?_⟩
    · have hi := priorAverageDeficiency_le_integral_rowTV μ F.2.1 H.1
      have hs : (∫ θ, finiteTV (F.2.1 θ) (H.1 θ) ∂μ) =
          priorAverageDecodeErr μ E.2.1 F.2.1 G := by
        apply integral_congr_ae
        filter_upwards [] with θ
        simp only [H, decodeErr, finiteTV, finiteDecisionLaw, abs_sub_comm]
      rw [hs] at hi
      exact hi.trans_lt (hg.trans_le (min_le_right _ _))
    · exact hc H F.2 (hg.trans_le (min_le_left _ _))

/-- An arbitrary actual growing measurable process, with its original rows. -/
def records {P : Type*} (M : MeasurableFiniteProcess Θ P S) (π : P) (n : ℕ) :
    IndexedMeasurableFiniteExperiment Θ S :=
  ⟨n, M.experiment π n, M.valid π n, M.measurable π n⟩

theorem records_refines {P : Type*} (M : MeasurableFiniteProcess Θ P S) :
    SCORE.toScoreExperimentSystem.Refines (records M) := M.refines

@[simp] theorem dominates_records_iff {P : Type*} (M : MeasurableFiniteProcess Θ P S)
    (π ρ : P) :
    SCORE.toScoreExperimentSystem.Dominates (records M) π ρ ↔ M.AverageDominates μ π ρ := Iff.rfl

/-- Finite-total equality for literal average simulation of growing records. -/
theorem totalScore_eq_iff_reverse_average {P : Type*} (M : MeasurableFiniteProcess Θ P S)
    (hc : SCORE.toScoreExperimentSystem.HasFixedTargetCost (records M))
    {π ρ : P} (hb : SCORE.toScoreExperimentSystem.totalScore (records M) π ≠ ⊤)
    (h : M.AverageDominates μ π ρ) :
    SCORE.toScoreExperimentSystem.totalScore (records M) π =
      SCORE.toScoreExperimentSystem.totalScore (records M) ρ ↔ M.AverageDominates μ ρ π :=
  SCORE.toScoreExperimentSystem.totalScore_eq_iff_reverse (records M)
    (SCORE.records_refines M) hc hb h

/-- Exact uniform strictness test for scores continuous in average row-TV.
The conclusion concerns actual uniform deficiency, not predictive-mixture TV. -/
theorem totalScore_uniform_strictness_iff [Nonempty Θ] {P : Type*}
    (M : MeasurableFiniteProcess Θ P S)
    (hc : SCORE.toScoreExperimentSystem.HasFixedTargetCost (records M)) :
    StrictlyMonotoneFor M.UniformDominates (SCORE.toScoreExperimentSystem.totalScore (records M)) ↔
      ReverseDominanceLifts M.UniformDominates (M.AverageDominates μ) ∧
        NoInfiniteStrictPairFor M.UniformDominates
          (SCORE.toScoreExperimentSystem.totalScore (records M)) :=
  SCORE.toScoreExperimentSystem.totalScore_strictness_iff (records M)
    (SCORE.records_refines M) hc M.UniformDominates
    (fun _ _ h => M.averageDominates_of_uniform μ h)

end AverageFiniteExperimentScore
end
end IdExp
