import Formal.PriorAverageDeficiency

/-! Information continuity and approximate reversal using prior-average errors.
All world classes are measurable; finite signals supply integrability. -/
namespace IdExp
open MeasureTheory Set Finset Filter Topology
noncomputable section
variable {Θ X Y : Type*} [MeasurableSpace Θ] [Fintype X] [Fintype Y]

/-- Finite-signal information is nonnegative without any prior support or topology. -/
theorem measurable_infinitePriorInformation_nonneg
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (hmE : ∀ x, Measurable (fun θ => E θ x)) :
    0 ≤ infinitePriorInformation μ E := by
  rw [infinitePriorInformation_eq_integral_finiteKL μ E hE hmE]
  apply integral_nonneg_of_ae
  filter_upwards [ae_priorSignalMass_support μ E hE hmE] with θ hθ
  have hp := priorSignalMass_isDist μ E hE
    (integrable_measurableFiniteExperiment_coordinate μ E hE hmE)
  have hb := finiteTV_sq_le_finiteKL_half (E θ) (priorSignalMass μ E) (hE θ) hp hθ
  change 0 ≤ finiteKL (E θ) (priorSignalMass μ E)
  nlinarith [sq_nonneg (finiteTV (E θ) (priorSignalMass μ E))]

variable [DecidableEq X]

theorem infinitePriorInformation_sub_le_fano_of_average_pos [Nonempty X]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (E F : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hmE : ∀ x, Measurable (fun θ => E θ x)) (hmF : ∀ x, Measurable (fun θ => F θ x))
    (r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1/2)
    (hTV : (∫ θ, finiteTV (E θ) (F θ) ∂μ) ≤ r) :
    infinitePriorInformation μ E - infinitePriorInformation μ F ≤ fanoModulus (Fintype.card X) r := by
  let J : FiniteExperiment Θ (X × X) := fun θ => finiteMaximalCoupling (E θ) (F θ)
  have hJ : IsFiniteExperiment J := fun θ => finiteMaximalCoupling_isDist _ _ (hE θ) (hF θ)
  have hmJ : ∀ z, Measurable (fun θ => J θ z) := measurable_finiteMaximalCoupling E F hmE hmF
  have he : finiteDecisionLaw J finiteFstRule = E := by
    funext θ x
    rw [finiteDecisionLaw_fst]
    exact finiteMaximalCoupling_fst _ _ (hE θ) (hF θ) x
  have hf : ∀ θ, finiteMarginalSnd (J θ) = F θ := fun θ =>
    funext fun x => finiteMaximalCoupling_snd _ _ (hE θ) (hF θ) x
  have hmono := infinitePriorInformation_mono_garbling μ J hJ hmJ finiteFstRule finiteFstRule_stochastic
  rw [he] at hmono
  have hmass : finiteMarginalSnd (priorSignalMass μ J) = priorSignalMass μ F := by
    funext x
    unfold finiteMarginalSnd priorSignalMass
    rw [← integral_finsetSum _ (fun y _ => integrable_measurableFiniteExperiment_coordinate μ J hJ hmJ (y,x))]
    apply integral_congr_ae
    filter_upwards [] with θ
    exact congrFun (hf θ) x
  have hmis : finiteMismatch (priorSignalMass μ J) ≤ r := by
    rw [← integral_finiteMismatch μ J hJ hmJ]
    have ht : (fun θ => finiteMismatch (J θ)) = (fun θ => finiteTV (E θ) (F θ)) :=
      funext fun θ => finiteMaximalCoupling_mismatch _ _ (hE θ) (hF θ)
    rw [ht]
    exact hTV
  have hbound := ent_sub_marginal_le_fano_pos (priorSignalMass μ J)
    (priorSignalMass_isDist μ J hJ (integrable_measurableFiniteExperiment_coordinate μ J hJ hmJ)) r hr hrhalf hmis
  rw [hmass] at hbound
  have hrow : ∀ θ, ent (F θ) ≤ ent (J θ) := fun θ => by
    rw [← hf θ]
    exact ent_marginal_snd_le _ (hJ θ).1
  have hi := integral_mono (integrable_finiteExperiment_ent μ F hF hmF)
    (integrable_finiteExperiment_ent μ J hJ hmJ) hrow
  rw [infinitePriorInformation_eq_ent_mass_sub μ J hJ hmJ] at hmono
  rw [infinitePriorInformation_eq_ent_mass_sub μ F hF hmF]
  unfold fanoModulus
  linarith


/-- A supplied approximate average simulator gives a quantitative reverse bound. -/
theorem priorAverageDeficiency_reverse_le [Nonempty X] [Nonempty Y]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ Y) (F : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hmE : ∀ y, Measurable (fun θ => E θ y))
    (hmF : ∀ x, Measurable (fun θ => F θ x))
    (G : Y → X → ℝ) (hG : G ∈ stochasticRules Y X)
    (r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1/2)
    (he : priorAverageDecodeErr μ E F G ≤ r) :
    priorAverageDeficiency μ F E ≤ r + Real.sqrt
      ((infinitePriorInformation μ E - infinitePriorInformation μ F +
        fanoModulus (Fintype.card X) r)/2) := by
  have hEG := finiteDecisionLaw_valid E hE G hG
  have hmEG := measurable_finiteDecisionLaw E hmE G
  have hc := infinitePriorInformation_sub_le_fano_of_average_pos μ F (finiteDecisionLaw E G)
    hF hEG hmF hmEG r hr hrhalf (by
      simpa only [priorAverageDecodeErr, decodeErr, finiteTV, finiteDecisionLaw, abs_sub_comm] using he)
  have hR := measurableBayesReverse_stochastic μ E hE hmE G hG
  have hrb := priorAverageDecodeErr_reverse_le_information_gap μ E hE hmE G hG
  have hf : priorAverageDeficiency μ F (finiteDecisionLaw E G) ≤ r := by
    apply (priorAverageDeficiency_le_integral_rowTV μ F (finiteDecisionLaw E G)).trans
    simpa only [priorAverageDecodeErr, decodeErr, finiteTV, finiteDecisionLaw, abs_sub_comm] using he
  have hb := priorAverageDeficiency_le_of_decoder μ (finiteDecisionLaw E G) E _ hR _ hrb
  have htri := priorAverageDeficiency_triangle μ F (finiteDecisionLaw E G) E
    hF hEG hE hmF hmEG hmE
  have hs : Real.sqrt ((infinitePriorInformation μ E -
        infinitePriorInformation μ (finiteDecisionLaw E G))/2) ≤
      Real.sqrt ((infinitePriorInformation μ E - infinitePriorInformation μ F +
        fanoModulus (Fintype.card X) r)/2) := Real.sqrt_le_sqrt (by linarith)
  linarith

end
end IdExp
