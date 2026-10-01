import Formal.CountableBrierScore

/-! Exact countable-posterior squared movement under a finite garbling. -/
namespace IdExp.CountableBrier
open MeasureTheory Finset Set Filter Topology
noncomputable section
set_option maxHeartbeats 1000000
variable {Θ S T : Type*} [Countable Θ] [MeasurableSpace Θ]
  [MeasurableSingletonClass Θ] [Fintype S] [Fintype T]
variable (μ : Measure Θ) [IsProbabilityMeasure μ]

def joint (E : FiniteExperiment Θ S) (G : S → T → ℝ) (s : S) (t : T) : ℝ :=
  priorSignalMass μ E s * G s t

theorem joint_nonneg (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (s : S) (t : T) :
    0 ≤ joint μ E G s t :=
  mul_nonneg ((mass_valid μ E hE).1 s) ((hG s (mem_univ s)).1 t)

theorem sum_joint_right (E : FiniteExperiment Θ S)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (s : S) :
    ∑ t, joint μ E G s t = priorSignalMass μ E s := by
  unfold joint
  rw [← mul_sum, (hG s (mem_univ s)).2, mul_one]

theorem sum_joint_left (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (G : S → T → ℝ) (t : T) :
    ∑ s, joint μ E G s t = priorSignalMass μ (finiteDecisionLaw E G) t :=
  priorSignalMass_garbling μ E _ (likelihood_integrable μ E hE) G rfl t

theorem sum_joint (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) :
    ∑ s, ∑ t, joint μ E G s t = 1 := by
  simp_rw [sum_joint_right μ E G hG]
  exact (mass_valid μ E hE).2

theorem ruleValue_garbling_identity (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T)
    (q : T → FullLabelBrierReport Θ) :
    ruleValue μ (finiteDecisionLaw E G) q = potential μ E hE -
      ∑ s, ∑ t, joint μ E G s t * ∑' θ, (posterior μ E hE s θ - q t θ)^2 := by
  have he : ruleValue μ (finiteDecisionLaw E G) q =
      ∑ s, ∑ t, G s t * (∫ θ, E θ s * (q t).score θ ∂μ) := by
    have hi (s : S) (t : T) : Integrable (fun θ => E θ s * G s t * (q t).score θ) μ :=
      ((likelihood_score_integrable μ E hE s (q t)).const_mul (G s t)).congr
        (Eventually.of_forall fun θ => by ring)
    unfold ruleValue rulePayoff finiteDecisionLaw
    simp_rw [sum_mul]
    rw [integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun s _ => hi s t))]
    have hi2 (t : T) : (∫ θ, ∑ s, E θ s * G s t * (q t).score θ ∂μ) =
        ∑ s, ∫ θ, E θ s * G s t * (q t).score θ ∂μ :=
      integral_finsetSum _ (fun s _ => hi s t)
    simp_rw [hi2]
    rw [sum_comm]
    apply sum_congr rfl
    intro s _
    apply sum_congr rfl
    intro t _
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun θ => by ring
  rw [he]
  simp_rw [likelihood_score_posterior μ E hE, FullLabelBrierReport.proper_identity]
  have hs (s : S) (t : T) :
      G s t * (priorSignalMass μ E s * ((posterior μ E hE s).potential -
        ∑' θ, (posterior μ E hE s θ - q t θ)^2)) =
      joint μ E G s t * (posterior μ E hE s).potential -
        joint μ E G s t * ∑' θ, (posterior μ E hE s θ - q t θ)^2 := by
    unfold joint
    ring
  simp_rw [hs, sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro s _
  rw [← sum_mul, sum_joint_right μ E G hG]

def movement (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) : ℝ :=
  ∑ s, ∑ t, joint μ E G s t * ∑' θ,
    (posterior μ E hE s θ - posterior μ (finiteDecisionLaw E G)
      (finiteDecisionLaw_valid E hE G hG) t θ)^2

/-- Countable-posterior Pythagoras, with all coordinates and arbitrary stochastic garbling. -/
theorem movement_eq (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) :
    movement μ E hE G hG = potential μ E hE -
      potential μ (finiteDecisionLaw E G) (finiteDecisionLaw_valid E hE G hG) := by
  have h := ruleValue_garbling_identity μ E hE G hG
    (posterior μ (finiteDecisionLaw E G) (finiteDecisionLaw_valid E hE G hG))
  rw [posterior_value] at h
  change _ = _ - movement μ E hE G hG at h
  linarith

theorem movement_nonneg (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) : 0 ≤ movement μ E hE G hG :=
  sum_nonneg fun s _ => sum_nonneg fun t _ =>
    mul_nonneg (joint_nonneg μ E hE G hG s t) (tsum_nonneg fun θ => sq_nonneg _)

/-- Data processing for the ordinary countable full-label Brier score. -/
theorem potential_mono_garbling (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) :
    potential μ (finiteDecisionLaw E G) (finiteDecisionLaw_valid E hE G hG) ≤ potential μ E hE := by
  have h := movement_nonneg μ E hE G hG
  rw [movement_eq] at h
  linarith

end
end IdExp.CountableBrier
