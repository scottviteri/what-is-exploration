import Formal.AlarmPanelNativeAudit
import Formal.AlarmPanelPosteriorCore
import Formal.CausalPartialExecution

/-! Exact finite-horizon posterior positive controls on the actual alarm/panel
histories. The countable geometric prior has positive mass at every world. -/
noncomputable section
namespace IdExp.AlarmPanel
open MeasureTheory Finset Set
open PulseBrierScore (prior prior_positive_atoms posteriorPotential)

 theorem no_reverse_of_inspectionProbability_lt_one
    (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) (hs : inspectionProbability π < 1) :
    ¬ FiniteBlackwellLE (experiment inspectPolicy (n+1)) (experiment π (n+1)) := by
  intro hr
  have hp : FiniteBlackwellLE (experiment inspectPolicy 1) (experiment inspectPolicy (n+1)) :=
    causalFiniteExperiment_prefix_blackwell_of_le inspectPolicy inspectPolicy_valid response response_valid (by omega)
  have hz := finiteDeficiency_eq_zero_of_blackwellLE _ _ (experiment_valid π hπ _)
    (experiment_valid inspectPolicy inspectPolicy_valid 1) (finiteBlackwellLE_trans hp hr)
  rw [inspection_deficiency_exact π hπ n] at hz
  linarith

local instance : TopologicalSpace World := ⊥
local instance : DiscreteTopology World := ⟨rfl⟩
local instance : OpensMeasurableSpace World := ⟨fun s _ => Set.Countable.measurableSet (Set.to_countable s)⟩

local instance prior_openPos : prior.IsOpenPosMeasure where
  open_pos U _ hn := by
    obtain ⟨θ,hθ⟩ := hn
    exact ne_of_gt ((prior_positive_atoms θ).trans_le (measure_mono (singleton_subset_iff.mpr hθ)))

 theorem finiteInformation_strict (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) (hs : inspectionProbability π < 1) :
    AlarmPanelPosterior.prefixInformation ⟨π,hπ⟩ (n+1) <
      AlarmPanelPosterior.prefixInformation ⟨inspectPolicy,inspectPolicy_valid⟩ (n+1) := by
  obtain ⟨G,hG,he⟩ := inspection_same_horizon_blackwell π hπ n
  exact continuous_infinitePriorInformation_lt_of_no_reverse prior _ _
    (experiment_valid inspectPolicy inspectPolicy_valid _) (experiment_valid π hπ _)
    (fun _ => continuous_of_discreteTopology) (fun _ => continuous_of_discreteTopology)
    G hG he (no_reverse_of_inspectionProbability_lt_one π hπ n hs)

 theorem finiteInformation_le (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) :
    AlarmPanelPosterior.prefixInformation ⟨π,hπ⟩ (n+1) ≤
      AlarmPanelPosterior.prefixInformation ⟨inspectPolicy,inspectPolicy_valid⟩ (n+1) := by
  obtain ⟨G,hG,he⟩ := inspection_same_horizon_blackwell π hπ n
  have hm := infinitePriorInformation_mono_garbling prior _
    (experiment_valid inspectPolicy inspectPolicy_valid _) (fun _ => measurable_of_countable _) G hG
  rw [he] at hm
  exact hm

 theorem finiteInformation_eq_iff (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) :
    AlarmPanelPosterior.prefixInformation ⟨π,hπ⟩ (n+1) =
      AlarmPanelPosterior.prefixInformation ⟨inspectPolicy,inspectPolicy_valid⟩ (n+1) ↔
      inspectionProbability π = 1 := by
  constructor
  · intro he
    by_contra hs
    have hlt := finiteInformation_strict π hπ n
      (lt_of_le_of_ne (inspectionProbability_le_one π hπ) hs)
    linarith
  · intro hs
    apply le_antisymm (finiteInformation_le π hπ n)
    obtain ⟨G,hG,he⟩ := alwaysInspect_blackwell π inspectPolicy hπ inspectPolicy_valid (n+1) n le_rfl hs
    have hm := infinitePriorInformation_mono_garbling prior _
      (experiment_valid π hπ _) (fun _ => measurable_of_countable _) G hG
    rw [he] at hm
    exact hm


/-- Ordinary full-label Brier as a posterior-density potential. The extra
prior-atom factor is essential: this is not unweighted squared density. -/
 def densityBrierPotential (f : World → ℝ) : ℝ :=
   ∫ θ, prior.real {θ} * (f θ)^2 ∂prior

 theorem integrable_weighted_square {f : World → ℝ}
    (hf : f ∈ boundedContinuousDensityDomain) :
    Integrable (fun θ => prior.real {θ} * (f θ)^2) prior := by
  obtain ⟨hc,M,hM,hbound⟩ := hf
  apply (integrable_const (M^2)).mono' (measurable_of_countable _).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro θ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg measureReal_nonneg (sq_nonneg _))]
  calc
    prior.real {θ} * (f θ)^2 ≤ (f θ)^2 :=
      mul_le_of_le_one_left (sq_nonneg _) measureReal_le_one
    _ ≤ M^2 := pow_le_pow_left₀ (hbound θ).1 (hbound θ).2 2

 theorem strictConvexOn_densityBrierPotential :
    StrictConvexOn ℝ boundedContinuousDensityDomain densityBrierPotential := by
  refine ⟨convex_boundedContinuousDensityDomain, ?_⟩
  intro f hf g hg hne a b ha hb hab
  obtain ⟨θ,hθ⟩ := Function.ne_iff.mp hne
  let k : World → ℝ := a • f + b • g
  have hk : k ∈ boundedContinuousDensityDomain :=
    convex_boundedContinuousDensityDomain hf hg ha.le hb.le hab
  let d : World → ℝ := fun z => a*(prior.real {z}*(f z)^2) +
    b*(prior.real {z}*(g z)^2) - prior.real {z}*(k z)^2
  have hd (z : World) : d z = prior.real {z}*a*b*(f z-g z)^2 := by
    have he : b = 1-a := by linarith
    simp only [d,k,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [he]
    ring
  have hdint : Integrable d prior :=
    (((integrable_weighted_square hf).const_mul a).add
      ((integrable_weighted_square hg).const_mul b)).sub (integrable_weighted_square hk)
  have hdnonneg : 0 ≤ d := by
    intro z
    rw [hd]
    positivity
  have hdpos : 0 < d θ := by
    rw [hd]
    exact mul_pos (mul_pos (mul_pos (PulseInformation.mass_pos θ) ha) hb)
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hθ))
  have hp := integral_pos_of_integrable_nonneg_nonzero
    (show Continuous d from continuous_of_discreteTopology) hdint hdnonneg (ne_of_gt hdpos)
  have hi := integral_sub (((integrable_weighted_square hf).const_mul a).add
      ((integrable_weighted_square hg).const_mul b)) (integrable_weighted_square hk)
  have hiadd := integral_add ((integrable_weighted_square hf).const_mul a)
    ((integrable_weighted_square hg).const_mul b)
  dsimp [d] at hp
  simp only [Pi.add_apply] at hi hiadd
  rw [hi,hiadd,integral_const_mul,integral_const_mul] at hp
  exact sub_pos.mp hp

 theorem densityBrier_eq_posteriorPotential {X : Type*} [Fintype X]
    (E : FiniteExperiment World X) (hE : IsFiniteExperiment E) :
    priorSignalPotential prior E densityBrierPotential = posteriorPotential E hE := by
  unfold priorSignalPotential posteriorPotential
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  unfold densityBrierPotential FullLabelBrierReport.potential
  rw [integral_countable (integrable_weighted_square
    (priorSignalDensity_mem_boundedContinuousDensityDomain prior E hE
      (fun _ => continuous_of_discreteTopology) x))]
  apply tsum_congr
  intro θ
  rw [PulseBrierScore.posteriorReport_apply]
  simp only [smul_eq_mul]
  ring

 theorem finiteBrier_strict (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) (hs : inspectionProbability π < 1) :
    AlarmPanelPosterior.prefixPotential ⟨π,hπ⟩ (n+1) <
      AlarmPanelPosterior.prefixPotential ⟨inspectPolicy,inspectPolicy_valid⟩ (n+1) := by
  obtain ⟨G,hG,he⟩ := inspection_same_horizon_blackwell π hπ n
  have h := continuous_priorSignalPotential_lt_of_no_reverse prior _ _
    (experiment_valid inspectPolicy inspectPolicy_valid _) (experiment_valid π hπ _)
    (fun _ => continuous_of_discreteTopology) (fun _ => continuous_of_discreteTopology)
    G hG he densityBrierPotential boundedContinuousDensityDomain
    strictConvexOn_densityBrierPotential
    (priorSignalDensity_mem_boundedContinuousDensityDomain prior _
      (experiment_valid inspectPolicy inspectPolicy_valid _) (fun _ => continuous_of_discreteTopology))
    (no_reverse_of_inspectionProbability_lt_one π hπ n hs)
  rw [densityBrier_eq_posteriorPotential _ (experiment_valid π hπ _),
    densityBrier_eq_posteriorPotential _ (experiment_valid inspectPolicy inspectPolicy_valid _)] at h
  exact h


 theorem brier_mono_blackwell {X Y : Type*} [Fintype X] [Fintype Y]
    (E : FiniteExperiment World X) (F : FiniteExperiment World Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hFE : FiniteBlackwellLE F E) : posteriorPotential F hF ≤ posteriorPotential E hE := by
  obtain ⟨G,hG,he⟩ := hFE
  let P := priorSignalSystem prior E hE (PulseBrierScore.likelihood_integrable E hE)
    (priorSignalMass_zero_of_positive_atoms prior prior_positive_atoms E hE
      (PulseBrierScore.likelihood_integrable E hE))
  let Q := priorSignalSystem prior F hF (PulseBrierScore.likelihood_integrable F hF)
    (priorSignalMass_zero_of_positive_atoms prior prior_positive_atoms F hF
      (PulseBrierScore.likelihood_integrable F hF))
  have hm := signalPosterior_potential_mono P Q G hG he
    (priorSignalMass_garbling prior E F (PulseBrierScore.likelihood_integrable E hE) G he)
    densityBrierPotential boundedContinuousDensityDomain strictConvexOn_densityBrierPotential.convexOn
    (priorSignalDensity_mem_boundedContinuousDensityDomain prior E hE (fun _ => continuous_of_discreteTopology))
  change priorSignalPotential prior F densityBrierPotential ≤ priorSignalPotential prior E densityBrierPotential at hm
  rwa [densityBrier_eq_posteriorPotential E hE, densityBrier_eq_posteriorPotential F hF] at hm

 theorem finiteBrier_le (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) :
    AlarmPanelPosterior.prefixPotential ⟨π,hπ⟩ (n+1) ≤
      AlarmPanelPosterior.prefixPotential ⟨inspectPolicy,inspectPolicy_valid⟩ (n+1) :=
  brier_mono_blackwell _ _ (experiment_valid inspectPolicy inspectPolicy_valid _)
    (experiment_valid π hπ _) (inspection_same_horizon_blackwell π hπ n)

 theorem finiteBrier_eq_iff (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) :
    AlarmPanelPosterior.prefixPotential ⟨π,hπ⟩ (n+1) =
      AlarmPanelPosterior.prefixPotential ⟨inspectPolicy,inspectPolicy_valid⟩ (n+1) ↔
      inspectionProbability π = 1 := by
  constructor
  · intro he
    by_contra hs
    have hlt := finiteBrier_strict π hπ n
      (lt_of_le_of_ne (inspectionProbability_le_one π hπ) hs)
    linarith
  · intro hs
    apply le_antisymm (finiteBrier_le π hπ n)
    exact brier_mono_blackwell _ _ (experiment_valid π hπ _)
      (experiment_valid inspectPolicy inspectPolicy_valid _)
      (alwaysInspect_blackwell π inspectPolicy hπ inspectPolicy_valid (n+1) n le_rfl hs)

/-- The summed ordinary Brier increments have exactly the same finite-horizon
maximizers, since the initial prior potential is policy-independent. -/
 theorem finiteMovement_eq_iff (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), AlarmPanelPosterior.expectedMovement ⟨π,hπ⟩ k) =
      (∑ k ∈ Finset.range (n+1), AlarmPanelPosterior.expectedMovement
        ⟨inspectPolicy,inspectPolicy_valid⟩ k) ↔ inspectionProbability π = 1 := by
  rw [AlarmPanelPosterior.finite_movement_telescope, AlarmPanelPosterior.finite_movement_telescope,
    sub_left_inj]
  exact finiteBrier_eq_iff π hπ n

end IdExp.AlarmPanel
