import Formal.CountableBrierCausal

/-! Complete ordinary Brier movement is the convergent series of actual
successive posterior squared distances on every countable world class. -/
namespace IdExp.CountableBrier
open MeasureTheory Finset Set Filter Topology
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1000000
variable {Θ A O : Type*} [Countable Θ] [MeasurableSpace Θ]
  [MeasurableSingletonClass Θ] [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  (μ : Measure Θ) [IsProbabilityMeasure μ] (ps : Θ → CausalBehavior A O)

abbrev record (π : ValidCausalPolicy A O) (n : ℕ) := causalBehaviorFiniteExperiment π.1 ps n

theorem record_valid (π : ValidCausalPolicy A O) (n : ℕ) : IsFiniteExperiment (record ps π n) :=
  causalBehaviorFiniteExperiment_valid π.1 π.2 ps n

def prefixPotential (π : ValidCausalPolicy A O) (n : ℕ) : ℝ :=
  potential μ (record ps π n) (record_valid ps π n)

/-- Every posterior world coordinate is included, with no feature weights. -/
def expectedMovement (π : ValidCausalPolicy A O) (n : ℕ) : ℝ :=
  ∑ w, priorSignalMass μ (record ps π (n+1)) w * ∑' θ,
    (posterior μ (record ps π (n+1)) (record_valid ps π (n+1)) w θ -
      posterior μ (record ps π n) (record_valid ps π n) (Fin.init w) θ)^2

theorem expectedMovement_nonneg (π : ValidCausalPolicy A O) (n : ℕ) :
    0 ≤ expectedMovement μ ps π n :=
  sum_nonneg fun w _ => mul_nonneg ((mass_valid μ _ (record_valid ps π (n+1))).1 w)
    (tsum_nonneg fun _ => sq_nonneg _)

/-- Exact Pythagoras for successive literal policy-history posteriors. -/
theorem expectedMovement_eq (π : ValidCausalPolicy A O) (n : ℕ) :
    expectedMovement μ ps π n = prefixPotential μ ps π (n+1) - prefixPotential μ ps π n := by
  classical
  have hp := causalBehaviorFiniteExperiment_prefix π.1 π.2 ps n
  change finiteDecisionLaw (record ps π (n+1)) (causalPrefixRule n) = record ps π n at hp
  have hm := movement_eq μ (record ps π (n+1)) (record_valid ps π (n+1))
    (causalPrefixRule n) (causalPrefixRule_mem_stochasticRules n)
  have he : movement μ (record ps π (n+1)) (record_valid ps π (n+1))
      (causalPrefixRule n) (causalPrefixRule_mem_stochasticRules n) = expectedMovement μ ps π n := by
    unfold movement expectedMovement
    simp only [hp]
    apply sum_congr rfl
    intro w _
    simp [joint, causalPrefixRule]
  rw [he] at hm
  simpa only [hp, prefixPotential] using hm

theorem prefixPotential_zero (π : ValidCausalPolicy A O) :
    prefixPotential μ ps π 0 = (FullLabelBrierReport.ofMeasure μ).potential := by
  have hzero (θ : Θ) (w : CausalFiniteTrace A O 0) : record ps π 0 θ w = 1 := by
    simp [record, causalBehaviorFiniteExperiment, causalBehaviorTraceProb,
      causalPolicyProb, causalPolicyProbFrom]
  have hm (w : CausalFiniteTrace A O 0) : priorSignalMass μ (record ps π 0) w = 1 := by
    simp [priorSignalMass, hzero]
  have hp (w : CausalFiniteTrace A O 0) (θ : Θ) :
      posterior μ (record ps π 0) (record_valid ps π 0) w θ = μ.real {θ} := by
    rw [posterior_apply]
    simp [priorSignalDensity, hm, hzero]
  have hpot (w : CausalFiniteTrace A O 0) :
      (posterior μ (record ps π 0) (record_valid ps π 0) w).potential =
        (FullLabelBrierReport.ofMeasure μ).potential := by
    unfold FullLabelBrierReport.potential
    apply tsum_congr
    intro θ
    rw [hp]
    rfl
  simp [prefixPotential, potential, hm, hpot]

theorem prefixPotential_monotone (π : ValidCausalPolicy A O) :
    Monotone (prefixPotential μ ps π) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := expectedMovement_nonneg μ ps π n
  rw [expectedMovement_eq] at h
  linarith

theorem finite_movement_telescope (π : ValidCausalPolicy A O) (N : ℕ) :
    (∑ n ∈ range N, expectedMovement μ ps π n) =
      prefixPotential μ ps π N - (FullLabelBrierReport.ofMeasure μ).potential := by
  induction N with
  | zero => simp [prefixPotential_zero]
  | succ N ih =>
    rw [sum_range_succ, ih, expectedMovement_eq]
    ring

theorem totalPotential_toReal (π : ValidCausalPolicy A O) :
    (causalTotalPotential μ ps π).toReal = ⨆ n, prefixPotential μ ps π n := by
  unfold causalTotalPotential
  rw [ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top)]
  congr 1
  funext n
  exact ENNReal.toReal_ofReal (potential_bounds μ _ (record_valid ps π n)).1

/-- The literal nonnegative posterior-movement series converges to the complete gain. -/
theorem expectedMovement_hasSum (π : ValidCausalPolicy A O) :
    HasSum (expectedMovement μ ps π) (causalCompleteGain μ ps π) := by
  have hb : BddAbove (range (prefixPotential μ ps π)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (potential_bounds μ _ (record_valid ps π n)).2
  have ht := tendsto_atTop_ciSup (prefixPotential_monotone μ ps π) hb
  apply (hasSum_iff_tendsto_nat_of_nonneg (expectedMovement_nonneg μ ps π) _).2
  simpa only [finite_movement_telescope, causalCompleteGain, totalPotential_toReal] using
    ht.sub_const (FullLabelBrierReport.ofMeasure μ).potential

/-- No divergent sum is hidden by a real supremum convention. -/
theorem expectedMovement_tsum (π : ValidCausalPolicy A O) :
    (∑' n, expectedMovement μ ps π n) = causalCompleteGain μ ps π :=
  (expectedMovement_hasSum μ ps π).tsum_eq

end
end IdExp.CountableBrier
