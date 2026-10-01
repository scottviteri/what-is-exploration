import Formal.PulsePriorEntropy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Complete finite-valued information gain on the countable pulse interface.
WAIT attains the finite prior entropy although QUERY strictly dominates it in
the finitary process order. Two dominated-convergence arguments connect actual
prefix likelihoods to their limit; terminal identification alone is not used as
an unproved entropy-limit bridge. -/
namespace IdExp.PulseInformation
open MeasureTheory Finset Set Filter Topology
open PulseBrierScore (World prior)
noncomputable section

def prefixInformation (π : ValidCausalPolicy Bool Bool) (t : ℕ) : ℝ :=
  infinitePriorInformation prior (causalBehaviorFiniteExperiment π.1 pulseBehavior t)

def completeInformation (π : ValidCausalPolicy Bool Bool) : ℝ :=
  sSup (Set.range (prefixInformation π))

theorem prefixInformation_le (π : ValidCausalPolicy Bool Bool) (t : ℕ) :
    prefixInformation π t ≤ 2 * Real.log 2 := by
  rw [← prior_entropy]
  exact information_le_atomic_entropy prior mass_pos surprisal_integrable _
    (causalBehaviorFiniteExperiment_valid π.1 π.2 pulseBehavior t)
    (fun _ => measurable_of_countable _)

theorem completeInformation_le (π : ValidCausalPolicy Bool Bool) :
    completeInformation π ≤ 2 * Real.log 2 :=
  csSup_le (Set.range_nonempty _) (by rintro _ ⟨t,rfl⟩; exact prefixInformation_le π t)

theorem wait_trace_eventually_separates (θ η : World) (hne : θ ≠ η) :
    ∀ᶠ t : ℕ in atTop, waitingQueryTrace t θ ≠ waitingQueryTrace t η := by
  cases θ with
  | some k =>
    filter_upwards [eventually_ge_atTop (k+2)] with t ht
    intro heq
    exact hne (waitingQueryTrace_detected_injective t k ht η heq).symm
  | none =>
    cases η with
    | none => exact False.elim (hne rfl)
    | some k =>
      filter_upwards [eventually_ge_atTop (k+2)] with t ht
      intro heq
      have h := waitingQueryTrace_detected_injective t k ht none heq.symm
      cases h

def waitMass (t : ℕ) (θ : World) : ℝ :=
  priorSignalMass prior (pulseExperiment false t) (waitingQueryTrace t θ)

theorem waitMass_tendsto (θ : World) :
    Tendsto (fun t => waitMass t θ) atTop (𝓝 (prior.real {θ})) := by
  classical
  have h := tendsto_integral_of_dominated_convergence (μ := prior)
    (F := fun t η => if waitingQueryTrace t η = waitingQueryTrace t θ then (1:ℝ) else 0)
    (f := fun η => if η = θ then (1:ℝ) else 0)
    (fun _ => (1:ℝ))
    (fun _ => (measurable_of_countable _).aestronglyMeasurable)
    (integrable_const _) (by
      intro t
      apply Eventually.of_forall
      intro η
      split_ifs <;> norm_num) (by
      apply Eventually.of_forall
      intro η
      by_cases he : η = θ
      · subst η; simp
      · apply tendsto_const_nhds.congr'
        filter_upwards [wait_trace_eventually_separates η θ he] with t ht
        simp [ht,he])
  have hi : (∫ η : World, (if η = θ then (1:ℝ) else 0) ∂prior) = prior.real {θ} := by
    have he : (fun η : World => if η = θ then (1:ℝ) else 0) =
        ({θ} : Set World).indicator (fun _ => (1:ℝ)) := by
      ext η
      by_cases he : η = θ <;> simp [he]
    rw [he, integral_indicator_const _ (measurableSet_singleton _)]
    simp
  rw [hi] at h
  have he (t : ℕ) : waitMass t θ = ∫ η : World,
      (if waitingQueryTrace t η = waitingQueryTrace t θ then (1:ℝ) else 0) ∂prior := by
    unfold waitMass priorSignalMass
    rw [pulseExperiment_wait, waitingQueryExperiment_eq_dirac]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro η
    by_cases ht : waitingQueryTrace t η = waitingQueryTrace t θ
    · simp [diracExp, ht]
    · simp [diracExp, ht, Ne.symm ht]
  simpa only [he] using h

theorem wait_finiteKL (t : ℕ) (θ : World) :
    finiteKL (pulseExperiment false t θ)
      (priorSignalMass prior (pulseExperiment false t)) = -Real.log (waitMass t θ) := by
  classical
  rw [pulseExperiment_wait, waitingQueryExperiment_eq_dirac]
  simp [finiteKL, diracExp, waitMass, pulseExperiment_wait,
    waitingQueryExperiment_eq_dirac, Real.log_inv]

theorem wait_information_tendsto :
    Tendsto (prefixInformation (pulsePolicy false)) atTop (𝓝 (2 * Real.log 2)) := by
  have h := tendsto_integral_of_dominated_convergence (μ := prior)
    (F := fun t θ => finiteKL (pulseExperiment false t θ)
      (priorSignalMass prior (pulseExperiment false t)))
    (f := surprisal) surprisal
    (fun _ => (measurable_of_countable _).aestronglyMeasurable)
    surprisal_integrable (by
      intro t
      apply Eventually.of_forall
      intro θ
      have hb := finiteKL_prior_bounds prior (pulseExperiment false t)
        (pulseExperiment_valid false t) (fun _ => measurable_of_countable _) θ (mass_pos θ)
      simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1, surprisal] using hb.2) (by
      apply Eventually.of_forall
      intro θ
      simp only [wait_finiteKL]
      exact ((waitMass_tendsto θ).log (mass_pos θ).ne').neg)
  rw [prior_entropy] at h
  have he (t : ℕ) : prefixInformation (pulsePolicy false) t =
      ∫ θ, finiteKL (pulseExperiment false t θ)
        (priorSignalMass prior (pulseExperiment false t)) ∂prior := by
    exact infinitePriorInformation_eq_integral_finiteKL prior (pulseExperiment false t)
      (pulseExperiment_valid false t) (fun _ => measurable_of_countable _)
  simpa only [← he] using h

theorem wait_completeInformation : completeInformation (pulsePolicy false) = 2 * Real.log 2 := by
  apply le_antisymm (completeInformation_le _)
  apply le_of_tendsto wait_information_tendsto
  apply Eventually.of_forall
  intro t
  exact le_csSup ⟨2 * Real.log 2, by
    rintro _ ⟨n,rfl⟩; exact prefixInformation_le _ n⟩ (Set.mem_range_self t)

/-- The literal complete information objective has an attained finite maximum,
with a strictly better feasible process on this full-support countable class. -/
theorem complete_dominated_maximizer :
    (∀ π : ValidCausalPolicy Bool Bool,
      completeInformation π ≤ completeInformation (pulsePolicy false)) ∧
    CausalBehaviorFinitaryDominates pulseBehavior (pulsePolicy true) (pulsePolicy false) ∧
    ¬ CausalBehaviorFinitaryDominates pulseBehavior (pulsePolicy false) (pulsePolicy true) := by
  refine ⟨?_, pulse_query_strictly_dominates_wait⟩
  intro π
  rw [wait_completeInformation]
  exact completeInformation_le π
end
end IdExp.PulseInformation
