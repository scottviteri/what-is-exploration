import Formal.InfiniteInformationGain
import Formal.CausalBehaviorGeometry
import Formal.CausalProcess

/-! Finite-budget information-gain optima are Blackwell-admissible in the
canonical controlled-behavior topology, including infinite world classes.
This concerns exact maxima at one fixed horizon, not native sufficiency. -/

namespace IdExp

open MeasureTheory Set

variable {Θ A O : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ]
  [OpensMeasurableSpace Θ] [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]

/-- Prefix laws are continuous simply because each likelihood is a fixed
policy propensity times one controlled-behavior mass coordinate. -/
theorem continuous_behaviorAcquired_coordinate
    (ps : Θ → CausalBehavior A O) (hps : Continuous ps)
    (π : CausalPolicy A O) (t : ℕ) (h : CausalFiniteTrace A O t) :
    Continuous (fun θ => causalBehaviorFiniteExperiment π ps t θ h) := by
  change Continuous (fun θ => causalPolicyProb π (List.ofFn h) * (ps θ).mass (List.ofFn h))
  exact (((continuous_apply _).comp causalBehavior_mass_isEmbedding.continuous).comp hps).const_mul _

/-- Any feasible experiment dominating an exact information-gain optimum
is equivalent to it. The prior sees every nonempty open set of worlds. -/
theorem information_maximizer_blackwell_admissible
    (μ : Measure Θ) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (ps : Θ → CausalBehavior A O) (hps : Continuous ps)
    (S : Set (ValidCausalPolicy A O)) (π : ValidCausalPolicy A O) (t : ℕ)
    (hmax : ∀ ρ ∈ S,
      infinitePriorInformation μ (causalBehaviorFiniteExperiment ρ.1 ps t) ≤
        infinitePriorInformation μ (causalBehaviorFiniteExperiment π.1 ps t))
    (ρ : ValidCausalPolicy A O) (hρ : ρ ∈ S)
    (hdom : FiniteBlackwellLE (causalBehaviorFiniteExperiment π.1 ps t)
      (causalBehaviorFiniteExperiment ρ.1 ps t)) :
    FiniteBlackwellLE (causalBehaviorFiniteExperiment ρ.1 ps t)
      (causalBehaviorFiniteExperiment π.1 ps t) := by
  by_contra hn
  obtain ⟨G, hG, hGF⟩ := hdom
  have hlt := continuous_infinitePriorInformation_lt_of_no_reverse μ
    (causalBehaviorFiniteExperiment ρ.1 ps t) (causalBehaviorFiniteExperiment π.1 ps t)
    (causalBehaviorFiniteExperiment_valid _ ρ.2 ps t)
    (causalBehaviorFiniteExperiment_valid _ π.2 ps t)
    (continuous_behaviorAcquired_coordinate ps hps ρ.1 t)
    (continuous_behaviorAcquired_coordinate ps hps π.1 t) G hG hGF hn
  exact (not_lt_of_ge (hmax ρ hρ)) hlt

/-- The identical admissibility implication for any strictly convex
functional on a convex domain containing the relevant posterior densities. -/
theorem posteriorPotential_maximizer_blackwell_admissible
    (μ : Measure Θ) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (ps : Θ → CausalBehavior A O) (hps : Continuous ps)
    (Φ : (Θ → ℝ) → ℝ) (C : Set (Θ → ℝ)) (hΦ : StrictConvexOn ℝ C Φ)
    (S : Set (ValidCausalPolicy A O)) (π : ValidCausalPolicy A O) (t : ℕ)
    (hpost : ∀ ρ ∈ S, ∀ h, priorSignalDensity μ (causalBehaviorFiniteExperiment ρ.1 ps t) h ∈ C)
    (hmax : ∀ ρ ∈ S,
      priorSignalPotential μ (causalBehaviorFiniteExperiment ρ.1 ps t) Φ ≤
        priorSignalPotential μ (causalBehaviorFiniteExperiment π.1 ps t) Φ)
    (ρ : ValidCausalPolicy A O) (hρ : ρ ∈ S)
    (hdom : FiniteBlackwellLE (causalBehaviorFiniteExperiment π.1 ps t)
      (causalBehaviorFiniteExperiment ρ.1 ps t)) :
    FiniteBlackwellLE (causalBehaviorFiniteExperiment ρ.1 ps t)
      (causalBehaviorFiniteExperiment π.1 ps t) := by
  by_contra hn
  obtain ⟨G, hG, hGF⟩ := hdom
  have hlt := continuous_priorSignalPotential_lt_of_no_reverse μ
    (causalBehaviorFiniteExperiment ρ.1 ps t) (causalBehaviorFiniteExperiment π.1 ps t)
    (causalBehaviorFiniteExperiment_valid _ ρ.2 ps t)
    (causalBehaviorFiniteExperiment_valid _ π.2 ps t)
    (continuous_behaviorAcquired_coordinate ps hps ρ.1 t)
    (continuous_behaviorAcquired_coordinate ps hps π.1 t) G hG hGF Φ C hΦ (hpost ρ hρ) hn
  exact (not_lt_of_ge (hmax ρ hρ)) hlt

end IdExp
