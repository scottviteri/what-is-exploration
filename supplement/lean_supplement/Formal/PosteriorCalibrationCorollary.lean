import Formal.PosteriorFeasibleObjectives
import Formal.PosteriorNativeCalibration
import Formal.PosteriorRegretBound
import Formal.QuadraticReverseBound

/-!
# Near-optimal complete posterior gain preserves native targets

This assembles the main paper's posterior calibration corollary on its literal
feasible-family supremum. It retains ordinary squared-posterior Brier gain,
the prior floor in each constant, and the order of the uniform quantifiers.
The controlled-behavior wrappers discharge response validity.
-/
namespace IdExp
open Set Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
universe u v
variable {A O Θ : Type u} {P : Type v} [Fintype A] [Fintype O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]
  [Nonempty A] [Nonempty O] [Fintype Θ] [Nonempty Θ]
  [DecidableEq Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

variable (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))

/-- Literal selected-policy calibration on any family containing a sufficient
policy. The family is arbitrary; no topology or compactness is imposed. -/
theorem causalPotentialObjective_nativeRecordCalibrated
    (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (F : P → ValidCausalPolicy A O) (pstar : P)
    (hstar : CausalNativelySufficient Qs (F pstar)) :
    NativeRecordObjectiveCalibrated Qs F
      (fun p => causalPotentialObjective Φ α Qs hQ (F p)) := by
  intro ρ n ε hε
  obtain ⟨η, hη, hsmall⟩ := exists_eventualLoss_tolerance_of_strictConvexOn
    Qs hQ Φ hΦc hΦ α hα hfs ε hε
  refine ⟨η, hη, fun p hp => ?_⟩
  have heq := causalPotentialObjective_feasibleSup_eq Qs hQ Φ hΦc hΦ.convexOn
    α hα F pstar hstar
  have hg : causalPotentialObjective Φ α Qs hQ (F pstar) -
      causalPotentialObjective Φ α Qs hQ (F p) ≤ η := by
    simpa only [selectedPolicySet, mem_ofPred_eq, heq] using hp
  exact hsmall (F p) (F pstar) hstar hg ρ n

/-- A reusable reverse bound controls actual feasible-family regret. -/
theorem eventualLoss_le_min_sqrt_feasiblePotentialRegret
    (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (c : ℝ) (hc : 0 ≤ c) (hrev : HasReverseBound.{u,u} Φ α c)
    (F : P → ValidCausalPolicy A O) (pstar : P)
    (hstar : CausalNativelySufficient Qs (F pstar)) (p : P)
    (ρ : ValidCausalPolicy A O) (n : ℕ) :
    eventualLoss Qs (F p) (causalFiniteExperiment ρ.1 Qs n) ≤ min 1
      (Real.sqrt (c * (objectiveSup (fun q => causalPotentialObjective Φ α Qs hQ (F q)) -
        causalPotentialObjective Φ α Qs hQ (F p)) / a)) := by
  rw [causalPotentialObjective_feasibleSup_eq Qs hQ Φ hΦc hΦ α hα F pstar hstar]
  exact eventualLoss_nativeRecord_le_min_sqrt_potential_gap Qs hQ Φ hΦc hΦ
    α hα a ha hlow c hc hrev (F p) (F pstar) hstar ρ n

/-- Complete information in nats has the exact stated sufficient bound. -/
theorem eventualLoss_le_min_sqrt_informationRegret
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (F : P → ValidCausalPolicy A O) (pstar : P)
    (hstar : CausalNativelySufficient Qs (F pstar)) (p : P)
    (ρ : ValidCausalPolicy A O) (n : ℕ) :
    eventualLoss Qs (F p) (causalFiniteExperiment ρ.1 Qs n) ≤ min 1
      (Real.sqrt ((objectiveSup (fun q => causalInformationObjective α Qs hQ (F q)) -
        causalInformationObjective α Qs hQ (F p)) / (2 * a))) := by
  have hb := eventualLoss_le_min_sqrt_feasiblePotentialRegret Qs hQ
    (fun p => -ent p) continuous_ent.neg.continuousOn strictConvexOn_neg_ent_simplex.convexOn
    α hα a ha hlow (1/2) (by norm_num) (negEnt_hasReverseBound α hα)
    F pstar hstar p ρ n
  simp only [← causalInformationObjective_eq_negEntropyPotential] at hb
  convert hb using 1
  congr 2
  ring

/-- The Brier potential is the ordinary sum of squared posterior masses,
with no inverse-prior coordinate weights. -/
theorem eventualLoss_le_min_sqrt_brierRegret
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (F : P → ValidCausalPolicy A O) (pstar : P)
    (hstar : CausalNativelySufficient Qs (F pstar)) (p : P)
    (ρ : ValidCausalPolicy A O) (n : ℕ) :
    eventualLoss Qs (F p) (causalFiniteExperiment ρ.1 Qs n) ≤ min 1
      (Real.sqrt (objectiveSup (fun q =>
          causalPotentialObjective posteriorQuadraticPotential α Qs hQ (F q)) -
        causalPotentialObjective posteriorQuadraticPotential α Qs hQ (F p)) / (2 * a)) := by
  have hb := eventualLoss_le_min_sqrt_feasiblePotentialRegret Qs hQ
    posteriorQuadraticPotential continuous_posteriorQuadraticPotential.continuousOn
    convexOn_posteriorQuadraticPotential α hα a ha hlow (1/(4*a)) (by positivity)
    (quadratic_hasReverseBound α hα a ha hlow) F pstar hstar p ρ n
  have hs (g : ℝ) : Real.sqrt ((1/(4*a))*g/a) = Real.sqrt g / (2*a) := by
    rw [show (1/(4*a))*g/a = g/(2*a)^2 by field_simp; ring,
      Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ 2*a)]
  simpa only [hs] using hb

/-- The qualitative corollary directly on controlled-prefix behaviors. -/
theorem causalBehaviorPotentialObjective_nativeRecordCalibrated
    (ps : Θ → CausalBehavior A O) (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (F : P → ValidCausalPolicy A O) (pstar : P)
    (hstar : CausalBehaviorNativelySufficient ps (F pstar)) :
    CausalBehaviorNativeRecordObjectiveCalibrated ps F
      (fun p => causalBehaviorPotentialObjective Φ α ps (F p)) := by
  rw [causalBehaviorNativeRecordObjectiveCalibrated_iff_raw]
  exact causalPotentialObjective_nativeRecordCalibrated _ _ Φ hΦc hΦ α hα hfs F pstar
    ((causalBehaviorNativelySufficient_iff_raw ps (F pstar)).mp hstar)


/-- Exact maximizers within the declared feasible family. -/
theorem causalPotentialObjective_feasibleMaximizer_iff_sufficient
    (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (F : P → ValidCausalPolicy A O) (pstar : P)
    (hstar : CausalNativelySufficient Qs (F pstar)) (p : P) :
    (∀ q, causalPotentialObjective Φ α Qs hQ (F q) ≤
      causalPotentialObjective Φ α Qs hQ (F p)) ↔ CausalNativelySufficient Qs (F p) := by
  constructor
  · intro hp
    apply causalNativelySufficient_of_strictConvex_objective_eq Qs hQ Φ hΦc hΦ α hα hfs hstar
    exact le_antisymm (causalPotentialObjective_le_of_nativelySufficient
      Qs hQ Φ hΦc hΦ.convexOn α hα hstar (F p)) (hp pstar)
  · intro hp q
    exact causalPotentialObjective_le_of_nativelySufficient Qs hQ Φ hΦc hΦ.convexOn α hα hp (F q)

/-- Changing information units rescales actual feasible-family regret. -/
theorem eventualLoss_le_min_sqrt_informationBitsRegret
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (F : P → ValidCausalPolicy A O) (pstar : P)
    (hstar : CausalNativelySufficient Qs (F pstar)) (p : P)
    (ρ : ValidCausalPolicy A O) (n : ℕ) :
    eventualLoss Qs (F p) (causalFiniteExperiment ρ.1 Qs n) ≤ min 1
      (Real.sqrt ((Real.log 2) *
        (objectiveSup (fun q => causalInformationObjective α Qs hQ (F q) / Real.log 2) -
          causalInformationObjective α Qs hQ (F p) / Real.log 2) / (2 * a))) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmax (q : P) : causalInformationObjective α Qs hQ (F q) ≤
      causalInformationObjective α Qs hQ (F pstar) := by
    simp only [causalInformationObjective_eq_negEntropyPotential]
    exact causalPotentialObjective_le_of_nativelySufficient Qs hQ (fun p => -ent p)
      continuous_ent.neg.continuousOn strictConvexOn_neg_ent_simplex.convexOn α hα hstar (F q)
  have hs := objectiveSup_eq_of_attained_upper
    (fun q => causalInformationObjective α Qs hQ (F q)) pstar hmax
  have hsb := objectiveSup_eq_of_attained_upper
    (fun q => causalInformationObjective α Qs hQ (F q) / Real.log 2) pstar
    (fun q => div_le_div_of_nonneg_right (hmax q) hlog.le)
  have hb := eventualLoss_le_min_sqrt_informationRegret Qs hQ α hα a ha hlow
    F pstar hstar p ρ n
  rw [hs] at hb
  rw [hsb]
  convert hb using 1
  congr 2
  field_simp

/-- Both printed rates with the actual minimum prior atom and actual behavior
records. Collection and target horizons remain independent. -/
theorem causalBehavior_posterior_regret_bounds
    (ps : Θ → CausalBehavior A O) (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (F : P → ValidCausalPolicy A O) (pstar : P)
    (hstar : CausalBehaviorNativelySufficient ps (F pstar))
    (p : P) (ρ : ValidCausalPolicy A O) (n : ℕ) :
    let ell := ⨅ t : ℕ, finiteDeficiency (causalBehaviorFiniteExperiment (F p).1 ps t)
      (causalBehaviorFiniteExperiment ρ.1 ps n)
    let gI := objectiveSup (fun q => causalBehaviorPotentialObjective (fun b => -ent b) α ps (F q)) -
      causalBehaviorPotentialObjective (fun b => -ent b) α ps (F p)
    let gB := objectiveSup (fun q => causalBehaviorPotentialObjective posteriorQuadraticPotential α ps (F q)) -
      causalBehaviorPotentialObjective posteriorQuadraticPotential α ps (F p)
    ell ≤ min 1 (Real.sqrt (gI / (2 * priorMinimum α))) ∧
      ell ≤ min 1 (Real.sqrt gB / (2 * priorMinimum α)) := by
  have hraw := (causalBehaviorNativelySufficient_iff_raw ps (F pstar)).mp hstar
  constructor
  · simpa only [causalBehaviorFiniteExperiment_eq_toResponse, causalBehaviorPotentialObjective,
      eventualLoss, causalInformationObjective_eq_negEntropyPotential] using
      eventualLoss_le_min_sqrt_informationRegret (causalBehaviorResponsePresentation ps)
        (causalBehaviorResponsePresentation_valid ps) α hα (priorMinimum α)
        (priorMinimum_pos α hfs) (priorMinimum_le α) F pstar hraw p ρ n
  · simpa only [causalBehaviorFiniteExperiment_eq_toResponse, causalBehaviorPotentialObjective,
      eventualLoss] using
      eventualLoss_le_min_sqrt_brierRegret (causalBehaviorResponsePresentation ps)
        (causalBehaviorResponsePresentation_valid ps) α hα (priorMinimum α)
        (priorMinimum_pos α hfs) (priorMinimum_le α) F pstar hraw p ρ n

end
end IdExp
