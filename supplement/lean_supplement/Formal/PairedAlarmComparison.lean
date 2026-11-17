import Formal.PairedAlarmNativeAudit
import Formal.PairedAlarmNativeScore
import Formal.PairedAlarmPseudoCountObjective
import Formal.PairedAlarmBlockChannel
import Formal.PairedAlarmInformationDiscount
import Formal.PairedAlarmInformationComplete
import Formal.PairedAlarmInformationFinite
import Formal.PairedAlarmMovementOptima
import Formal.PairedAlarmPredictiveReturns

/-!
# The paired alarm: the comparison table

Each specified objective's optimizer characterization on the paired alarm
interface, combined with the exact native comparison. Objectives whose optima
skip startup inspection select policies with permanent inspection deficiency
`1/2` that are strictly finitarily dominated by inspection; objectives whose
optima inspect select natively sufficient policies. The complete information
and Brier returns tie every policy, including deficient ones. Complete block
empowerment has a different optimizer set: every policy with positive startup
PLAY probability maximizes, with native losses filling `(0,1/2]`.

The objective definitions and their source conventions are in the imported
modules; this file only assembles them. Bayesian prediction gain is connected
to the actual posterior-information rewards in `PairedAlarmPredictionGainReturns`,
including its finite-horizon optima and complete two-bit tie. The physical-state
and four-bit examples use their own interfaces and comparison modules.
-/

noncomputable section

namespace IdExp.PairedAlarm.Comparison

open IdExp.PairedAlarm

/-- The always-inspecting policy, as a valid policy. -/
def inspectValid : ValidCausalPolicy Action Observation := ⟨inspectPolicy, inspectPolicy_valid⟩

/-- The always-PLAY₀ policy; it never inspects. -/
def playValid : ValidCausalPolicy Action Observation := validDetPolicy fun _ => play0

theorem playValid_inspection : inspectionProbability playValid.1 = 0 := by
  norm_num [inspectionProbability, playValid, validDetPolicy, detPolicy, inspect, play0]

/-- The native consequence of skipping startup inspection: deficiency `1/2` to the
one-step inspection experiment at every positive collection time, and strict
finitary domination by inspection. Later choices are unrestricted. -/
def SkipsAndFails (π : ValidCausalPolicy Action Observation) : Prop :=
  inspectionProbability π.1 = 0 ∧
    (∀ n : ℕ, finiteDeficiency (experiment π.1 (n+1)) (experiment inspectPolicy 1) = 1/2) ∧
    CausalFinitaryDominates response inspectValid π ∧
    ¬ CausalFinitaryDominates response π inspectValid

theorem skipsAndFails_of_inspectionProbability_zero (π : ValidCausalPolicy Action Observation)
    (hs : inspectionProbability π.1 = 0) : SkipsAndFails π := by
  refine ⟨hs, fun n => ?_, inspection_strictly_dominates π.1 π.2 (by rw [hs]; norm_num)⟩
  rw [inspection_deficiency_exact π.1 π.2 n, hs]
  norm_num

/-- Inspecting at startup with probability one gives native sufficiency. -/
theorem sufficient_of_inspectionProbability_one (π : ValidCausalPolicy Action Observation)
    (hs : inspectionProbability π.1 = 1) : CausalNativelySufficient response π :=
  (sufficient_iff_inspectionProbability_one π.1 π.2).2 hs

/-! ## Rewards for variation without evidence: every optimum skips inspection -/

/-- Categorical pseudo-count, finite horizon `H ≥ 64`: a maximum is attained, and every
maximizer skips inspection and fails. -/
theorem pseudoCount_optima_fail (H : ℕ) (hH : 64 ≤ H) :
    (∃ π : ValidCausalPolicy Action Observation,
      ∀ ρ, PseudoCount.objective H ρ ≤ PseudoCount.objective H π) ∧
    ∀ π : ValidCausalPolicy Action Observation,
      (∀ ρ, PseudoCount.objective H ρ ≤ PseudoCount.objective H π) → SkipsAndFails π :=
  ⟨(PseudoCount.objective_large_horizon H hH).1, fun π hopt =>
    skipsAndFails_of_inspectionProbability_zero π
      (PseudoCount.objective_maximizer_skips_inspection H hH π hopt)⟩

/-- Literal complete full-block empowerment: every maximizer has positive native
loss, with inspection a strict finitary dominator. Startup is the actual prior
integral of the empty-history block capacity. -/
theorem blockEmpowerment_optima_fail (n : ℕ) (hn : 1 ≤ n)
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ, BlockChannel.completeReturn n ρ ≤ BlockChannel.completeReturn n π) :
    0 < BlockComplete.eventualInspectionDeficiency π ∧
      BlockComplete.eventualInspectionDeficiency π ≤ 1/2 ∧
      CausalFinitaryDominates response inspectValid π ∧
      ¬ CausalFinitaryDominates response π inspectValid :=
  BlockChannel.all_optima_failure n hn π hopt

/-- Every loss in `(0,1/2]` is attained by a literal complete-return optimum. -/
theorem blockEmpowerment_loss_realized (n : ℕ) (hn : 1 ≤ n)
    (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1/2) :
    ∃ π : ValidCausalPolicy Action Observation,
      (∀ ρ, BlockChannel.completeReturn n ρ ≤ BlockChannel.completeReturn n π) ∧
      BlockComplete.eventualInspectionDeficiency π = d :=
  BlockChannel.optimizer_loss_realized n hn d hd hd1

/-- Predictive Shannon, every finite horizon at least two: exactly the policies
that skip inspection maximize, and each has permanent deficiency one half. -/
theorem shannonFinite_optima_fail (H : ℕ) (hH : 2 ≤ H)
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ, Predictive.shannonFinite ρ H ≤ Predictive.shannonFinite π H) :
    SkipsAndFails π :=
  skipsAndFails_of_inspectionProbability_zero π
    ((Predictive.shannonFinite_maximizer_iff H hH π).mp hopt)

/-- Predictive Square, every finite horizon at least three. -/
theorem squareFinite_optima_fail (H : ℕ) (hH : 3 ≤ H)
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ, Predictive.squareFinite ρ H ≤ Predictive.squareFinite π H) :
    SkipsAndFails π :=
  skipsAndFails_of_inspectionProbability_zero π
    ((Predictive.squareFinite_maximizer_iff H hH π).mp hopt)

/-- Both finite predictive maxima are attained by the same policy from horizon three. -/
theorem predictive_optima_fail (H : ℕ) (hH : 3 ≤ H) :
    (∃ π : ValidCausalPolicy Action Observation,
      (∀ ρ, Predictive.shannonFinite ρ H ≤ Predictive.shannonFinite π H) ∧
      (∀ ρ, Predictive.squareFinite ρ H ≤ Predictive.squareFinite π H)) ∧
    ∀ π : ValidCausalPolicy Action Observation,
      ((∀ ρ, Predictive.shannonFinite ρ H ≤ Predictive.shannonFinite π H) →
        SkipsAndFails π) ∧
      ((∀ ρ, Predictive.squareFinite ρ H ≤ Predictive.squareFinite π H) →
        SkipsAndFails π) := by
  refine ⟨⟨Predictive.alwaysPlay, ?_, ?_⟩, fun π =>
    ⟨shannonFinite_optima_fail H (by omega) π, squareFinite_optima_fail H hH π⟩⟩
  · exact (Predictive.shannonFinite_maximizer_iff H (by omega) _).mpr
      Predictive.alwaysPlay_inspectionProbability
  · exact (Predictive.squareFinite_maximizer_iff H hH _).mpr
      Predictive.alwaysPlay_inspectionProbability

/-- Complete Shannon optimizers have positive native loss and a strict native dominator. -/
theorem shannonComplete_optima_fail (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ, Predictive.shannonComplete ρ ≤ Predictive.shannonComplete π) :
    0 < BlockComplete.eventualInspectionDeficiency π ∧
      BlockComplete.eventualInspectionDeficiency π ≤ 1/2 ∧
      CausalFinitaryDominates response inspectValid π ∧
      ¬ CausalFinitaryDominates response π inspectValid := by
  have hs := (Predictive.shannonComplete_maximizer_iff π).mp hopt
  refine ⟨?_, ?_, inspection_strictly_dominates π.1 π.2 hs⟩
  · rw [BlockComplete.eventualInspectionDeficiency_eq]; linarith
  · rw [BlockComplete.eventualInspectionDeficiency_eq]
    linarith [inspectionProbability_nonneg π.1 π.2]

theorem shannonComplete_loss_realized (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1/2) :
    ∃ π : ValidCausalPolicy Action Observation,
      (∀ ρ, Predictive.shannonComplete ρ ≤ Predictive.shannonComplete π) ∧
      BlockComplete.eventualInspectionDeficiency π = d := by
  let π := BlockComplete.mixedPolicy (1-2*d) (by linarith : 0 ≤ 1-2*d)
    (by linarith : 1-2*d ≤ 1)
  have hs : inspectionProbability π.1 = 1-2*d := rfl
  refine ⟨π, (Predictive.shannonComplete_maximizer_iff π).mpr (by rw [hs]; linarith), ?_⟩
  rw [BlockComplete.eventualInspectionDeficiency_eq, hs]
  ring

/-- Complete Square ties every policy, including the deficient never-inspecting policy. -/
theorem squareComplete_bad_tie :
    (∀ π : ValidCausalPolicy Action Observation, Predictive.squareComplete π = ⊥) ∧
    (∀ ρ, Predictive.squareComplete ρ ≤ Predictive.squareComplete playValid) ∧
    SkipsAndFails playValid :=
  ⟨Predictive.squareComplete_eq_bot, Predictive.squareComplete_all_maximize playValid,
    skipsAndFails_of_inspectionProbability_zero playValid playValid_inspection⟩

/-! ## Information and Brier on the world posterior -/

/-- Finite horizons `n+1 ≥ 1`: every maximizer of prefix information or of the expected
squared posterior norm is natively sufficient. -/
theorem finitePosterior_optima_succeed (n : ℕ) (π : ValidCausalPolicy Action Observation) :
    ((∀ ρ, Information.prefixInformation ρ (n+1) ≤ Information.prefixInformation π (n+1)) →
      CausalNativelySufficient response π) ∧
    ((∀ ρ, Information.prefixPotential ρ (n+1) ≤ Information.prefixPotential π (n+1)) →
      CausalNativelySufficient response π) :=
  ⟨fun hopt => sufficient_of_inspectionProbability_one π
      ((Information.finiteInformation_maximizer_iff n π).1 hopt),
    fun hopt => sufficient_of_inspectionProbability_one π
      ((Information.finiteBrier_maximizer_iff n π).1 hopt)⟩

/-- Every proper discount: every maximizer of discounted information or discounted Brier
movement is natively sufficient. -/
theorem discountedPosterior_optima_succeed (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) :
    ((∀ ρ, Information.discountedInformation γ ρ ≤ Information.discountedInformation γ π) →
      CausalNativelySufficient response π) ∧
    ((∀ ρ, Information.discountedBrier γ ρ ≤ Information.discountedBrier γ π) →
      CausalNativelySufficient response π) :=
  ⟨fun hopt => sufficient_of_inspectionProbability_one π
      ((Information.discountedInformation_maximizer_iff γ hγ hγ1 π).1 hopt),
    fun hopt => sufficient_of_inspectionProbability_one π
      ((Information.discountedBrier_maximizer_iff γ hγ hγ1 π).1 hopt)⟩

/-- Complete returns: every policy has complete information `2 log 2` nats and complete
Brier movement `2/3`, so every policy maximizes both, including the never-inspecting
`playValid`, which fails. -/
theorem completePosterior_bad_tie :
    (∀ π : ValidCausalPolicy Action Observation,
      Information.completeInformation π = 2 * Real.log 2 ∧
        Information.totalMovement π = 2/3) ∧
    (∀ ρ, Information.completeInformation ρ ≤ Information.completeInformation playValid) ∧
    (∀ ρ, Information.totalMovement ρ ≤ Information.totalMovement playValid) ∧
    SkipsAndFails playValid := by
  refine ⟨fun π => ⟨Information.completeInformation_eq π,
      Information.totalMovement_eq_two_thirds π⟩, fun ρ => ?_, fun ρ => ?_,
    skipsAndFails_of_inspectionProbability_zero playValid playValid_inspection⟩
  · rw [Information.completeInformation_eq ρ, Information.completeInformation_eq playValid]
  · rw [Information.totalMovement_eq_two_thirds ρ,
      Information.totalMovement_eq_two_thirds playValid]

/-! ## Hellinger and Absolute posterior movement -/

/-- Every `0 ≤ γ ≤ 1`, with `γ = 1` the complete return: every maximizer is natively
sufficient, and inspection attains the maximum. -/
theorem movement_optima_succeed (kind : PosteriorMovement.Kind) (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ, Movement.discounted kind γ ρ ≤ Movement.discounted kind γ π) :
    CausalNativelySufficient response π :=
  sufficient_of_inspectionProbability_one π ((Movement.isMaximizer_iff kind γ hγ hγ1 π).1 hopt)

theorem movementComplete_optima_succeed (kind : PosteriorMovement.Kind)
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ, Movement.complete kind ρ ≤ Movement.complete kind π) :
    CausalNativelySufficient response π :=
  sufficient_of_inspectionProbability_one π ((Movement.complete_isMaximizer_iff kind π).1 hopt)

/-! ## The native score -/

/-- Every maximizer of a rich positive-weight native score is natively sufficient. -/
theorem nativeScore_optima_succeed (ρ : ℕ → ℕ → ValidCausalPolicy Action Observation)
    (hρ : DenseRecordFamily response (fun n k => experiment (ρ n k).1 n))
    (w : ℕ → ℝ) (hw : ∀ j, 0 < w j) (hsum : Summable w)
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ σ, nativeWeightedObjective ρ w σ ≤ nativeWeightedObjective ρ w π) :
    CausalNativelySufficient response π :=
  sufficient_of_inspectionProbability_one π
    ((nativeWeightedObjective_maximizer_iff ρ hρ w hw hsum π).1 hopt)

end IdExp.PairedAlarm.Comparison
