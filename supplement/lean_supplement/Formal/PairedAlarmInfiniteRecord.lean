import Formal.PairedAlarmNativeScore
import Formal.PairedAlarmNativeExtraction
import Formal.PulseTerminal

/-!
# Infinite-record identification on the current paired alarm

The complete monitor stream has a measurable world decoder independent of both
the world and the collecting policy. It is correct almost surely under each
actual policy/world path law, including the never-pulse world. This is distinct
from the finite-record native error. Let `s` be startup inspection probability.
Every positive finite prefix still has inspection-target deficiency `(1 - s) / 2`. No prior, deterministic-policy restriction, or finite stopping
rule for certifying the never-pulse world is assumed.
-/

noncomputable section
namespace IdExp.PairedAlarm
open MeasureTheory Set Filter

/-- Retain the entire monitor stream and give it the pulse interface's WAIT
action labels. Display randomness and the collecting actions are discarded. -/
def extractWaitPath (ω : CausalTraj Action Observation) : CausalTraj Bool Bool :=
  fun i => (false, decide ((ω i).2.2 = 1))

theorem measurable_extractWaitPath : Measurable extractWaitPath := by
  apply measurable_pi_lambda
  intro i
  exact measurable_const.prodMk
    ((measurable_of_finite (fun x : Action × Observation => decide (x.2.2 = 1))).comp
      (measurable_pi_apply i))

/-- Every finite prefix of an actual path has nonzero probability almost
surely. Countably many such events can be used together below. -/
theorem ae_prefix_supported (π : ValidCausalPolicy Action Observation) (θ : World)
    (t : ℕ) :
    ∀ᵐ ω ∂causalPathMeasure π.1 π.2 (response θ) (response_valid θ),
      experiment π.1 t θ (causalPrefixMap t ω) ≠ 0 := by
  have each (w : CausalFiniteTrace Action Observation t) :
      ∀ᵐ ω ∂causalPathMeasure π.1 π.2 (response θ) (response_valid θ),
        causalPrefixMap t ω = w → experiment π.1 t θ w ≠ 0 := by
    by_cases hw : experiment π.1 t θ w = 0
    · have hz : (causalPathMeasure π.1 π.2 (response θ) (response_valid θ))
          {ω | causalPrefixMap t ω = w} = 0 := by
        change (causalPathMeasure π.1 π.2 (response θ) (response_valid θ))
          (causalPrefixMap t ⁻¹' {w}) = 0
        rw [causalPrefixMap_preimage_singleton, causalPathMeasure_cyl]
        change ENNReal.ofReal (experiment π.1 t θ w) = 0
        simp [hw]
      apply ae_iff.mpr
      simpa [hw] using hz
    · exact Filter.Eventually.of_forall (fun _ _ => hw)
  filter_upwards [ae_all_iff.mpr each] with ω hω
  exact hω (causalPrefixMap t ω) rfl

/-- The extracted infinite monitor path is the literal pulse path in every
world, almost surely under every randomized collecting policy. -/
theorem extractWaitPath_ae_eq (π : ValidCausalPolicy Action Observation) (θ : World) :
    ∀ᵐ ω ∂causalPathMeasure π.1 π.2 (response θ) (response_valid θ),
      extractWaitPath ω = pulsePath false θ := by
  filter_upwards [ae_all_iff.mpr (ae_prefix_supported π θ)] with ω hω
  funext i
  have h := supported_monitor π.1 θ (i+1) (causalPrefixMap (i+1) ω)
    (hω (i+1)) (Fin.last i)
  change (ω i).2.2 = monitorAt θ i at h
  change (false, decide ((ω i).2.2 = 1)) = pulsePath false θ i
  rw [h]
  cases i with
  | zero =>
    cases θ <;> simp [monitorAt, pulsePath, waitingQueryBit]
  | succ i =>
    simp only [pulsePath, Nat.succ_ne_zero, if_false, monitorAt_eq_one_iff]
    cases waitingQueryBit θ (i+1) <;> rfl

/-- One measurable decoder is correct under every actual policy/world path
law. Its choice precedes the policy and world quantifiers. -/
theorem infinite_record_exact_identification :
    ∃ D : CausalTraj Action Observation → World, Measurable D ∧
      ∀ (π : ValidCausalPolicy Action Observation) (θ : World),
        (causalPathMeasure π.1 π.2 (response θ) (response_valid θ))
          {ω | D ω = θ} = 1 := by
  obtain ⟨D, hD, hcorrect⟩ := pulsePath_exact_decoder false
  refine ⟨D ∘ extractWaitPath, hD.comp measurable_extractWaitPath, ?_⟩
  intro π θ
  apply (mem_ae_iff_prob_eq_one
    ((hD.comp measurable_extractWaitPath) (measurableSet_singleton θ))).mp
  change ∀ᵐ ω ∂causalPathMeasure π.1 π.2 (response θ) (response_valid θ),
    D (extractWaitPath ω) = θ
  filter_upwards [extractWaitPath_ae_eq π θ] with ω hω
  rw [hω, hcorrect]

/-- Infinite exact decoding coexists with the current law's nonvanishing
finite-record inspection error, for every policy that sometimes plays. -/
theorem infinite_identification_with_finite_deficiency
    (π : ValidCausalPolicy Action Observation) (hs : inspectionProbability π.1 < 1) :
    (∃ D : CausalTraj Action Observation → World, Measurable D ∧ ∀ θ,
      (causalPathMeasure π.1 π.2 (response θ) (response_valid θ))
        {ω | D ω = θ} = 1) ∧
    (∀ t, finiteDeficiency (experiment π.1 (t+1)) (experiment inspectPolicy 1) =
      (1-inspectionProbability π.1)/2) ∧
    ¬ CausalNativelySufficient response π := by
  obtain ⟨D, hD, hcorrect⟩ := infinite_record_exact_identification
  refine ⟨⟨D, hD, hcorrect π⟩, fun t => inspection_deficiency_exact π.1 π.2 t, ?_⟩
  rw [sufficient_iff_inspectionProbability_one π.1 π.2]
  exact ne_of_lt hs

end IdExp.PairedAlarm
