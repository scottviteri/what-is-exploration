import Formal.NativeDecisionReadiness
import Formal.DecisionReadiness
import Formal.FiniteRowKernel

/-!
# Native readiness simultaneously for every probability prior

Measurable dependence of each controlled-prefix mass on the world makes
literal finite records into Markov kernels. Their measure deficiency equals
the existing finite-matrix deficiency. Consequently the native audit chooses
one collection time before the probability prior, decision alphabet, utility,
and alternative collector are supplied. The world class need not be finite
or standard Borel, and measurable singleton worlds are not assumed.

The converse continues to need only the existing finite-support decision
problems, with no world measurability. The final theorem packages that exact
converse with the stronger forward probability-prior conclusion; it does not
assume that every utility on an arbitrary finite set of world labels extends
measurably to the entire parameter space.
-/
namespace IdExp
open MeasureTheory ProbabilityTheory Set
noncomputable section
set_option linter.unusedSectionVars false
universe u

variable {A O Θ : Type u} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O] [Nonempty Θ]
  [MeasurableSpace A] [MeasurableSpace O] [MeasurableSingletonClass A]
  [MeasurableSingletonClass O] [MeasurableSpace Θ]

/-- Parameter measurability of controlled masses suffices for every policy's
record rows; the policy's action likelihood is world-independent. -/
theorem measurable_causalBehaviorRecord_rows
    (ps : Θ → CausalBehavior A O)
    (hps : ∀ h, Measurable (fun θ => (ps θ).mass h))
    (π : ValidCausalPolicy A O) (t : ℕ) (x : CausalFiniteTrace A O t) :
    Measurable (fun θ => causalBehaviorFiniteExperiment π.1 ps t θ x) :=
  measurable_const.mul (hps (List.ofFn x))

/-- The actual acquired finite record as a parameter-measurable Markov kernel. -/
def causalBehaviorRecordKernel (ps : Θ → CausalBehavior A O)
    (hps : ∀ h, Measurable (fun θ => (ps θ).mass h))
    (π : ValidCausalPolicy A O) (t : ℕ) :
    FiniteMarkovKernel Θ (CausalFiniteTrace A O t) :=
  measurableRowKernel (causalBehaviorFiniteExperiment π.1 ps t)
    (causalBehaviorFiniteExperiment_valid π.1 π.2 ps t)
    (measurable_causalBehaviorRecord_rows ps hps π t)

/-- The bundled record is exactly the row measure of the canonical experiment. -/
theorem kernelExperiment_causalBehaviorRecordKernel
    (ps : Θ → CausalBehavior A O)
    (hps : ∀ h, Measurable (fun θ => (ps θ).mass h))
    (π : ValidCausalPolicy A O) (t : ℕ) :
    kernelExperiment (causalBehaviorRecordKernel ps hps π t) =
      rowExperiment (causalBehaviorFiniteExperiment π.1 ps t) := rfl

/-- No gap remains between measurable-decoder and finite-matrix deficiency
for these literal finite source and target records. -/
theorem finiteMeasureDeficiency_causalBehaviorRecordKernel
    (ps : Θ → CausalBehavior A O)
    (hps : ∀ h, Measurable (fun θ => (ps θ).mass h))
    (π ρ : ValidCausalPolicy A O) (t m : ℕ) :
    finiteMeasureDeficiency (kernelExperiment (causalBehaviorRecordKernel ps hps π t))
        (kernelExperiment (causalBehaviorRecordKernel ps hps ρ m)) =
      finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps t)
        (causalBehaviorFiniteExperiment ρ.1 ps m) :=
  finiteMeasureDeficiency_eq_finiteDeficiency _ _
    (causalBehaviorFiniteExperiment_valid π.1 π.2 ps t)
    (causalBehaviorFiniteExperiment_valid ρ.1 ρ.2 ps m)

/-- The time is chosen before all priors and all finite measurable purposes.
The requested native budget remains fixed independently of collection time. -/
def CausalBehaviorUniformProbabilityReadiness
    (ps : Θ → CausalBehavior A O)
    (hps : ∀ h, Measurable (fun θ => (ps θ).mass h))
    (π : ValidCausalPolicy A O) : Prop :=
  ∀ n ε, 0 < ε → ∃ T, ∀ t, T ≤ t →
    ∀ (α : Measure Θ) [IsProbabilityMeasure α],
    ∀ (D : Type u) [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D] [Nonempty D],
    ∀ (u : Θ → D → ℝ), (∀ d, Measurable (fun θ => u θ d)) →
      (∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) →
    ∀ (ρ : ValidCausalPolicy A O) (m : ℕ), m ≤ n →
      bayesExperimentValue α (causalBehaviorRecordKernel ps hps ρ m) u - ε ≤
        bayesExperimentValue α (causalBehaviorRecordKernel ps hps π t) u

/-- Native sufficiency gives readiness simultaneously for every probability
prior and measurable unit-range finite decision problem on the actual records.
Only the finite audit chooses T, so T is independent of the prior and purpose. -/
theorem causalBehaviorNativelySufficient_uniformProbabilityReadiness
    (ps : Θ → CausalBehavior A O)
    (hps : ∀ h, Measurable (fun θ => (ps θ).mass h))
    (π : ValidCausalPolicy A O) (hs : CausalBehaviorNativelySufficient ps π) :
    CausalBehaviorUniformProbabilityReadiness ps hps π := by
  intro n ε hε
  obtain ⟨T, hT⟩ := (causalBehaviorNativelySufficient_iff_eventually_nativeAudit_lt ps π).mp hs n ε hε
  refine ⟨T, fun t htt α _ D _ _ _ _ u hum hu ρ m hm => ?_⟩
  apply bayesExperimentValue_readiness α _ _ u hum hu
  rw [finiteMeasureDeficiency_causalBehaviorRecordKernel]
  have hsource := causalBehaviorFiniteExperiment_valid π.1 π.2 ps t
  apply le_trans _ (hT t htt).le
  rw [causalBehaviorNativeDeficiencyUpTo_eq_raw,
    causalNativeDeficiencyUpTo_eq_terminal _ hsource _
      (causalBehaviorResponsePresentation_valid ps),
    causalBehaviorFiniteExperiment_eq_toResponse ρ.1 ps m]
  exact finiteDeficiency_causalPolicy_le_native_of_le _ hsource ρ.1 ρ.2 _
    (causalBehaviorResponsePresentation_valid ps) hm

/-- Finite-support purposes suffice for the converse, while the forward
conclusion includes every probability prior under the stated measurability.
The finite-support conjunct retains arbitrary utilities on its finite support;
no extra measurability restriction is inserted into the necessity theorem. -/
theorem causalBehaviorNativelySufficient_iff_probability_and_finiteSupportReadiness
    (ps : Θ → CausalBehavior A O)
    (hps : ∀ h, Measurable (fun θ => (ps θ).mass h))
    (π : ValidCausalPolicy A O) :
    CausalBehaviorNativelySufficient ps π ↔
      CausalBehaviorUniformProbabilityReadiness ps hps π ∧
      (∀ n ε, 0 < ε → ∃ T, ∀ t, T ≤ t →
        ∀ (P : FiniteSupportDecisionProblem Θ) (ρ : ValidCausalPolicy A O)
          (m : ℕ), m ≤ n →
          finiteDecisionProblemValue (causalBehaviorFiniteExperiment ρ.1 ps m) P - ε ≤
            finiteDecisionProblemValue (causalBehaviorFiniteExperiment π.1 ps t) P) := by
  constructor
  · intro hs
    exact ⟨causalBehaviorNativelySufficient_uniformProbabilityReadiness ps hps π hs,
      (causalBehaviorNativelySufficient_iff_uniformDecisionReadiness ps π).mp hs⟩
  · rintro ⟨_, hs⟩
    exact (causalBehaviorNativelySufficient_iff_uniformDecisionReadiness ps π).mpr hs

end
end IdExp
