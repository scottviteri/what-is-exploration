import Formal.WaitingQueryNativeAudit
import Formal.DecisionReadiness

/-!
# Arbitrary-prior decision readiness of the countable waiting collector

The record experiment below is the literal actual controlled-behavior record
of `WaitingQueryBehavior.lean`, now bundled as a measurable Markov kernel.
The decoder interprets a detected pulse as its finite world and blank as
infinity. Its only possible error is the undetected finite-world tail, whose
probability tends to zero under every fixed probability prior.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

instance waitingQueryWorldMeasurableSpace : MeasurableSpace WaitingQueryWorld := ⊤
instance waitingQueryWorldMeasurableSingletonClass : MeasurableSingletonClass WaitingQueryWorld :=
  ⟨fun _ => trivial⟩

/-- Undetected finite worlds. Infinity is never in this error event. -/
def waitingQueryTailSet (t : ℕ) : Set WaitingQueryWorld :=
  {θ | ∃ k, θ = some k ∧ t < k + 2}

/-- Prior mass of the only possible decoder-error event. -/
noncomputable def waitingQueryTail (α : Measure WaitingQueryWorld) (t : ℕ) : ℝ :=
  α.real (waitingQueryTailSet t)

theorem waitingQueryTailSet_antitone : Antitone waitingQueryTailSet := by
  intro s t hst θ hθ
  obtain ⟨k, rfl, hk⟩ := hθ
  exact ⟨k, rfl, lt_of_le_of_lt hst hk⟩

theorem waitingQueryTailSet_iInter : (⋂ t, waitingQueryTailSet t) = ∅ := by
  ext θ
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨k, rfl, _⟩ := h 0
  have hk := h (k + 2)
  simp [waitingQueryTailSet] at hk

/-- The undetected mass vanishes under every fixed probability prior on
the entire countable world class. -/
theorem waitingQueryTail_tendsto_zero (α : Measure WaitingQueryWorld) [IsProbabilityMeasure α] :
    Tendsto (waitingQueryTail α) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := α)
    (fun t => (show MeasurableSet (waitingQueryTailSet t) from trivial).nullMeasurableSet)
    waitingQueryTailSet_antitone ⟨0, measure_ne_top _ _⟩
  rw [waitingQueryTailSet_iInter, measure_empty] at h
  change Tendsto (fun t => (α (waitingQueryTailSet t)).toReal) atTop (𝓝 0)
  simpa [Function.comp_def] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp h

/-- Measurable actual record law, identical to the full deterministic trace
already derived from controlled-behavior execution. -/
noncomputable def waitingQueryRecordKernel (t : ℕ) :
    FiniteMarkovKernel WaitingQueryWorld (CausalFiniteTrace Bool Bool t) :=
  ⟨Kernel.deterministic (waitingQueryTrace t) (measurable_of_countable _), inferInstance⟩

/-- The measurable kernel is the row measure of the actual acquired
experiment, not a separate observation model. -/
theorem waitingQueryRecordKernel_eq_actual (t : ℕ) (θ : WaitingQueryWorld) :
    (kernelExperiment (waitingQueryRecordKernel t) θ : Measure (CausalFiniteTrace Bool Bool t)) =
      (rowExperiment (waitingQueryExperiment t) θ : Measure (CausalFiniteTrace Bool Bool t)) := by
  rw [waitingQueryExperiment_eq_dirac]
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro x
  simp [kernelExperiment, waitingQueryRecordKernel, rowExperiment, measureReal_def,
    finiteMeasureOfRow_singleton, diracExp, Kernel.deterministic_apply, Pi.single_apply, eq_comm]
  split <;> simp

/-- The inferred integer-or-blank signal recovers every actual waiting
trace exactly. Thus the short description is a reversible encoding of
the literal acquired experiment on its support. -/
theorem waitingQueryTrace_recoverable (t : ℕ) (θ : WaitingQueryWorld) :
    waitingQueryTrace t (waitingQueryGuess t (waitingQueryTrace t θ)) = waitingQueryTrace t θ := by
  cases θ with
  | none => rw [waitingQueryGuess_exact t none (Or.inl rfl)]
  | some k =>
    by_cases hk : k + 2 ≤ t
    · rw [waitingQueryGuess_exact t (some k) (Or.inr ⟨k, rfl, hk⟩)]
    · have hkt : t < k + 2 := by omega
      rw [waitingQueryTrace_undetected t k hkt, waitingQueryGuess_exact t none (Or.inl rfl)]

/-- A finite native alternative on the actual behavior class, bundled for
arbitrary measurable probability-prior evaluation. -/
noncomputable def waitingQueryNativeKernel {m : ℕ} (σ : CausalObservationPlan Bool Bool m) :
    FiniteMarkovKernel WaitingQueryWorld (CausalObservationTrace Bool m) :=
  ⟨Kernel.deterministic (fun θ => detPlanObs m σ.toCausalPlan (waitingQueryOutput θ))
    (measurable_of_countable _), inferInstance⟩

/-- The native kernel is exactly the row law of canonical native execution. -/
theorem waitingQueryNativeKernel_eq_actual {m : ℕ}
    (σ : CausalObservationPlan Bool Bool m) (θ : WaitingQueryWorld) :
    (kernelExperiment (waitingQueryNativeKernel σ) θ : Measure (CausalObservationTrace Bool m)) =
      (rowExperiment (CausalObservationPlan.behaviorPlanExperiment σ waitingQueryBehavior) θ :
        Measure (CausalObservationTrace Bool m)) := by
  rw [waitingQuery_nativePlan_dirac]
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro x
  simp [kernelExperiment, waitingQueryNativeKernel, rowExperiment, measureReal_def,
    finiteMeasureOfRow_singleton, diracExp, Kernel.deterministic_apply, Pi.single_apply, eq_comm]
  split <;> simp

/-- Measurable world-independent interpretation of an acquired trace. -/
noncomputable def waitingQueryGuessKernel (t : ℕ) :
    FiniteMarkovKernel (CausalFiniteTrace Bool Bool t) WaitingQueryWorld :=
  ⟨Kernel.deterministic (waitingQueryGuess t) (measurable_of_finite _), inferInstance⟩

/-- Interpret the trace and then generate the requested target experiment. -/
noncomputable def waitingQueryTargetDecoder {Y : Type*} [MeasurableSpace Y]
    (t : ℕ) (F : FiniteMarkovKernel WaitingQueryWorld Y) :
    FiniteMarkovKernel (CausalFiniteTrace Bool Bool t) Y :=
  F.comp (waitingQueryGuessKernel t)

/-- Exact decoded law, including the undetected branches. -/
theorem waitingQuery_decodedLaw {Y : Type*} [MeasurableSpace Y]
    (t : ℕ) (F : FiniteMarkovKernel WaitingQueryWorld Y) (θ : WaitingQueryWorld) :
    finiteMarkovDecode (waitingQueryTargetDecoder t F)
      (kernelExperiment (waitingQueryRecordKernel t) θ) =
        kernelExperiment F (waitingQueryGuess t (waitingQueryTrace t θ)) := by
  apply Subtype.ext
  change (waitingQueryTargetDecoder t F).toKernel ∘ₘ
    Measure.dirac (waitingQueryTrace t θ) = _
  rw [Measure.dirac_bind (waitingQueryTargetDecoder t F).toKernel.measurable]
  change (F.toKernel ∘ₖ (waitingQueryGuessKernel t).toKernel) (waitingQueryTrace t θ) = _
  rw [Kernel.comp_apply]
  change F.toKernel ∘ₘ Measure.dirac (waitingQueryGuess t (waitingQueryTrace t θ)) = _
  exact Measure.dirac_bind F.toKernel.measurable _

theorem waitingQueryGuess_exact_off_tail (t : ℕ) (θ : WaitingQueryWorld)
    (hθ : θ ∉ waitingQueryTailSet t) :
    waitingQueryGuess t (waitingQueryTrace t θ) = θ := by
  apply waitingQueryGuess_exact
  cases θ with
  | none => exact Or.inl rfl
  | some k =>
    right
    refine ⟨k, rfl, ?_⟩
    have hk : ¬ t < k + 2 := fun hk => hθ ⟨k, rfl, hk⟩
    omega

/-- The actual target decoder is exact off the undetected finite-world
error event; on that event its TV error is at most one. -/
theorem waitingQuery_decoderTV_le_indicator {Y : Type*} [MeasurableSpace Y]
    (t : ℕ) (F : FiniteMarkovKernel WaitingQueryWorld Y) (θ : WaitingQueryWorld) :
    finiteMeasureTV
      (finiteMarkovDecode (waitingQueryTargetDecoder t F)
        (kernelExperiment (waitingQueryRecordKernel t) θ) : Measure Y)
      (kernelExperiment F θ : Measure Y) ≤ (waitingQueryTailSet t).indicator (fun _ => 1) θ := by
  rw [waitingQuery_decodedLaw]
  by_cases hθ : θ ∈ waitingQueryTailSet t
  · rw [Set.indicator_of_mem hθ]
    exact finiteMeasureTV_le_one _ _
  · rw [waitingQueryGuess_exact_off_tail t θ hθ, Set.indicator_of_notMem hθ]
    simp [finiteMeasureTV_self]

/-- The prior-averaged total-variation error is at most the undetected
finite-world tail, for every fixed probability prior and target kernel. -/
theorem waitingQuery_integral_decoderTV_le_tail {Y : Type*} [MeasurableSpace Y]
    (α : Measure WaitingQueryWorld) [IsProbabilityMeasure α]
    (t : ℕ) (F : FiniteMarkovKernel WaitingQueryWorld Y) :
    (∫ θ, finiteMeasureTV
      (finiteMarkovDecode (waitingQueryTargetDecoder t F)
        (kernelExperiment (waitingQueryRecordKernel t) θ) : Measure Y)
      (kernelExperiment F θ : Measure Y) ∂α) ≤ waitingQueryTail α t := by
  have hbound θ := waitingQuery_decoderTV_le_indicator t F θ
  have hint : Integrable (fun θ => finiteMeasureTV
      (finiteMarkovDecode (waitingQueryTargetDecoder t F)
        (kernelExperiment (waitingQueryRecordKernel t) θ) : Measure Y)
      (kernelExperiment F θ : Measure Y)) α := by
    apply (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [] with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (finiteMeasureTV_nonneg _ _)]
    have := isProbabilityMeasure_finiteMarkovDecode (waitingQueryTargetDecoder t F)
      (kernelExperiment (waitingQueryRecordKernel t) θ)
    exact finiteMeasureTV_le_one _ _
  have hset : MeasurableSet (waitingQueryTailSet t) := trivial
  calc
    _ ≤ ∫ θ, (waitingQueryTailSet t).indicator (fun _ => (1 : ℝ)) θ ∂α :=
      integral_mono hint ((integrable_const 1).indicator hset) hbound
    _ = waitingQueryTail α t := integral_indicator_one hset

/-- A finite support has a finite last possible pulse time. -/
def waitingQuerySupportTime (S : Finset WaitingQueryWorld) : ℕ :=
  S.sup (fun θ => θ.elim 0 (fun k => k + 2))

/-- Every finitely supported prior has zero tail after an explicit finite
support-dependent time. -/
theorem waitingQueryTail_zero_of_finiteSupport
    (α : Measure WaitingQueryWorld) (S : Finset WaitingQueryWorld)
    (hS : α (S : Set WaitingQueryWorld)ᶜ = 0)
    (t : ℕ) (ht : waitingQuerySupportTime S ≤ t) : waitingQueryTail α t = 0 := by
  have hsub : waitingQueryTailSet t ⊆ (S : Set WaitingQueryWorld)ᶜ := by
    rintro θ ⟨k, rfl, hk⟩ hmem
    have hbound : k + 2 ≤ waitingQuerySupportTime S := by
      exact Finset.le_sup (f := fun θ => θ.elim 0 (fun k => k + 2)) hmem
    omega
  have hzero : α (waitingQueryTailSet t) = 0 :=
    le_antisymm ((measure_mono hsub).trans_eq hS) bot_le
  simp [waitingQueryTail, measureReal_def, hzero]

section Decision

variable {Y D : Type*} [MeasurableSpace Y]
  [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D] [Nonempty D]

/-- Rule-by-rule decision readiness with the prior-tail error bound. -/
theorem waitingQuery_bayesRuleValue_sub_le_tail
    (α : Measure WaitingQueryWorld) [IsProbabilityMeasure α]
    (t : ℕ) (F : FiniteMarkovKernel WaitingQueryWorld Y)
    (r : FiniteMarkovKernel Y D) (u : WaitingQueryWorld → D → ℝ)
    (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) :
    bayesRuleValue α F r u - bayesRuleValue α (waitingQueryRecordKernel t)
      (r.comp (waitingQueryTargetDecoder t F)) u ≤ waitingQueryTail α t := by
  have hum d : Measurable (fun θ => u θ d) := measurable_of_countable _
  have hpoint θ : bayesRulePayoff F r u θ -
      bayesRulePayoff (waitingQueryRecordKernel t) (r.comp (waitingQueryTargetDecoder t F)) u θ ≤
        (waitingQueryTailSet t).indicator (fun _ => (1 : ℝ)) θ := by
    by_cases hθ : θ ∈ waitingQueryTailSet t
    · rw [Set.indicator_of_mem hθ]
      have hF := bayesRulePayoff_mem_unitInterval F r u hu θ
      have hE := bayesRulePayoff_mem_unitInterval (waitingQueryRecordKernel t)
        (r.comp (waitingQueryTargetDecoder t F)) u hu θ
      linarith [hF.2, hE.1]
    · rw [Set.indicator_of_notMem hθ]
      have heq : bayesRulePayoff (waitingQueryRecordKernel t)
          (r.comp (waitingQueryTargetDecoder t F)) u θ = bayesRulePayoff F r u θ := by
        unfold bayesRulePayoff
        rw [finiteMarkovDecode_comp, waitingQuery_decodedLaw, waitingQueryGuess_exact_off_tail t θ hθ]
      rw [heq, sub_self]
  unfold bayesRuleValue
  rw [← integral_sub (integrable_bayesRulePayoff α F r u hum hu)
    (integrable_bayesRulePayoff α (waitingQueryRecordKernel t)
      (r.comp (waitingQueryTargetDecoder t F)) u hum hu)]
  have hset : MeasurableSet (waitingQueryTailSet t) := trivial
  calc
    _ ≤ ∫ θ, (waitingQueryTailSet t).indicator (fun _ => (1 : ℝ)) θ ∂α :=
      integral_mono
        ((integrable_bayesRulePayoff α F r u hum hu).sub
          (integrable_bayesRulePayoff α (waitingQueryRecordKernel t)
            (r.comp (waitingQueryTargetDecoder t F)) u hum hu))
        ((integrable_const 1).indicator hset) hpoint
    _ = waitingQueryTail α t := integral_indicator_one hset

/-- After optimizing all randomized decision rules, the same fixed-prior
bound holds uniformly over unit-range utilities and all target kernels. -/
theorem waitingQuery_bayesValue_sub_le_tail
    (α : Measure WaitingQueryWorld) [IsProbabilityMeasure α]
    (t : ℕ) (F : FiniteMarkovKernel WaitingQueryWorld Y)
    (u : WaitingQueryWorld → D → ℝ) (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) :
    bayesExperimentValue α F u - bayesExperimentValue α (waitingQueryRecordKernel t) u ≤
      waitingQueryTail α t := by
  have hum d : Measurable (fun θ => u θ d) := measurable_of_countable _
  have hupper : bayesExperimentValue α F u ≤
      bayesExperimentValue α (waitingQueryRecordKernel t) u + waitingQueryTail α t := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨r, rfl⟩
    have h := waitingQuery_bayesRuleValue_sub_le_tail α t F r u hu
    have he := le_csSup (bayesValue_range_bddAbove α (waitingQueryRecordKernel t) u hum hu)
      (Set.mem_range_self (r.comp (waitingQueryTargetDecoder t F)))
    change bayesRuleValue α (waitingQueryRecordKernel t) (r.comp (waitingQueryTargetDecoder t F)) u ≤
      bayesExperimentValue α (waitingQueryRecordKernel t) u at he
    linarith
  linarith

/-- Every fixed probability-prior decision problem is eventually ready for
any fixed target experiment, although the uniform native audit stays one half. -/
theorem waitingQuery_bayesValue_le_liminf
    (α : Measure WaitingQueryWorld) [IsProbabilityMeasure α]
    (F : FiniteMarkovKernel WaitingQueryWorld Y)
    (u : WaitingQueryWorld → D → ℝ) (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) :
    bayesExperimentValue α F u ≤
      Filter.liminf (fun t => bayesExperimentValue α (waitingQueryRecordKernel t) u) atTop := by
  have hum d : Measurable (fun θ => u θ d) := measurable_of_countable _
  have hv t := bayesExperimentValue_mem_unitInterval α (waitingQueryRecordKernel t) u hum hu
  apply (Filter.le_liminf_iff'
    (f := (atTop : Filter ℕ)) (u := fun t => bayesExperimentValue α (waitingQueryRecordKernel t) u)
    (Filter.isCoboundedUnder_ge_of_le (atTop : Filter ℕ) (fun t => (hv t).2))
    (Filter.isBoundedUnder_of ⟨0, fun t => (hv t).1⟩)).2
  intro b hb
  filter_upwards [(tendsto_order.mp (waitingQueryTail_tendsto_zero α)).2 _ (sub_pos.mpr hb)] with t ht
  have hgap := waitingQuery_bayesValue_sub_le_tail α t F u hu
  linarith

/-- For a finitely supported prior the readiness bound is exactly zero
from a prior-dependent finite time, uniformly over targets and purposes. -/
theorem waitingQuery_bayesValue_finiteSupport
    (α : Measure WaitingQueryWorld) [IsProbabilityMeasure α]
    (S : Finset WaitingQueryWorld) (hS : α (S : Set WaitingQueryWorld)ᶜ = 0)
    (t : ℕ) (ht : waitingQuerySupportTime S ≤ t)
    (F : FiniteMarkovKernel WaitingQueryWorld Y)
    (u : WaitingQueryWorld → D → ℝ) (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) :
    bayesExperimentValue α F u ≤ bayesExperimentValue α (waitingQueryRecordKernel t) u := by
  have h := waitingQuery_bayesValue_sub_le_tail α t F u hu
  rw [waitingQueryTail_zero_of_finiteSupport α S hS t ht] at h
  linarith

/-- Literal causal specialization: under every fixed countable-world
probability prior, the actual waiting collector eventually meets every
fixed finite native intervention's optimized decision value. -/
theorem waitingQuery_native_bayesValue_le_liminf
    (α : Measure WaitingQueryWorld) [IsProbabilityMeasure α]
    {m : ℕ} (σ : CausalObservationPlan Bool Bool m)
    (u : WaitingQueryWorld → D → ℝ) (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) :
    bayesExperimentValue α (waitingQueryNativeKernel σ) u ≤
      Filter.liminf (fun t => bayesExperimentValue α (waitingQueryRecordKernel t) u) atTop :=
  waitingQuery_bayesValue_le_liminf α (waitingQueryNativeKernel σ) u hu

end Decision

end IdExp
