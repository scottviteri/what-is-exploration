import Formal.MeasureDeficiency

/-!
# Quantitative downstream readiness, including arbitrary priors

This module proves `prop:readiness` for arbitrary measurable source and
target signal spaces and arbitrary probability priors.  Only the downstream
decision set is finite.  Experiments and decision rules are genuine bundled
Markov kernels; the optimized value is the supremum over all such rules.
The proof integrates the sharp unit-range TV bound, composes rules, and then
passes through both optimization operations.  No optimal decoder is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace IdExp

variable {Θ X Y D : Type*}

/-- Forget only the parameter measurability of a Markov experiment, retaining
its probability rows for the measure-deficiency calculus. -/
noncomputable def kernelExperiment [MeasurableSpace Θ] [MeasurableSpace X]
    (E : FiniteMarkovKernel Θ X) : Θ → FiniteMeasure X := by
  let _ := E.isMarkov
  exact fun θ => ⟨E.toKernel θ, inferInstance⟩

instance isProbabilityMeasure_kernelExperiment
    [MeasurableSpace Θ] [MeasurableSpace X]
    (E : FiniteMarkovKernel Θ X) (θ : Θ) :
    IsProbabilityMeasure (kernelExperiment E θ : Measure X) := by
  have := E.isMarkov
  change IsProbabilityMeasure (E.toKernel θ)
  infer_instance

instance nonempty_finiteMarkovKernel [MeasurableSpace X] [MeasurableSpace D] [Nonempty D] :
    Nonempty (FiniteMarkovKernel X D) :=
  ⟨⟨Kernel.const X (Measure.dirac (Classical.arbitrary D)), inferInstance⟩⟩

/-- On a finite discrete space, general measure TV is the half-l1 distance
between the actual singleton masses. -/
theorem finiteMeasureTV_eq_finiteTV_singletons
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ ν : FiniteMeasure D) :
    finiteMeasureTV (μ : Measure D) (ν : Measure D) =
      finiteTV (fun d => (μ : Measure D).real {d}) (fun d => (ν : Measure D).real {d}) := by
  have hμ := finiteMeasureOfRow_eq_of_forall_singleton μ
    (fun d => (μ : Measure D).real {d}) (fun d =>
      (ENNReal.ofReal_toReal (measure_ne_top (μ : Measure D) {d})).symm)
  have hν := finiteMeasureOfRow_eq_of_forall_singleton ν
    (fun d => (ν : Measure D).real {d}) (fun d =>
      (ENNReal.ofReal_toReal (measure_ne_top (ν : Measure D) {d})).symm)
  calc
    _ = finiteMeasureTV
        (finiteMeasureOfRow (fun d => (μ : Measure D).real {d}) : Measure D)
        (finiteMeasureOfRow (fun d => (ν : Measure D).real {d}) : Measure D) := by
      exact finiteMeasureTV_congr _ _ _ _ (congrArg Subtype.val hμ) (congrArg Subtype.val hν)
    _ = _ := finiteMeasureTV_finiteMeasureOfRow _ _
      (fun _ => measureReal_nonneg) (fun _ => measureReal_nonneg)

theorem isDist_measureReal_singletons
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ : Measure D) [IsProbabilityMeasure μ] :
    IsDist (fun d => μ.real {d}) := by
  refine ⟨fun _ => measureReal_nonneg, ?_⟩
  have h := sum_measureReal_singleton (μ := μ) (Finset.univ : Finset D)
  rw [Finset.coe_univ] at h
  rw [h, measureReal_def, measure_univ, ENNReal.toReal_one]

/-- A unit-range decision payoff has the sharp measure-TV error bound. -/
theorem finiteLawPayoff_sub_le_TV
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ ν : FiniteMeasure D)
    [IsProbabilityMeasure (μ : Measure D)] [IsProbabilityMeasure (ν : Measure D)]
    (u : D → ℝ) (hu : ∀ d, u d ∈ Set.Icc (0 : ℝ) 1) :
    (∑ d, (μ : Measure D).real {d} * u d) -
      (∑ d, (ν : Measure D).real {d} * u d) ≤
        finiteMeasureTV (μ : Measure D) (ν : Measure D) := by
  rw [finiteMeasureTV_eq_finiteTV_singletons]
  exact expectation_sub_le_finiteTV _ _ u
    ((isDist_measureReal_singletons (μ : Measure D)).2.trans
      (isDist_measureReal_singletons (ν : Measure D)).2.symm)
    (fun d => (hu d).1) (fun d => (hu d).2)

section Values

variable [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y]
  [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D] [Nonempty D]

/-- Worldwise expected utility after one randomized decision rule. -/
noncomputable def bayesRulePayoff (E : FiniteMarkovKernel Θ X)
    (r : FiniteMarkovKernel X D) (u : Θ → D → ℝ) (θ : Θ) : ℝ :=
  ∑ d, (finiteMarkovDecode r (kernelExperiment E θ) : Measure D).real {d} * u θ d

theorem bayesRulePayoff_mem_unitInterval (E : FiniteMarkovKernel Θ X)
    (r : FiniteMarkovKernel X D) (u : Θ → D → ℝ)
    (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) (θ : Θ) :
    bayesRulePayoff E r u θ ∈ Set.Icc (0 : ℝ) 1 := by
  have := isProbabilityMeasure_finiteMarkovDecode r (kernelExperiment E θ)
  have hp := isDist_measureReal_singletons
    (finiteMarkovDecode r (kernelExperiment E θ) : Measure D)
  constructor
  · exact Finset.sum_nonneg fun d _ => mul_nonneg (hp.1 d) (hu θ d).1
  · calc
      _ ≤ ∑ d, (finiteMarkovDecode r (kernelExperiment E θ) : Measure D).real {d} :=
        Finset.sum_le_sum fun d _ => mul_le_of_le_one_right (hp.1 d) (hu θ d).2
      _ = 1 := hp.2

theorem measurable_bayesRulePayoff (E : FiniteMarkovKernel Θ X)
    (r : FiniteMarkovKernel X D) (u : Θ → D → ℝ)
    (hu : ∀ d, Measurable (fun θ => u θ d)) :
    Measurable (bayesRulePayoff E r u) := by
  change Measurable (fun θ => ∑ d,
    (((r.toKernel ∘ₖ E.toKernel) θ) {d}).toReal * u θ d)
  exact Finset.measurable_sum _ fun d _ =>
    (((r.toKernel ∘ₖ E.toKernel).measurable_coe (measurableSet_singleton d)).ennreal_toReal).mul
      (hu d)

theorem integrable_bayesRulePayoff (α : Measure Θ) [IsProbabilityMeasure α]
    (E : FiniteMarkovKernel Θ X) (r : FiniteMarkovKernel X D) (u : Θ → D → ℝ)
    (hum : ∀ d, Measurable (fun θ => u θ d))
    (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (bayesRulePayoff E r u) α := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_bayesRulePayoff E r u hum).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun θ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (bayesRulePayoff_mem_unitInterval E r u hu θ).1]
    exact (bayesRulePayoff_mem_unitInterval E r u hu θ).2

noncomputable def bayesRuleValue (α : Measure Θ) (E : FiniteMarkovKernel Θ X)
    (r : FiniteMarkovKernel X D) (u : Θ → D → ℝ) : ℝ :=
  ∫ θ, bayesRulePayoff E r u θ ∂α

theorem bayesRuleValue_mem_unitInterval (α : Measure Θ) [IsProbabilityMeasure α]
    (E : FiniteMarkovKernel Θ X) (r : FiniteMarkovKernel X D) (u : Θ → D → ℝ)
    (hum : ∀ d, Measurable (fun θ => u θ d))
    (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) :
    bayesRuleValue α E r u ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg fun θ => (bayesRulePayoff_mem_unitInterval E r u hu θ).1
  · calc
      _ ≤ ∫ _ : Θ, (1 : ℝ) ∂α := integral_mono
        (integrable_bayesRulePayoff α E r u hum hu) (integrable_const 1)
        (fun θ => (bayesRulePayoff_mem_unitInterval E r u hu θ).2)
      _ = 1 := by simp

/-- The optimized Bayesian value, over all measurable randomized rules. -/
noncomputable def bayesExperimentValue (α : Measure Θ)
    (E : FiniteMarkovKernel Θ X) (u : Θ → D → ℝ) : ℝ :=
  sSup (Set.range fun r : FiniteMarkovKernel X D => bayesRuleValue α E r u)

theorem bayesValue_range_bddAbove (α : Measure Θ) [IsProbabilityMeasure α]
    (E : FiniteMarkovKernel Θ X) (u : Θ → D → ℝ)
    (hum : ∀ d, Measurable (fun θ => u θ d))
    (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) :
    BddAbove (Set.range fun r : FiniteMarkovKernel X D => bayesRuleValue α E r u) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨r, rfl⟩
  exact (bayesRuleValue_mem_unitInterval α E r u hum hu).2

theorem bayesExperimentValue_mem_unitInterval (α : Measure Θ) [IsProbabilityMeasure α]
    (E : FiniteMarkovKernel Θ X) (u : Θ → D → ℝ)
    (hum : ∀ d, Measurable (fun θ => u θ d))
    (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) :
    bayesExperimentValue α E u ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · let r := Classical.arbitrary (FiniteMarkovKernel X D)
    exact (bayesRuleValue_mem_unitInterval α E r u hum hu).1.trans
      (le_csSup (bayesValue_range_bddAbove α E u hum hu) (Set.mem_range_self r))
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨r, rfl⟩
    exact (bayesRuleValue_mem_unitInterval α E r u hum hu).2

/-- Composing any target rule with a decoder of uniform error `c` loses at
most `c` in Bayesian value, for every probability prior. -/
theorem bayesRuleValue_sub_le_of_decoder (α : Measure Θ) [IsProbabilityMeasure α]
    (E : FiniteMarkovKernel Θ X) (F : FiniteMarkovKernel Θ Y)
    (G : FiniteMarkovKernel X Y) (r : FiniteMarkovKernel Y D) (u : Θ → D → ℝ)
    (hum : ∀ d, Measurable (fun θ => u θ d))
    (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) (c : ℝ)
    (herr : ∀ θ, finiteMeasureTV
      (finiteMarkovDecode G (kernelExperiment E θ) : Measure Y)
      (kernelExperiment F θ : Measure Y) ≤ c) :
    bayesRuleValue α F r u - bayesRuleValue α E (r.comp G) u ≤ c := by
  have hpoint (θ : Θ) : bayesRulePayoff F r u θ - bayesRulePayoff E (r.comp G) u θ ≤ c := by
    have := r.isMarkov
    have := isProbabilityMeasure_finiteMarkovDecode r (kernelExperiment F θ)
    have := isProbabilityMeasure_finiteMarkovDecode (r.comp G) (kernelExperiment E θ)
    have hpay := finiteLawPayoff_sub_le_TV
      (finiteMarkovDecode r (kernelExperiment F θ))
      (finiteMarkovDecode (r.comp G) (kernelExperiment E θ)) (u θ) (hu θ)
    apply hpay.trans
    rw [finiteMarkovDecode_comp]
    calc
      _ ≤ finiteMeasureTV (kernelExperiment F θ : Measure Y)
          (finiteMarkovDecode G (kernelExperiment E θ) : Measure Y) :=
        finiteMeasureTV_comp_le r.toKernel _ _
      _ = finiteMeasureTV (finiteMarkovDecode G (kernelExperiment E θ) : Measure Y)
          (kernelExperiment F θ : Measure Y) := finiteMeasureTV_symm _ _
      _ ≤ c := herr θ
  unfold bayesRuleValue
  rw [← integral_sub (integrable_bayesRulePayoff α F r u hum hu)
    (integrable_bayesRulePayoff α E (r.comp G) u hum hu)]
  calc
    _ ≤ ∫ _ : Θ, c ∂α := integral_mono
      ((integrable_bayesRulePayoff α F r u hum hu).sub
        (integrable_bayesRulePayoff α E (r.comp G) u hum hu))
      (integrable_const c) hpoint
    _ = c := by simp

/-- The optimized value loss is bounded by the actual decoder-infimum
definition of directed deficiency. -/
theorem bayesExperimentValue_sub_le_deficiency [Nonempty Θ] [Nonempty Y]
    (α : Measure Θ) [IsProbabilityMeasure α]
    (E : FiniteMarkovKernel Θ X) (F : FiniteMarkovKernel Θ Y) (u : Θ → D → ℝ)
    (hum : ∀ d, Measurable (fun θ => u θ d))
    (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) :
    bayesExperimentValue α F u - bayesExperimentValue α E u ≤
      finiteMeasureDeficiency (kernelExperiment E) (kernelExperiment F) := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨G, hG⟩ := exists_finiteMarkovDecoder_le_add_of_nonempty
    (kernelExperiment E) (kernelExperiment F)
    (finiteMeasureDeficiencyCandidates_nonempty_of_prob _ _
      (fun _ => inferInstance) (fun _ => inferInstance)) hη
  have hvalue : bayesExperimentValue α F u ≤ bayesExperimentValue α E u +
      (finiteMeasureDeficiency (kernelExperiment E) (kernelExperiment F) + η) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨r, rfl⟩
    have hr := bayesRuleValue_sub_le_of_decoder α E F G r u hum hu _ hG
    have hsup := le_csSup (bayesValue_range_bddAbove α E u hum hu)
      (Set.mem_range_self (r.comp G))
    change bayesRuleValue α E (r.comp G) u ≤ bayesExperimentValue α E u at hsup
    linarith
  linarith

/-- The literal finite-decision readiness inequality in the paper. -/
theorem bayesExperimentValue_readiness [Nonempty Θ] [Nonempty Y]
    (α : Measure Θ) [IsProbabilityMeasure α]
    (E : FiniteMarkovKernel Θ X) (F : FiniteMarkovKernel Θ Y) (u : Θ → D → ℝ)
    (hum : ∀ d, Measurable (fun θ => u θ d))
    (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ}
    (hε : finiteMeasureDeficiency (kernelExperiment E) (kernelExperiment F) ≤ ε) :
    bayesExperimentValue α F u - ε ≤ bayesExperimentValue α E u := by
  have h := bayesExperimentValue_sub_le_deficiency α E F u hum hu
  linarith

/-- Process readiness permits the acquired signal type to grow with time.
The target experiment, prior, and bounded decision problem are held fixed. -/
theorem bayesExperimentValue_le_liminf [Nonempty Θ] [Nonempty Y]
    {Xt : ℕ → Type*} [∀ t, MeasurableSpace (Xt t)]
    (α : Measure Θ) [IsProbabilityMeasure α]
    (E : ∀ t, FiniteMarkovKernel Θ (Xt t)) (F : FiniteMarkovKernel Θ Y)
    (u : Θ → D → ℝ) (hum : ∀ d, Measurable (fun θ => u θ d))
    (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1)
    (hδ : Tendsto (fun t => finiteMeasureDeficiency (kernelExperiment (E t))
      (kernelExperiment F)) atTop (𝓝 0)) :
    bayesExperimentValue α F u ≤
      Filter.liminf (fun t => bayesExperimentValue α (E t) u) atTop := by
  have hbound t := bayesExperimentValue_mem_unitInterval α (E t) u hum hu
  apply (Filter.le_liminf_iff'
    (f := (atTop : Filter ℕ))
    (u := fun t : ℕ => bayesExperimentValue α (E t) u)
    (Filter.isCoboundedUnder_ge_of_le (atTop : Filter ℕ)
      (fun t : ℕ => (hbound t).2))
    (Filter.isBoundedUnder_of ⟨0, fun t : ℕ => (hbound t).1⟩)).2
  intro b hb
  have hpos : 0 < bayesExperimentValue α F u - b := sub_pos.mpr hb
  filter_upwards [(tendsto_order.mp hδ).2 _ hpos] with t ht
  have h := bayesExperimentValue_readiness α (E t) F u hum hu ht.le
  linarith

end Values

end IdExp
