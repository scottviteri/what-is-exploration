import Formal.FullRevelation

/-!
# Negative deficiency to full revelation

This is the actual randomized-decoder Le Cam objective, not deterministic
classification error. On a finite nonempty class, its value is at most zero,
and it equals zero exactly when a measurable decoder recovers the class
almost surely. If a feasible experiment attains full revelation, the
maximizers are therefore exactly the identifying experiments.

The source signal space is arbitrary measurable. No prior or optimizer
attainment assumption is used; finite-label exact attainment is proved in
`FullRevelation.lean`. The causal-policy specialization lives separately in
`CausalDeficiencyObjective.lean`.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory

variable {Θ : Type*} [Fintype Θ] [Nonempty Θ]
  [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  {X : Type*} [MeasurableSpace X]

/-- Negative directed Le Cam deficiency to the exact class-label experiment.
The infimum inside the deficiency ranges over randomized Markov decoders. -/
noncomputable def negativeExactLabelDeficiency (E : Θ → FiniteMeasure X) : ℝ :=
  -finiteMeasureDeficiency E (exactLabelExperiment Θ)

omit [Fintype Θ] [Nonempty Θ] [MeasurableSingletonClass Θ] in
private theorem label_probability (θ : Θ) :
    IsProbabilityMeasure (exactLabelExperiment Θ θ : Measure Θ) := by
  change IsProbabilityMeasure (Measure.dirac θ)
  infer_instance

omit [Fintype Θ] [MeasurableSingletonClass Θ] in
theorem negativeExactLabelDeficiency_nonpos
    (E : Θ → FiniteMeasure X) (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X)) :
    negativeExactLabelDeficiency E ≤ 0 :=
  neg_nonpos.mpr (finiteMeasureDeficiency_nonneg_of_prob E
    (exactLabelExperiment Θ) hE label_probability)

omit [Fintype Θ] [MeasurableSingletonClass Θ] in
theorem neg_one_le_negativeExactLabelDeficiency
    (E : Θ → FiniteMeasure X) (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X)) :
    -1 ≤ negativeExactLabelDeficiency E :=
  neg_le_neg (finiteMeasureDeficiency_le_one_of_prob E
    (exactLabelExperiment Θ) hE label_probability)

theorem negativeExactLabelDeficiency_eq_zero_iff_decoder
    (E : Θ → FiniteMeasure X) (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X)) :
    negativeExactLabelDeficiency E = 0 ↔ ∃ D : X → Θ, MeasurableExactDecoder E D := by
  rw [negativeExactLabelDeficiency, neg_eq_zero,
    finiteMeasureDeficiency_exactLabel_eq_zero_iff_decoder E hE]

omit [Fintype Θ] [MeasurableSingletonClass Θ] in
/-- The objective cannot increase when the collected experiment is garbled.
The source spaces may differ and need not be finite or standard Borel. -/
theorem negativeExactLabelDeficiency_mono_blackwell
    {Y : Type*} [MeasurableSpace Y]
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y)
    (hF : ∀ θ, IsProbabilityMeasure (F θ : Measure Y))
    (h : BlackwellLE (fun θ => (F θ : Measure Y)) (fun θ => (E θ : Measure X))) :
    negativeExactLabelDeficiency F ≤ negativeExactLabelDeficiency E := by
  obtain ⟨κ, hκ, hκE⟩ := h
  apply neg_le_neg
  exact finiteMeasureDeficiency_le_of_source_garbling_of_prob E F ⟨κ, hκ⟩
    (fun θ => Subtype.ext (hκE θ)) (exactLabelExperiment Θ) hF label_probability

/-- Exact maximizer characterization for any family of feasible experiments.
Existence of one identifying experiment is essential; it is not inferred from
finiteness of the class. -/
theorem negativeExactLabelDeficiency_maximizer_iff
    {I : Type*} (E : I → Θ → FiniteMeasure X)
    (hE : ∀ i θ, IsProbabilityMeasure (E i θ : Measure X))
    (hattain : ∃ i, ∃ D : X → Θ, MeasurableExactDecoder (E i) D) (i : I) :
    (∀ j, negativeExactLabelDeficiency (E j) ≤ negativeExactLabelDeficiency (E i)) ↔
      ∃ D : X → Θ, MeasurableExactDecoder (E i) D := by
  constructor
  · intro hmax
    obtain ⟨j, hj⟩ := hattain
    have hzero := (negativeExactLabelDeficiency_eq_zero_iff_decoder (E j) (hE j)).2 hj
    apply (negativeExactLabelDeficiency_eq_zero_iff_decoder (E i) (hE i)).1
    exact le_antisymm (negativeExactLabelDeficiency_nonpos (E i) (hE i))
      (hzero ▸ hmax j)
  · intro hi j
    rw [(negativeExactLabelDeficiency_eq_zero_iff_decoder (E i) (hE i)).2 hi]
    exact negativeExactLabelDeficiency_nonpos (E j) (hE j)

end IdExp
