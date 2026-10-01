import Formal.MeasureDeficiencyCore
import Formal.MeasureDensity
import Formal.BlackwellConverse
import Formal.DualCertificate

/-!
# Total variation and directed deficiency for finite-measure experiments

`DominatedPrefix.lean` defines `finiteMeasureTV` (one half of the total
variation of the signed difference) and `finiteMeasureDeficiency` (the
infimum of uniform decoder errors over bundled Markov kernels) for
experiments whose signal spaces are arbitrary measurable spaces.  It uses
them only through two facts: a displayed decoder bounds the deficiency from
above, and the candidate set is bounded below by zero.

This module supplies the calculus the finite-prefix-to-terminal recovery
wrapper needs on top of those definitions, at the level of general
measurable spaces wherever the statements make sense:

* total variation: `finiteMeasureTV_self`, `finiteMeasureTV_symm`,
  `finiteMeasureTV_triangle`, the mass bound
  `finiteMeasureTV_le_half_add_mass` (hence `finiteMeasureTV_le_one` for
  probability measures), and **data processing**
  `finiteMeasureTV_comp_le` under any Markov kernel (proved through the
  Jordan decomposition of the signed difference), with the deterministic
  special case `finiteMeasureTV_map_le`;
* directed deficiency: the positive-eta approximation
  `exists_finiteMarkovDecoder_le_add_of_nonempty`, the triangle inequality
  `finiteMeasureDeficiency_triangle_of_nonempty`, **source garbling**
  `finiteMeasureDeficiency_le_of_source_garbling` (deficiency from a source
  is at most the deficiency from any exact garbling of that source:
  candidate-set inclusion, no data processing needed), **target garbling**
  `finiteMeasureDeficiency_mono_target` (garbling the target cannot
  increase deficiency; this is where data processing enters),
  `finiteMeasureDeficiency_garbling_eq_zero`, nonnegativity, and the bound
  by one for probability experiments;
* the finite discrete bridge: `finiteMeasureOfRow` turns a real row into a
  finite measure with those singleton masses, Markov kernels act on it by
  matrix multiplication with `ruleMatrix`, and
  `finiteMeasureDeficiency_eq_finiteDeficiency` identifies the general
  measure deficiency with the matrix deficiency `finiteDeficiency` of
  `DualCertificate.lean` for valid finite experiments (both inequalities,
  via equality of the candidate sets).

As in `DeficiencyTriangle.lean`, the real infimum convention `sInf ∅ = 0`
means the triangle and monotonicity statements need nonempty candidate
sets; these are explicit hypotheses in the general statements and are
discharged automatically for probability experiments by
`finiteMeasureDeficiencyCandidates_nonempty_of_prob`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace IdExp

/-! ## Finite discrete signal spaces: measure deficiency is matrix deficiency -/

section FiniteBridge

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The finite measure on a finite discrete type whose singleton masses are
the entries of a real row (negative entries clipped to zero): the density
`ENNReal.ofReal ∘ p` against counting measure. -/
noncomputable def finiteMeasureOfRow (p : X → ℝ) : FiniteMeasure X :=
  withDensityOfRealFinite Measure.count p Integrable.of_finite

theorem finiteMeasureOfRow_singleton (p : X → ℝ) (x : X) :
    (finiteMeasureOfRow p : Measure X) {x} = ENNReal.ofReal (p x) := by
  show (Measure.count.withDensity fun x => ENNReal.ofReal (p x)) {x} = _
  rw [withDensity_apply _ (measurableSet_singleton x), lintegral_singleton,
    Measure.count_singleton, mul_one]

/-- A finite measure on a finite discrete type is determined by its
singleton masses; matching them to a row identifies it with
`finiteMeasureOfRow`. -/
theorem finiteMeasureOfRow_eq_of_forall_singleton (μ : FiniteMeasure X) (p : X → ℝ)
    (h : ∀ x, (μ : Measure X) {x} = ENNReal.ofReal (p x)) :
    μ = finiteMeasureOfRow p := by
  apply FiniteMeasure.toMeasure_injective
  rw [Measure.ext_iff_singleton]
  intro x
  rw [h x, finiteMeasureOfRow_singleton]

theorem finiteMeasureOfRow_univ (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) :
    (finiteMeasureOfRow p : Measure X) Set.univ = ENNReal.ofReal (∑ x, p x) := by
  show (Measure.count.withDensity fun x => ENNReal.ofReal (p x)) Set.univ = _
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count,
    tsum_fintype, ENNReal.ofReal_sum_of_nonneg (fun x _ => hp x)]

theorem isProbabilityMeasure_finiteMeasureOfRow (p : X → ℝ) (hp : IsDist p) :
    IsProbabilityMeasure (finiteMeasureOfRow p : Measure X) := by
  constructor
  rw [finiteMeasureOfRow_univ p hp.1, hp.2, ENNReal.ofReal_one]

/-- On finite discrete types the general total variation of the row
measures is the matrix total variation `finiteTV`. -/
theorem finiteMeasureTV_finiteMeasureOfRow (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    finiteMeasureTV (finiteMeasureOfRow p : Measure X) (finiteMeasureOfRow q : Measure X) =
      finiteTV p q := by
  have h := finiteMeasureTV_withDensity_ofReal (Measure.count : Measure X) p q
    (measurable_of_countable p).stronglyMeasurable
    (measurable_of_countable q).stronglyMeasurable
    Integrable.of_finite Integrable.of_finite
    (Filter.Eventually.of_forall hp) (Filter.Eventually.of_forall hq)
  rw [integral_count] at h
  exact h

variable {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- A Markov kernel between finite discrete types acts on row measures by
right multiplication with its stochastic matrix `ruleMatrix`. -/
theorem comp_finiteMeasureOfRow (r : Kernel X Y) [IsMarkovKernel r] (p : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) :
    r ∘ₘ (finiteMeasureOfRow p : Measure X) =
      finiteMeasureOfRow (fun y => ∑ x, p x * ruleMatrix r x y) := by
  rw [Measure.ext_iff_singleton]
  intro y
  rw [finiteMeasureOfRow_singleton,
    Measure.bind_apply (measurableSet_singleton y) (Kernel.aemeasurable r)]
  show ∫⁻ x, r x {y} ∂(Measure.count.withDensity fun x => ENNReal.ofReal (p x)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
    (Kernel.measurable_coe r (measurableSet_singleton y)), lintegral_count, tsum_fintype]
  have hnn : ∀ x ∈ (Finset.univ : Finset X), 0 ≤ p x * ruleMatrix r x y := fun x _ =>
    mul_nonneg (hp x) (by unfold ruleMatrix; exact measureReal_nonneg)
  rw [ENNReal.ofReal_sum_of_nonneg hnn]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.mul_apply, ruleMatrix]
  rw [ENNReal.ofReal_mul (hp x), measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The kernel of a stochastic matrix acts on row measures by that matrix. -/
theorem kernelOfMatrix_comp_finiteMeasureOfRow (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) :
    kernelOfMatrix G ∘ₘ (finiteMeasureOfRow p : Measure X) =
      finiteMeasureOfRow (fun y => ∑ x, p x * G x y) := by
  have := isMarkovKernel_kernelOfMatrix G hG
  rw [comp_finiteMeasureOfRow _ p hp, ruleMatrix_kernelOfMatrix G hG]

/-- Row experiments: every finite experiment matrix, read row by row as a
family of finite measures on the discrete signal space. -/
noncomputable def rowExperiment {Θ : Type*} (E : FiniteExperiment Θ X) : Θ → FiniteMeasure X :=
  fun θ => finiteMeasureOfRow (E θ)

omit [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y]
  [MeasurableSingletonClass Y] in
theorem finiteDecisionLaw_nonneg {Θ : Type*} (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) (θ : Θ)
    (y : Y) : 0 ≤ finiteDecisionLaw E G θ y :=
  Finset.sum_nonneg fun x _ => mul_nonneg ((hE θ).1 x) ((hG x (Set.mem_univ x)).1 y)

/-- Decoding a valid row experiment through a bundled Markov kernel is the
row experiment of the matrix decision law of its `ruleMatrix`. -/
theorem finiteMarkovDecode_rowExperiment {Θ : Type*} (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (G : FiniteMarkovKernel X Y) (θ : Θ) :
    (finiteMarkovDecode G (rowExperiment E θ) : Measure Y) =
      finiteMeasureOfRow (finiteDecisionLaw E (ruleMatrix G.toKernel) θ) := by
  have := G.isMarkov
  exact comp_finiteMeasureOfRow G.toKernel (E θ) fun x => (hE θ).1 x

/-- **Candidate sets agree on finite discrete types.**  A stochastic matrix
and its Markov kernel decode a valid row experiment to the same law, so the
uniform-error candidate sets of `finiteMeasureDeficiency` and
`finiteDeficiency` coincide. -/
theorem finiteMeasureDeficiencyCandidates_rowExperiment {Θ : Type*}
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    finiteMeasureDeficiencyCandidates (rowExperiment E) (rowExperiment F) =
      finiteDeficiencyCandidates E F := by
  ext c
  constructor
  · rintro ⟨G, herr⟩
    have hM := G.isMarkov
    refine ⟨ruleMatrix G.toKernel, ruleMatrix_mem_stochasticRules G.toKernel, fun θ => ?_⟩
    have hdec := finiteMarkovDecode_rowExperiment E hE G θ
    calc decodeErr E F (ruleMatrix G.toKernel) θ
        = finiteTV (finiteDecisionLaw E (ruleMatrix G.toKernel) θ) (F θ) := rfl
      _ = finiteMeasureTV
            (finiteMeasureOfRow (finiteDecisionLaw E (ruleMatrix G.toKernel) θ) : Measure Y)
            (finiteMeasureOfRow (F θ) : Measure Y) :=
          (finiteMeasureTV_finiteMeasureOfRow _ _
            (finiteDecisionLaw_nonneg E hE _ (ruleMatrix_mem_stochasticRules G.toKernel) θ)
            (hF θ).1).symm
      _ = finiteMeasureTV (finiteMarkovDecode G (rowExperiment E θ) : Measure Y)
            (rowExperiment F θ : Measure Y) :=
          finiteMeasureTV_congr _ _ _ _ hdec.symm rfl
      _ ≤ c := herr θ
  · rintro ⟨G, hG, herr⟩
    let K : FiniteMarkovKernel X Y := ⟨kernelOfMatrix G, isMarkovKernel_kernelOfMatrix G hG⟩
    refine ⟨K, fun θ => ?_⟩
    have hdec : (finiteMarkovDecode K (rowExperiment E θ) : Measure Y) =
        finiteMeasureOfRow (finiteDecisionLaw E G θ) :=
      kernelOfMatrix_comp_finiteMeasureOfRow G hG (E θ) fun x => (hE θ).1 x
    calc finiteMeasureTV (finiteMarkovDecode K (rowExperiment E θ) : Measure Y)
          (rowExperiment F θ : Measure Y)
        = finiteMeasureTV (finiteMeasureOfRow (finiteDecisionLaw E G θ) : Measure Y)
            (finiteMeasureOfRow (F θ) : Measure Y) :=
          finiteMeasureTV_congr _ _ _ _ hdec rfl
      _ = finiteTV (finiteDecisionLaw E G θ) (F θ) :=
          finiteMeasureTV_finiteMeasureOfRow _ _
            (finiteDecisionLaw_nonneg E hE G hG θ) (hF θ).1
      _ ≤ c := herr θ

/-- **Measure deficiency is matrix deficiency on finite discrete types.**
For valid finite experiments the general Markov-kernel deficiency of
`DominatedPrefix.lean` applied to the row measures equals the stochastic-
matrix deficiency `finiteDeficiency` of `DualCertificate.lean`. -/
theorem finiteMeasureDeficiency_eq_finiteDeficiency {Θ : Type*}
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    finiteMeasureDeficiency (rowExperiment E) (rowExperiment F) = finiteDeficiency E F := by
  unfold finiteMeasureDeficiency finiteDeficiency
  rw [finiteMeasureDeficiencyCandidates_rowExperiment E F hE hF]

theorem finiteMeasureDeficiency_le_finiteDeficiency {Θ : Type*}
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    finiteMeasureDeficiency (rowExperiment E) (rowExperiment F) ≤ finiteDeficiency E F :=
  (finiteMeasureDeficiency_eq_finiteDeficiency E F hE hF).le

theorem finiteDeficiency_le_finiteMeasureDeficiency {Θ : Type*}
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    finiteDeficiency E F ≤ finiteMeasureDeficiency (rowExperiment E) (rowExperiment F) :=
  (finiteMeasureDeficiency_eq_finiteDeficiency E F hE hF).ge

/-- Unfolded form of the identification, with the row measures displayed. -/
theorem finiteMeasureDeficiency_finiteMeasureOfRow_eq_finiteDeficiency {Θ : Type*}
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    finiteMeasureDeficiency (fun θ => finiteMeasureOfRow (E θ))
      (fun θ => finiteMeasureOfRow (F θ)) = finiteDeficiency E F :=
  finiteMeasureDeficiency_eq_finiteDeficiency E F hE hF

end FiniteBridge

/-! ## Finite matrix garblings as measurable kernels -/

/-- A finite stochastic matrix realizing a garbling also realizes that
garbling between the corresponding probability-measure experiments. -/
theorem exists_finiteMarkovKernel_of_finiteBlackwellLE
    {Θ Y Z : Type*} [Fintype Y] [Fintype Z]
    [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSingletonClass Y] [MeasurableSingletonClass Z]
    (F : FiniteExperiment Θ Y) (D : FiniteExperiment Θ Z)
    (hD : IsFiniteExperiment D) (hFD : FiniteBlackwellLE F D) :
    ∃ H : FiniteMarkovKernel Z Y,
      ∀ θ, finiteMarkovDecode H (rowExperiment D θ) = rowExperiment F θ := by
  obtain ⟨G, hG, hGF⟩ := hFD
  refine ⟨⟨kernelOfMatrix G, isMarkovKernel_kernelOfMatrix G hG⟩, ?_⟩
  intro θ
  apply Subtype.ext
  change kernelOfMatrix G ∘ₘ (finiteMeasureOfRow (D θ) : Measure Z) =
    (finiteMeasureOfRow (F θ) : Measure Y)
  rw [kernelOfMatrix_comp_finiteMeasureOfRow G hG (D θ) (hD θ).1]
  exact congrArg (fun p => (finiteMeasureOfRow p : Measure Y)) (congrFun hGF θ)

/-- Finite Blackwell-equivalent targets have equal deficiency from an
arbitrary measurable probability experiment. -/
theorem finiteMeasureDeficiency_row_target_eq_of_blackwellEquiv
    {Θ X Y Z : Type*} [Nonempty Θ] [Fintype Y] [Fintype Z]
    [Nonempty Y] [Nonempty Z]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSingletonClass Y] [MeasurableSingletonClass Z]
    (E : Θ → FiniteMeasure X)
    (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X))
    (F : FiniteExperiment Θ Y) (D : FiniteExperiment Θ Z)
    (hF : IsFiniteExperiment F) (hD : IsFiniteExperiment D)
    (hFD : FiniteBlackwellLE F D) (hDF : FiniteBlackwellLE D F) :
    finiteMeasureDeficiency E (rowExperiment F) =
      finiteMeasureDeficiency E (rowExperiment D) := by
  obtain ⟨H, hH⟩ := exists_finiteMarkovKernel_of_finiteBlackwellLE F D hD hFD
  obtain ⟨G, hG⟩ := exists_finiteMarkovKernel_of_finiteBlackwellLE D F hF hDF
  exact le_antisymm
    (finiteMeasureDeficiency_mono_target_of_prob E (rowExperiment D) (rowExperiment F)
      H hH hE (fun θ => isProbabilityMeasure_finiteMeasureOfRow _ (hD θ)))
    (finiteMeasureDeficiency_mono_target_of_prob E (rowExperiment F) (rowExperiment D)
      G hG hE (fun θ => isProbabilityMeasure_finiteMeasureOfRow _ (hF θ)))

end IdExp
