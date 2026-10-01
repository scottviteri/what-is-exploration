import Formal.ExactLabelDeficiency

/-!
# Full revelation on a finite class with arbitrary measurable signals

This is measure-level recovery infrastructure, independent of POMDPs and of
the causal encoding. For finite nonempty classes, exact label garbling,
measurable almost-sure class decoding, and pairwise mutual singularity are
equivalent. The source signal space need not be finite or standard Borel.
Zero directed deficiency to these finite labels also attains an exact
garbling; this special-target fact is not an attainment theorem for arbitrary
terminal experiment targets.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {Θ X : Type*} [MeasurableSpace X]

/-- The converse to the singular-probability TV identity, on any measurable
space. Equality in the variation mass bound makes the original measures the
positive and negative Jordan parts. -/
theorem mutuallySingular_of_finiteMeasureTV_eq_one
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : finiteMeasureTV μ ν = 1) : μ ⟂ₘ ν := by
  let s : SignedMeasure X := μ.toSignedMeasure - ν.toSignedMeasure
  let j : JordanDecomposition X := s.toJordanDecomposition
  have hmass : s.totalVariation.real univ = 2 := by
    change (1 / 2 : ℝ) * s.totalVariation.real univ = 1 at h
    linarith
  have hmass' : s.totalVariation univ = (μ + ν) univ := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top s.totalVariation univ) (measure_ne_top (μ + ν) univ)).mp
    change s.totalVariation.real univ = (μ + ν).real univ
    rw [hmass, measureReal_add_apply, probReal_univ (μ := μ), probReal_univ (μ := ν)]
    norm_num
  have hvar : s.totalVariation = μ + ν :=
    Measure.eq_of_le_of_measure_univ_eq (totalVariation_sub_le μ ν) hmass'
  have hsum : j.posPart.toSignedMeasure + j.negPart.toSignedMeasure =
      μ.toSignedMeasure + ν.toSignedMeasure := by
    rw [← Measure.toSignedMeasure_add, ← Measure.toSignedMeasure_add]
    exact Measure.toSignedMeasure_congr hvar
  have hdiff : j.posPart.toSignedMeasure - j.negPart.toSignedMeasure =
      μ.toSignedMeasure - ν.toSignedMeasure :=
    SignedMeasure.toSignedMeasure_toJordanDecomposition s
  have hp : j.posPart = μ := by
    apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
    ext z hz
    have ha := congrArg (fun u : SignedMeasure X => u z) hsum
    have hb := congrArg (fun u : SignedMeasure X => u z) hdiff
    change j.posPart.toSignedMeasure z + j.negPart.toSignedMeasure z =
      μ.toSignedMeasure z + ν.toSignedMeasure z at ha
    change j.posPart.toSignedMeasure z - j.negPart.toSignedMeasure z =
      μ.toSignedMeasure z - ν.toSignedMeasure z at hb
    linarith
  have hn : j.negPart = ν := by
    apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
    ext z hz
    have ha := congrArg (fun u : SignedMeasure X => u z) hsum
    have hb := congrArg (fun u : SignedMeasure X => u z) hdiff
    change j.posPart.toSignedMeasure z + j.negPart.toSignedMeasure z =
      μ.toSignedMeasure z + ν.toSignedMeasure z at ha
    change j.posPart.toSignedMeasure z - j.negPart.toSignedMeasure z =
      μ.toSignedMeasure z - ν.toSignedMeasure z at hb
    linarith
  simpa only [hp, hn] using j.mutuallySingular

theorem finiteMeasureTV_eq_one_iff_mutuallySingular
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    finiteMeasureTV μ ν = 1 ↔ μ ⟂ₘ ν :=
  ⟨mutuallySingular_of_finiteMeasureTV_eq_one μ ν,
    finiteMeasureTV_eq_one_of_mutuallySingular μ ν⟩

variable [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

/-- One measurable class-valued decoder with zero error under every world. -/
def MeasurableExactDecoder (E : Θ → FiniteMeasure X) (D : X → Θ) : Prop :=
  Measurable D ∧ ∀ θ, (E θ : Measure X) {x | D x ≠ θ} = 0

/-- Zero error and probability-one correct identification are the same
literal condition under probability class laws. -/
theorem measurableExactDecoder_iff_correct_probability_one
    (E : Θ → FiniteMeasure X) (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X))
    (D : X → Θ) :
    MeasurableExactDecoder E D ↔
      Measurable D ∧ ∀ θ, (E θ : Measure X) {x | D x = θ} = 1 := by
  constructor
  · rintro ⟨hD, herr⟩
    refine ⟨hD, fun θ => ?_⟩
    have := hE θ
    exact (prob_compl_eq_zero_iff (hD (measurableSet_singleton θ))).1 (herr θ)
  · rintro ⟨hD, hcorrect⟩
    refine ⟨hD, fun θ => ?_⟩
    have := hE θ
    exact (prob_compl_eq_zero_iff (hD (measurableSet_singleton θ))).2 (hcorrect θ)

/-- Pairwise singular finite families have measurable class carriers. -/
theorem exists_finite_measurable_carriers (E : Θ → FiniteMeasure X)
    (hsing : Pairwise fun θ η => (E θ : Measure X) ⟂ₘ (E η : Measure X)) :
    ∃ S : Θ → Set X, (∀ θ, MeasurableSet (S θ)) ∧
      (∀ θ, (E θ : Measure X) (S θ)ᶜ = 0) ∧
      ∀ θ η, η ≠ θ → (E η : Measure X) (S θ) = 0 := by
  refine ⟨fun θ => ⋂ η : {η : Θ // η ≠ θ}, (hsing η.2).nullSet,
    fun θ => MeasurableSet.iInter fun η => (hsing η.2).measurableSet_nullSet,
    fun θ => ?_, fun θ η hη => ?_⟩
  · rw [Set.compl_iInter]
    exact measure_iUnion_null fun η => (hsing η.2).measure_compl_nullSet
  · exact measure_mono_null (Set.iInter_subset _ ⟨η, hη⟩)
      (hsing hη).measure_nullSet

/-- A measurable selector for finitely many disjoint measurable sets; its
value off the union is an arbitrary fixed class. -/
theorem exists_finite_measurable_selector [Nonempty Θ]
    (S : Θ → Set X) (hS : ∀ θ, MeasurableSet (S θ))
    (hdisj : Pairwise fun θ η => Disjoint (S θ) (S η)) :
    ∃ D : X → Θ, Measurable D ∧ ∀ θ, ∀ x ∈ S θ, D x = θ := by
  classical
  let θ₀ : Θ := Classical.arbitrary Θ
  let D : X → Θ := fun x => if h : ∃ θ, x ∈ S θ then h.choose else θ₀
  have hsel : ∀ θ, ∀ x ∈ S θ, D x = θ := by
    intro θ x hx
    have h : ∃ θ, x ∈ S θ := ⟨θ, hx⟩
    simp only [D, dif_pos h]
    by_contra hne
    exact Set.disjoint_left.1 (hdisj hne) h.choose_spec hx
  have hpre : ∀ θ, D ⁻¹' {θ} = S θ ∪ ({x | ∀ η, x ∉ S η} ∩ {_x | θ = θ₀}) := by
    intro θ
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hθ
      by_cases h : ∃ η, x ∈ S η
      · obtain ⟨η, hη⟩ := h
        left
        rw [← hθ, hsel η x hη]
        exact hη
      · right
        refine ⟨fun η hη => h ⟨η, hη⟩, ?_⟩
        rw [← hθ]
        simp only [D, dif_neg h]
    · rintro (hθ | ⟨hno, rfl⟩)
      · exact hsel θ x hθ
      · simp only [D, dif_neg (not_exists.2 hno)]
  refine ⟨D, measurable_to_countable' fun θ => ?_, hsel⟩
  rw [hpre θ]
  refine (hS θ).union (MeasurableSet.inter ?_ (MeasurableSet.const _))
  have : {x : X | ∀ θ, x ∉ S θ} = (⋃ θ, S θ)ᶜ := by
    ext x
    simp
  rw [this]
  exact (MeasurableSet.iUnion hS).compl

theorem exists_measurableExactDecoder_of_pairwise_mutuallySingular [Nonempty Θ]
    (E : Θ → FiniteMeasure X)
    (hsing : Pairwise fun θ η => (E θ : Measure X) ⟂ₘ (E η : Measure X)) :
    ∃ D : X → Θ, MeasurableExactDecoder E D := by
  classical
  obtain ⟨S, hSmeas, hSfull, hSnull⟩ := exists_finite_measurable_carriers E hsing
  let S' : Θ → Set X := fun θ => S θ \ ⋃ η, ⋃ (_ : η ≠ θ), S η
  have hS'meas : ∀ θ, MeasurableSet (S' θ) := fun θ =>
    (hSmeas θ).diff (MeasurableSet.iUnion fun η => MeasurableSet.iUnion fun _ => hSmeas η)
  have hS'disj : Pairwise fun θ η => Disjoint (S' θ) (S' η) := by
    intro θ η hθη
    rw [Set.disjoint_left]
    rintro x ⟨hxθ, -⟩ ⟨-, hxη⟩
    exact hxη (Set.mem_iUnion.2 ⟨θ, Set.mem_iUnion.2 ⟨hθη, hxθ⟩⟩)
  have hS'full : ∀ θ, (E θ : Measure X) (S' θ)ᶜ = 0 := by
    intro θ
    have hsub : (S' θ)ᶜ ⊆ (S θ)ᶜ ∪ ⋃ η, ⋃ (_ : η ≠ θ), S η := by
      intro x hx
      by_cases hθ : x ∈ S θ
      · right
        by_contra hU
        exact hx ⟨hθ, hU⟩
      · exact Or.inl hθ
    refine measure_mono_null hsub (measure_union_null (hSfull θ) ?_)
    exact measure_iUnion_null fun η => measure_iUnion_null fun hη => hSnull η θ hη.symm
  obtain ⟨D, hD, hsel⟩ := exists_finite_measurable_selector S' hS'meas hS'disj
  refine ⟨D, hD, fun θ => measure_mono_null (fun x hx => ?_) (hS'full θ)⟩
  intro hxθ
  exact hx (hsel θ x hxθ)

theorem pairwise_mutuallySingular_of_measurableExactDecoder
    (E : Θ → FiniteMeasure X) (D : X → Θ) (hD : MeasurableExactDecoder E D) :
    Pairwise fun θ η => (E θ : Measure X) ⟂ₘ (E η : Measure X) := by
  intro θ η hθη
  refine ⟨{x | D x ≠ θ}, (hD.1 (measurableSet_singleton θ)).compl, hD.2 θ, ?_⟩
  apply measure_mono_null ?_ (hD.2 η)
  intro x hx hη
  have hθ : D x = θ := by simpa only [mem_compl_iff, mem_ofPred_eq, not_not] using hx
  exact hθη (hθ.symm.trans hη)

theorem exists_measurableExactDecoder_iff_pairwise_mutuallySingular [Nonempty Θ]
    (E : Θ → FiniteMeasure X) :
    (∃ D : X → Θ, MeasurableExactDecoder E D) ↔
      Pairwise fun θ η => (E θ : Measure X) ⟂ₘ (E η : Measure X) :=
  ⟨fun ⟨D, hD⟩ => pairwise_mutuallySingular_of_measurableExactDecoder E D hD,
    exists_measurableExactDecoder_of_pairwise_mutuallySingular E⟩

/-- A deterministic exact decoder is in particular an exact Blackwell
garbling into the finite label experiment. -/
theorem blackwellLE_exactLabel_of_measurableExactDecoder
    (E : Θ → FiniteMeasure X) (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X))
    (D : X → Θ) (hD : MeasurableExactDecoder E D) :
    BlackwellLE (fun θ => Measure.dirac θ) (fun θ => (E θ : Measure X)) := by
  obtain ⟨hmeas, herr⟩ := hD
  refine ⟨Kernel.deterministic D hmeas, inferInstance, fun θ => ?_⟩
  have := hE θ
  ext S hS
  rw [Measure.bind_apply hS (Kernel.measurable _).aemeasurable]
  have hae : ∀ᵐ x ∂(E θ : Measure X), D x = θ := by
    rw [ae_iff]
    exact herr θ
  have hrow : ∀ᵐ x ∂(E θ : Measure X),
      Kernel.deterministic D hmeas x S = Measure.dirac θ S := by
    filter_upwards [hae] with x hx
    rw [Kernel.deterministic_apply, hx]
  rw [lintegral_congr_ae hrow, lintegral_const, measure_univ, mul_one]

/-- Two different measurable labels have total variation one. -/
theorem finiteMeasureTV_dirac_dirac (θ η : Θ) (hne : θ ≠ η) :
    finiteMeasureTV (Measure.dirac θ) (Measure.dirac η) = 1 := by
  apply finiteMeasureTV_eq_one_of_mutuallySingular
  exact ⟨{θ}ᶜ, (measurableSet_singleton θ).compl, by simp, by simp [hne.symm]⟩

/-- Exact randomized class revelation forces pairwise singularity, by TV
data processing. This does not assume the decoder is deterministic. -/
theorem pairwise_mutuallySingular_of_blackwellLE_exactLabel
    (E : Θ → FiniteMeasure X) (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X))
    (h : BlackwellLE (fun θ => Measure.dirac θ) (fun θ => (E θ : Measure X))) :
    Pairwise fun θ η => (E θ : Measure X) ⟂ₘ (E η : Measure X) := by
  obtain ⟨κ, hκ, hκE⟩ := h
  intro θ η hθη
  have := hE θ
  have := hE η
  apply mutuallySingular_of_finiteMeasureTV_eq_one
  apply le_antisymm (finiteMeasureTV_le_one _ _)
  have hdata := finiteMeasureTV_comp_le κ (E θ : Measure X) (E η : Measure X)
  change finiteMeasureTV ((E θ : Measure X).bind fun x => κ x)
    ((E η : Measure X).bind fun x => κ x) ≤ _ at hdata
  simpa only [hκE θ, hκE η, finiteMeasureTV_dirac_dirac θ η hθη] using hdata

theorem blackwellLE_exactLabel_iff_pairwise_mutuallySingular [Nonempty Θ]
    (E : Θ → FiniteMeasure X) (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X)) :
    BlackwellLE (fun θ => Measure.dirac θ) (fun θ => (E θ : Measure X)) ↔
      Pairwise fun θ η => (E θ : Measure X) ⟂ₘ (E η : Measure X) := by
  constructor
  · exact pairwise_mutuallySingular_of_blackwellLE_exactLabel E hE
  · intro h
    obtain ⟨D, hD⟩ := exists_measurableExactDecoder_of_pairwise_mutuallySingular E h
    exact blackwellLE_exactLabel_of_measurableExactDecoder E hE D hD

theorem blackwellLE_exactLabel_iff_decoder [Nonempty Θ]
    (E : Θ → FiniteMeasure X) (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X)) :
    BlackwellLE (fun θ => Measure.dirac θ) (fun θ => (E θ : Measure X)) ↔
      ∃ D : X → Θ, MeasurableExactDecoder E D := by
  rw [blackwellLE_exactLabel_iff_pairwise_mutuallySingular E hE,
    exists_measurableExactDecoder_iff_pairwise_mutuallySingular E]

/-- Full labels dominate every probability experiment on a finite class:
after reading the label, sample that class's prescribed law. -/
theorem blackwellLE_from_exactLabel
    (E : Θ → FiniteMeasure X) (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X)) :
    BlackwellLE (fun θ => (E θ : Measure X)) (fun θ => Measure.dirac θ) := by
  let κ : Kernel Θ X := ⟨fun θ => (E θ : Measure X), measurable_of_countable _⟩
  have hκ : IsMarkovKernel κ := ⟨hE⟩
  exact ⟨κ, hκ, fun θ => Measure.dirac_bind κ.measurable θ⟩

/-! ## Zero exact-label deficiency attains an exact garbling -/

/-- Vanishing deficiency to finite labels forces each source pair to have
TV one. No compactness or optimizer assumption on measurable decoders is used. -/
theorem pairwise_mutuallySingular_of_exactLabelDeficiency_eq_zero [Nonempty Θ]
    (E : Θ → FiniteMeasure X) (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X))
    (hzero : finiteMeasureDeficiency E (exactLabelExperiment Θ) = 0) :
    Pairwise fun θ η => (E θ : Measure X) ⟂ₘ (E η : Measure X) := by
  intro θ η hθη
  have := hE θ
  have := hE η
  apply mutuallySingular_of_finiteMeasureTV_eq_one
  apply le_antisymm (finiteMeasureTV_le_one _ _)
  have hprob (ζ : Θ) :
      IsProbabilityMeasure (exactLabelExperiment Θ ζ : Measure Θ) := by
    change IsProbabilityMeasure (Measure.dirac ζ)
    infer_instance
  have hlower := finiteMeasureDeficiency_pairwise_lower
    E (exactLabelExperiment Θ) hE hprob θ η
  change (finiteMeasureTV (Measure.dirac θ) (Measure.dirac η) -
    finiteMeasureTV (E θ : Measure X) (E η : Measure X)) / 2 ≤ _ at hlower
  rw [finiteMeasureTV_dirac_dirac θ η hθη, hzero] at hlower
  linarith

theorem finiteMeasureDeficiency_exactLabel_eq_zero_of_blackwellLE [Nonempty Θ]
    (E : Θ → FiniteMeasure X)
    (h : BlackwellLE (fun θ => Measure.dirac θ) (fun θ => (E θ : Measure X))) :
    finiteMeasureDeficiency E (exactLabelExperiment Θ) = 0 := by
  obtain ⟨κ, hκ, hκE⟩ := h
  exact finiteMeasureDeficiency_garbling_eq_zero E (exactLabelExperiment Θ)
    ⟨κ, hκ⟩ fun θ => Subtype.ext (hκE θ)

/-- For the finite exact-label target, zero deficiency always attains exact
Blackwell dominance, even with an arbitrary measurable source signal. -/
theorem finiteMeasureDeficiency_exactLabel_eq_zero_iff_blackwellLE [Nonempty Θ]
    (E : Θ → FiniteMeasure X) (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X)) :
    finiteMeasureDeficiency E (exactLabelExperiment Θ) = 0 ↔
      BlackwellLE (fun θ => Measure.dirac θ) (fun θ => (E θ : Measure X)) :=
  ⟨fun h => (blackwellLE_exactLabel_iff_pairwise_mutuallySingular E hE).2
      (pairwise_mutuallySingular_of_exactLabelDeficiency_eq_zero E hE h),
    finiteMeasureDeficiency_exactLabel_eq_zero_of_blackwellLE E⟩

theorem finiteMeasureDeficiency_exactLabel_eq_zero_iff_decoder [Nonempty Θ]
    (E : Θ → FiniteMeasure X) (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X)) :
    finiteMeasureDeficiency E (exactLabelExperiment Θ) = 0 ↔
      ∃ D : X → Θ, MeasurableExactDecoder E D := by
  rw [finiteMeasureDeficiency_exactLabel_eq_zero_iff_blackwellLE E hE,
    blackwellLE_exactLabel_iff_decoder E hE]

theorem finiteMeasureDeficiency_exactLabel_eq_zero_iff_pairwise_mutuallySingular [Nonempty Θ]
    (E : Θ → FiniteMeasure X) (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X)) :
    finiteMeasureDeficiency E (exactLabelExperiment Θ) = 0 ↔
      Pairwise fun θ η => (E θ : Measure X) ⟂ₘ (E η : Measure X) := by
  rw [finiteMeasureDeficiency_exactLabel_eq_zero_iff_blackwellLE E hE,
    blackwellLE_exactLabel_iff_pairwise_mutuallySingular E hE]

end IdExp
