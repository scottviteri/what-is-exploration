import Formal.MeasureTotalVariation

/-!
# Directed deficiency of measurable experiments

Bundled Markov decoders, candidate errors, composition and data processing.
For general finite measures the nonempty-candidate hypotheses stay explicit;
probability-experiment wrappers discharge them under their stated nonemptiness
assumptions. Finite-matrix bridges live in `MeasureDeficiency`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace IdExp

/-- A Markov kernel bundled with its normalization proof. -/
structure FiniteMarkovKernel
    (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  toKernel : Kernel X Y
  isMarkov : IsMarkovKernel toKernel

/-- Apply a bundled Markov kernel to a finite input measure. -/
noncomputable def finiteMarkovDecode
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (G : FiniteMarkovKernel X Y) (ν : FiniteMeasure X) : FiniteMeasure Y := by
  let _ : IsMarkovKernel G.toKernel := G.isMarkov
  exact ⟨G.toKernel ∘ₘ (ν : Measure X), by infer_instance⟩

/-- Candidate uniform decoder errors for finite-measure experiments. -/
def finiteMeasureDeficiencyCandidates
    {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y) : Set ℝ :=
  {c | ∃ G : FiniteMarkovKernel X Y, ∀ θ,
    finiteMeasureTV (finiteMarkovDecode G (E θ) : Measure Y)
      (F θ : Measure Y) ≤ c}

/-- Directed deficiency for experiments with arbitrary measurable signal
spaces and finite laws. -/
noncomputable def finiteMeasureDeficiency
    {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y) : ℝ :=
  sInf (finiteMeasureDeficiencyCandidates E F)

theorem finiteMeasureDeficiencyCandidates_bddBelow
    {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Nonempty Θ]
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y) :
    BddBelow (finiteMeasureDeficiencyCandidates E F) := by
  refine ⟨0, ?_⟩
  rintro c ⟨G, herr⟩
  exact (finiteMeasureTV_nonneg
    (finiteMarkovDecode G (E (Classical.arbitrary Θ)) : Measure Y)
    (F (Classical.arbitrary Θ) : Measure Y)).trans
      (herr (Classical.arbitrary Θ))

theorem finiteMeasureDeficiency_le_of_decoder
    {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Nonempty Θ]
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y)
    (G : FiniteMarkovKernel X Y) (c : ℝ)
    (herr : ∀ θ, finiteMeasureTV
      (finiteMarkovDecode G (E θ) : Measure Y) (F θ : Measure Y) ≤ c) :
    finiteMeasureDeficiency E F ≤ c := by
  apply csInf_le (finiteMeasureDeficiencyCandidates_bddBelow E F)
  exact ⟨G, herr⟩

theorem finiteMeasureDeficiency_nonneg_of_decoder
    {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Nonempty Θ]
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y)
    (G : FiniteMarkovKernel X Y) (c : ℝ)
    (herr : ∀ θ, finiteMeasureTV
      (finiteMarkovDecode G (E θ) : Measure Y) (F θ : Measure Y) ≤ c) :
    0 ≤ finiteMeasureDeficiency E F := by
  apply le_csInf
  · exact ⟨c, G, herr⟩
  · rintro b ⟨H, hH⟩
    exact (finiteMeasureTV_nonneg
      (finiteMarkovDecode H (E (Classical.arbitrary Θ)) : Measure Y)
      (F (Classical.arbitrary Θ) : Measure Y)).trans
        (hH (Classical.arbitrary Θ))

/-! ## Directed deficiency calculus -/

section Deficiency

variable {Θ X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- Composite of bundled Markov kernels: first `G₁ : X → Y`, then
`G₂ : Y → Z`. -/
noncomputable def FiniteMarkovKernel.comp
    (G₂ : FiniteMarkovKernel Y Z) (G₁ : FiniteMarkovKernel X Y) :
    FiniteMarkovKernel X Z where
  toKernel := G₂.toKernel ∘ₖ G₁.toKernel
  isMarkov := by
    have := G₁.isMarkov
    have := G₂.isMarkov
    infer_instance

theorem finiteMarkovDecode_comp
    (G₂ : FiniteMarkovKernel Y Z) (G₁ : FiniteMarkovKernel X Y)
    (ν : FiniteMeasure X) :
    finiteMarkovDecode (G₂.comp G₁) ν =
      finiteMarkovDecode G₂ (finiteMarkovDecode G₁ ν) := by
  apply Subtype.ext
  show (G₂.toKernel ∘ₖ G₁.toKernel) ∘ₘ (ν : Measure X) =
    G₂.toKernel ∘ₘ (G₁.toKernel ∘ₘ (ν : Measure X))
  exact Measure.comp_assoc.symm

/-- Positive-eta approximation of the deficiency infimum from a nonempty
candidate set. -/
theorem exists_finiteMarkovDecoder_le_add_of_nonempty
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y)
    (hne : (finiteMeasureDeficiencyCandidates E F).Nonempty)
    {η : ℝ} (hη : 0 < η) :
    ∃ G : FiniteMarkovKernel X Y, ∀ θ,
      finiteMeasureTV (finiteMarkovDecode G (E θ) : Measure Y) (F θ : Measure Y) ≤
        finiteMeasureDeficiency E F + η := by
  have hlt : sInf (finiteMeasureDeficiencyCandidates E F) <
      finiteMeasureDeficiency E F + η :=
    lt_add_of_pos_right _ hη
  obtain ⟨c, ⟨G, herr⟩, hclt⟩ := exists_lt_of_csInf_lt hne hlt
  exact ⟨G, fun θ => (herr θ).trans hclt.le⟩

/-- Pointwise triangle step: the composite decoder's error at one world is at
most the first decoder's error plus the second's (TV triangle inequality
through the intermediate decoded law, then data processing under `G₂`). -/
theorem finiteMeasureTV_decode_comp_le_add
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y) (H : Θ → FiniteMeasure Z)
    (G₁ : FiniteMarkovKernel X Y) (G₂ : FiniteMarkovKernel Y Z) (θ : Θ) :
    finiteMeasureTV (finiteMarkovDecode (G₂.comp G₁) (E θ) : Measure Z)
        (H θ : Measure Z) ≤
      finiteMeasureTV (finiteMarkovDecode G₁ (E θ) : Measure Y) (F θ : Measure Y) +
        finiteMeasureTV (finiteMarkovDecode G₂ (F θ) : Measure Z) (H θ : Measure Z) := by
  rw [finiteMarkovDecode_comp]
  have hmid : finiteMeasureTV
      (finiteMarkovDecode G₂ (finiteMarkovDecode G₁ (E θ)) : Measure Z)
      (finiteMarkovDecode G₂ (F θ) : Measure Z) ≤
      finiteMeasureTV (finiteMarkovDecode G₁ (E θ) : Measure Y) (F θ : Measure Y) := by
    have := G₂.isMarkov
    exact finiteMeasureTV_comp_le G₂.toKernel _ _
  exact (finiteMeasureTV_triangle _ _ _).trans (add_le_add hmid le_rfl)

/-- **Deficiency triangle inequality, candidate-set form.**  Whenever both
right-hand candidate sets are nonempty,
`δ(E, H) ≤ δ(E, F) + δ(F, H)` for experiments on arbitrary measurable
signal spaces over an arbitrary nonempty world class. -/
theorem finiteMeasureDeficiency_triangle_of_nonempty [Nonempty Θ]
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y) (H : Θ → FiniteMeasure Z)
    (hEF : (finiteMeasureDeficiencyCandidates E F).Nonempty)
    (hFH : (finiteMeasureDeficiencyCandidates F H).Nonempty) :
    finiteMeasureDeficiency E H ≤
      finiteMeasureDeficiency E F + finiteMeasureDeficiency F H := by
  apply le_of_forall_pos_le_add
  intro η hη
  have hhalf : 0 < η / 2 := half_pos hη
  obtain ⟨G₁, herr₁⟩ :=
    exists_finiteMarkovDecoder_le_add_of_nonempty E F hEF hhalf
  obtain ⟨G₂, herr₂⟩ :=
    exists_finiteMarkovDecoder_le_add_of_nonempty F H hFH hhalf
  have hbound : finiteMeasureDeficiency E H ≤
      (finiteMeasureDeficiency E F + η / 2) +
        (finiteMeasureDeficiency F H + η / 2) := by
    apply finiteMeasureDeficiency_le_of_decoder E H (G₂.comp G₁)
    intro θ
    exact (finiteMeasureTV_decode_comp_le_add E F H G₁ G₂ θ).trans
      (add_le_add (herr₁ θ) (herr₂ θ))
  linarith

/-- Every decoder from an exact garbling `E'` of `E` composes with the
garbling kernel into a decoder from `E` with the same error: the candidate
set from the garbled source is contained in the candidate set from the
finer source. -/
theorem finiteMeasureDeficiencyCandidates_subset_of_source_garbling
    {X' : Type*} [MeasurableSpace X']
    (E : Θ → FiniteMeasure X) (E' : Θ → FiniteMeasure X')
    (H : FiniteMarkovKernel X X') (hH : ∀ θ, finiteMarkovDecode H (E θ) = E' θ)
    (F : Θ → FiniteMeasure Y) :
    finiteMeasureDeficiencyCandidates E' F ⊆ finiteMeasureDeficiencyCandidates E F := by
  rintro c ⟨G, herr⟩
  refine ⟨G.comp H, fun θ => ?_⟩
  have hdec : (finiteMarkovDecode (G.comp H) (E θ) : Measure Y) =
      (finiteMarkovDecode G (E' θ) : Measure Y) := by
    rw [finiteMarkovDecode_comp, hH θ]
  calc finiteMeasureTV (finiteMarkovDecode (G.comp H) (E θ) : Measure Y) (F θ : Measure Y)
      = finiteMeasureTV (finiteMarkovDecode G (E' θ) : Measure Y) (F θ : Measure Y) :=
        finiteMeasureTV_congr _ _ _ _ hdec rfl
    _ ≤ c := herr θ

/-- **Source garbling.**  Replacing the source by an exact garbling of it
cannot decrease directed deficiency to any target: the deficiency from the
finer source `E` is at most the deficiency from the garbled source `E'`.
No data processing is needed; the nonemptiness hypothesis on the garbled
candidate set is forced by the `sInf ∅ = 0` convention. -/
theorem finiteMeasureDeficiency_le_of_source_garbling [Nonempty Θ]
    {X' : Type*} [MeasurableSpace X']
    (E : Θ → FiniteMeasure X) (E' : Θ → FiniteMeasure X')
    (H : FiniteMarkovKernel X X') (hH : ∀ θ, finiteMarkovDecode H (E θ) = E' θ)
    (F : Θ → FiniteMeasure Y)
    (hne : (finiteMeasureDeficiencyCandidates E' F).Nonempty) :
    finiteMeasureDeficiency E F ≤ finiteMeasureDeficiency E' F :=
  csInf_le_csInf (finiteMeasureDeficiencyCandidates_bddBelow E F) hne
    (finiteMeasureDeficiencyCandidates_subset_of_source_garbling E E' H hH F)

/-- **Target garbling.**  Replacing the target by an exact garbling of it
cannot increase directed deficiency.  The proof approaches the infimum
within eta, post-composes the decoder with the garbling kernel, and applies
data processing. -/
theorem finiteMeasureDeficiency_mono_target [Nonempty Θ]
    {Y' : Type*} [MeasurableSpace Y']
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y) (F' : Θ → FiniteMeasure Y')
    (H : FiniteMarkovKernel Y Y') (hH : ∀ θ, finiteMarkovDecode H (F θ) = F' θ)
    (hne : (finiteMeasureDeficiencyCandidates E F).Nonempty) :
    finiteMeasureDeficiency E F' ≤ finiteMeasureDeficiency E F := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨G, herr⟩ := exists_finiteMarkovDecoder_le_add_of_nonempty E F hne hη
  apply finiteMeasureDeficiency_le_of_decoder E F' (H.comp G)
  intro θ
  rw [finiteMarkovDecode_comp, ← hH θ]
  have := H.isMarkov
  exact (finiteMeasureTV_comp_le H.toKernel _ _).trans (herr θ)

/-- An exact garbling of an experiment has deficiency zero from it. -/
theorem finiteMeasureDeficiency_garbling_eq_zero [Nonempty Θ]
    {X' : Type*} [MeasurableSpace X']
    (E : Θ → FiniteMeasure X) (E' : Θ → FiniteMeasure X')
    (H : FiniteMarkovKernel X X') (hH : ∀ θ, finiteMarkovDecode H (E θ) = E' θ) :
    finiteMeasureDeficiency E E' = 0 := by
  have herr : ∀ θ,
      finiteMeasureTV (finiteMarkovDecode H (E θ) : Measure X') (E' θ : Measure X') ≤ 0 := by
    intro θ
    rw [hH θ, finiteMeasureTV_self]
  exact le_antisymm (finiteMeasureDeficiency_le_of_decoder E E' H 0 herr)
    (finiteMeasureDeficiency_nonneg_of_decoder E E' H 0 herr)

theorem finiteMeasureDeficiency_self_eq_zero [Nonempty Θ]
    (E : Θ → FiniteMeasure X) : finiteMeasureDeficiency E E = 0 := by
  refine finiteMeasureDeficiency_garbling_eq_zero E E
    ⟨Kernel.id, inferInstance⟩ fun θ => ?_
  apply Subtype.ext
  show Kernel.id ∘ₘ (E θ : Measure X) = (E θ : Measure X)
  exact Measure.id_comp

/-- Directed deficiency is nonnegative as soon as one candidate exists. -/
theorem finiteMeasureDeficiency_nonneg_of_nonempty [Nonempty Θ]
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y)
    (hne : (finiteMeasureDeficiencyCandidates E F).Nonempty) :
    0 ≤ finiteMeasureDeficiency E F := by
  obtain ⟨c, G, herr⟩ := hne
  exact finiteMeasureDeficiency_nonneg_of_decoder E F G c herr

/-- On a finite world class any Markov decoder yields a candidate, so the
candidate set is nonempty without normalization hypotheses. -/
theorem finiteMeasureDeficiencyCandidates_nonempty_of_fintype [Fintype Θ]
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y)
    (G : FiniteMarkovKernel X Y) :
    (finiteMeasureDeficiencyCandidates E F).Nonempty := by
  let err : Θ → ℝ := fun θ =>
    finiteMeasureTV (finiteMarkovDecode G (E θ) : Measure Y) (F θ : Measure Y)
  have hbound : ∀ θ, err θ ≤ ∑ θ', err θ' := fun θ =>
    Finset.single_le_sum (f := err) (s := Finset.univ)
      (fun θ' _ => finiteMeasureTV_nonneg _ _) (Finset.mem_univ θ)
  exact ⟨∑ θ', err θ', G, hbound⟩

/-- Decoding a probability experiment through a Markov kernel yields a
probability experiment. -/
theorem isProbabilityMeasure_finiteMarkovDecode
    (G : FiniteMarkovKernel X Y) (ν : FiniteMeasure X)
    [IsProbabilityMeasure (ν : Measure X)] :
    IsProbabilityMeasure (finiteMarkovDecode G ν : Measure Y) := by
  have := G.isMarkov
  show IsProbabilityMeasure (G.toKernel ∘ₘ (ν : Measure X))
  infer_instance

/-- For probability experiments every Markov decoder has error at most one,
so the candidate set is nonempty over an arbitrary world class as soon as
the target signal space is nonempty. -/
theorem finiteMeasureDeficiencyCandidates_nonempty_of_prob [Nonempty Y]
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y)
    (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X))
    (hF : ∀ θ, IsProbabilityMeasure (F θ : Measure Y)) :
    (finiteMeasureDeficiencyCandidates E F).Nonempty := by
  let G : FiniteMarkovKernel X Y :=
    ⟨Kernel.const X (Measure.dirac (Classical.arbitrary Y)), inferInstance⟩
  refine ⟨1, G, fun θ => ?_⟩
  have := hE θ
  have := hF θ
  have := isProbabilityMeasure_finiteMarkovDecode G (E θ)
  exact finiteMeasureTV_le_one _ _

/-- Any simulator must pay for pairwise separation in the target that is
absent from the source. This is the measurable-experiment version of the
finite-matrix two-world deficiency obstruction, with the actual decoder infimum. -/
theorem finiteMeasureDeficiency_pairwise_lower [Nonempty Y]
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y)
    (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X))
    (hF : ∀ θ, IsProbabilityMeasure (F θ : Measure Y))
    (θ η : Θ) :
    (finiteMeasureTV (F θ : Measure Y) (F η : Measure Y) -
      finiteMeasureTV (E θ : Measure X) (E η : Measure X)) / 2 ≤
      finiteMeasureDeficiency E F := by
  apply le_csInf (finiteMeasureDeficiencyCandidates_nonempty_of_prob E F hE hF)
  rintro c ⟨G, hG⟩
  have := G.isMarkov
  have hfirst := finiteMeasureTV_triangle
    (F θ : Measure Y) (finiteMarkovDecode G (E θ) : Measure Y) (F η : Measure Y)
  have hsecond := finiteMeasureTV_triangle
    (finiteMarkovDecode G (E θ) : Measure Y)
    (finiteMarkovDecode G (E η) : Measure Y) (F η : Measure Y)
  have hdata := finiteMeasureTV_comp_le G.toKernel (E θ : Measure X) (E η : Measure X)
  change finiteMeasureTV (finiteMarkovDecode G (E θ) : Measure Y)
    (finiteMarkovDecode G (E η) : Measure Y) ≤ _ at hdata
  rw [finiteMeasureTV_symm (F θ : Measure Y)
    (finiteMarkovDecode G (E θ) : Measure Y)] at hfirst
  have hθ := hG θ
  have hη := hG η
  linarith

theorem finiteMeasureDeficiency_nonneg_of_prob [Nonempty Θ] [Nonempty Y]
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y)
    (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X))
    (hF : ∀ θ, IsProbabilityMeasure (F θ : Measure Y)) :
    0 ≤ finiteMeasureDeficiency E F :=
  finiteMeasureDeficiency_nonneg_of_nonempty E F
    (finiteMeasureDeficiencyCandidates_nonempty_of_prob E F hE hF)

/-- Reindexing both probability experiments to a nonempty smaller parameter
class cannot increase directed deficiency.  This generic fact belongs in the
measure-deficiency calculus; applications may take `phi` to be a subtype
inclusion. -/
theorem finiteMeasureDeficiency_reindex_le_of_prob
    {Θ' : Type*} [Nonempty Θ] [Nonempty Θ'] [Nonempty Y]
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y)
    (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X))
    (hF : ∀ θ, IsProbabilityMeasure (F θ : Measure Y))
    (phi : Θ' → Θ) :
    finiteMeasureDeficiency (fun θ' => E (phi θ'))
        (fun θ' => F (phi θ')) ≤
      finiteMeasureDeficiency E F := by
  unfold finiteMeasureDeficiency
  apply le_csInf
    (finiteMeasureDeficiencyCandidates_nonempty_of_prob E F hE hF)
  intro d hd
  apply csInf_le
    (finiteMeasureDeficiencyCandidates_bddBelow
      (fun θ' => E (phi θ')) (fun θ' => F (phi θ')))
  obtain ⟨G, hG⟩ := hd
  exact ⟨G, fun θ' => hG (phi θ')⟩

theorem finiteMeasureDeficiency_le_one_of_prob [Nonempty Θ] [Nonempty Y]
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y)
    (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X))
    (hF : ∀ θ, IsProbabilityMeasure (F θ : Measure Y)) :
    finiteMeasureDeficiency E F ≤ 1 := by
  let G : FiniteMarkovKernel X Y :=
    ⟨Kernel.const X (Measure.dirac (Classical.arbitrary Y)), inferInstance⟩
  refine finiteMeasureDeficiency_le_of_decoder E F G 1 fun θ => ?_
  have := hE θ
  have := hF θ
  have := isProbabilityMeasure_finiteMarkovDecode G (E θ)
  exact finiteMeasureTV_le_one _ _

/-- Triangle inequality for probability experiments, with the candidate
nonemptiness discharged automatically. -/
theorem finiteMeasureDeficiency_triangle_of_prob [Nonempty Θ] [Nonempty Y] [Nonempty Z]
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y) (H : Θ → FiniteMeasure Z)
    (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X))
    (hF : ∀ θ, IsProbabilityMeasure (F θ : Measure Y))
    (hH : ∀ θ, IsProbabilityMeasure (H θ : Measure Z)) :
    finiteMeasureDeficiency E H ≤
      finiteMeasureDeficiency E F + finiteMeasureDeficiency F H :=
  finiteMeasureDeficiency_triangle_of_nonempty E F H
    (finiteMeasureDeficiencyCandidates_nonempty_of_prob E F hE hF)
    (finiteMeasureDeficiencyCandidates_nonempty_of_prob F H hF hH)

/-- Source garbling for probability experiments. -/
theorem finiteMeasureDeficiency_le_of_source_garbling_of_prob [Nonempty Θ] [Nonempty Y]
    {X' : Type*} [MeasurableSpace X']
    (E : Θ → FiniteMeasure X) (E' : Θ → FiniteMeasure X')
    (H : FiniteMarkovKernel X X') (hH : ∀ θ, finiteMarkovDecode H (E θ) = E' θ)
    (F : Θ → FiniteMeasure Y)
    (hE' : ∀ θ, IsProbabilityMeasure (E' θ : Measure X'))
    (hF : ∀ θ, IsProbabilityMeasure (F θ : Measure Y)) :
    finiteMeasureDeficiency E F ≤ finiteMeasureDeficiency E' F :=
  finiteMeasureDeficiency_le_of_source_garbling E E' H hH F
    (finiteMeasureDeficiencyCandidates_nonempty_of_prob E' F hE' hF)

/-- Target garbling for probability experiments. -/
theorem finiteMeasureDeficiency_mono_target_of_prob [Nonempty Θ] [Nonempty Y]
    {Y' : Type*} [MeasurableSpace Y']
    (E : Θ → FiniteMeasure X) (F : Θ → FiniteMeasure Y) (F' : Θ → FiniteMeasure Y')
    (H : FiniteMarkovKernel Y Y') (hH : ∀ θ, finiteMarkovDecode H (F θ) = F' θ)
    (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X))
    (hF : ∀ θ, IsProbabilityMeasure (F θ : Measure Y)) :
    finiteMeasureDeficiency E F' ≤ finiteMeasureDeficiency E F :=
  finiteMeasureDeficiency_mono_target E F F' H hH
    (finiteMeasureDeficiencyCandidates_nonempty_of_prob E F hE hF)

/-- Two experiments that are exact garblings of each other have the same
deficiency to every target (Blackwell-equivalent encoding invariance). -/
theorem finiteMeasureDeficiency_eq_of_mutual_garbling [Nonempty Θ]
    {X' : Type*} [MeasurableSpace X']
    (E : Θ → FiniteMeasure X) (E' : Θ → FiniteMeasure X')
    (H : FiniteMarkovKernel X X') (hH : ∀ θ, finiteMarkovDecode H (E θ) = E' θ)
    (H' : FiniteMarkovKernel X' X) (hH' : ∀ θ, finiteMarkovDecode H' (E' θ) = E θ)
    (F : Θ → FiniteMeasure Y)
    (hne : (finiteMeasureDeficiencyCandidates E F).Nonempty)
    (hne' : (finiteMeasureDeficiencyCandidates E' F).Nonempty) :
    finiteMeasureDeficiency E F = finiteMeasureDeficiency E' F :=
  le_antisymm (finiteMeasureDeficiency_le_of_source_garbling E E' H hH F hne')
    (finiteMeasureDeficiency_le_of_source_garbling E' E H' hH' F hne)

end Deficiency

end IdExp
