import Formal.DualCertificate
import Formal.NativeProcess

/-!
# The directed deficiency triangle inequality

**Relevance:** direct current-paper support, finite-experiment scope.

`NativeProcess.lean` proves that finitary dominance is transitive for any
directed distance `δ` satisfying `δ x z ≤ δ x y + δ y z`, and
`Frontier.lean` uses the same hypothesis for its epsilon split.  Until now no
module proved that the concrete finite directed deficiency `finiteDeficiency`
satisfies it; `Curriculum/SYLLABUS.md` item 3 flags the deficiency triangle
inequality as "on paper".  This file closes that boundary.

The argument is the paper's: approach both infima within `η / 2` by decoders
`G₁` (source to middle) and `G₂` (middle to target), compose them, and bound
the composite's error at every world by the total-variation triangle
inequality plus data processing.  Sending `η` to zero finishes.

The infimum uses Mathlib's convention `sInf ∅ = 0` on the reals, so the
inequality needs every candidate set nonempty.  That is automatic for a
finite world class, and for valid (row-normalized) experiments on an
arbitrary nonempty world class.  It is not automatic in general: on
`Θ = ℝ`, the unnormalized matrices `E θ = (1 + θ, -θ)`, `F θ = θ` on a
one-point signal, and `H θ = (θ, 1 - θ)` give `finiteDeficiency E H = 1`
while both `finiteDeficiency E F` and `finiteDeficiency F H` are `0` because
their candidate sets are empty.  The validity hypotheses below are therefore
not decorative.
-/

namespace IdExp

open Finset Set

variable {Θ X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- A valid finite experiment on a nonempty world class has a nonempty signal
space: some row must sum to one. -/
theorem nonempty_of_isFiniteExperiment [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) : Nonempty X := by
  obtain ⟨x, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (s := Finset.univ) (f := E (Classical.arbitrary Θ)) (by
      rw [(hE _).2]
      exact one_ne_zero)
  exact ⟨x⟩

/-- Positive-eta approximation of the deficiency infimum, with nonemptiness
of the candidate set taken as an explicit hypothesis rather than derived from
validity or finiteness of the world class. -/
theorem exists_decoder_le_finiteDeficiency_add_of_nonempty
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hne : (finiteDeficiencyCandidates E F).Nonempty)
    {η : ℝ} (hη : 0 < η) :
    ∃ G ∈ stochasticRules X Y,
      ∀ θ, decodeErr E F G θ ≤ finiteDeficiency E F + η := by
  have hlt : sInf (finiteDeficiencyCandidates E F) < finiteDeficiency E F + η :=
    lt_add_of_pos_right _ hη
  obtain ⟨c, ⟨G, hG, herr⟩, hclt⟩ := exists_lt_of_csInf_lt hne hlt
  exact ⟨G, hG, fun θ => (herr θ).trans hclt.le⟩

/-- Pointwise triangle step.  The composite decoder's error at one world is at
most the first decoder's error plus the second's: total variation obeys the
triangle inequality through the intermediate law
`finiteDecisionLaw F G₂ θ`, and post-processing the first decoded law by `G₂`
cannot increase its distance to `F θ`. -/
theorem decodeErr_stochasticRuleComp_le_add
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (H : FiniteExperiment Θ Z)
    (G₁ : X → Y → ℝ) (G₂ : Y → Z → ℝ) (hG₂ : G₂ ∈ stochasticRules Y Z)
    (θ : Θ) :
    decodeErr E H (stochasticRuleComp G₁ G₂) θ ≤
      decodeErr E F G₁ θ + decodeErr F H G₂ θ := by
  have hmid := decodeErr_stochasticRuleComp_le E F G₁ G₂ hG₂ θ
  change finiteTV (finiteDecisionLaw E (stochasticRuleComp G₁ G₂) θ)
      (finiteDecisionLaw F G₂ θ) ≤
    finiteTV (finiteDecisionLaw E G₁ θ) (F θ) at hmid
  change finiteTV (finiteDecisionLaw E (stochasticRuleComp G₁ G₂) θ) (H θ) ≤
    finiteTV (finiteDecisionLaw E G₁ θ) (F θ) +
      finiteTV (finiteDecisionLaw F G₂ θ) (H θ)
  exact (finiteTV_triangle
    (finiteDecisionLaw E (stochasticRuleComp G₁ G₂) θ)
    (finiteDecisionLaw F G₂ θ) (H θ)).trans (add_le_add hmid le_rfl)

/-- **Deficiency triangle inequality, candidate-set form.**  Whenever the two
right-hand candidate sets are nonempty, directed deficiency satisfies
`δ(E, H) ≤ δ(E, F) + δ(F, H)`.  The world class is arbitrary and nonempty. -/
theorem finiteDeficiency_triangle_of_nonempty [Nonempty Θ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (H : FiniteExperiment Θ Z)
    (hEF : (finiteDeficiencyCandidates E F).Nonempty)
    (hFH : (finiteDeficiencyCandidates F H).Nonempty) :
    finiteDeficiency E H ≤ finiteDeficiency E F + finiteDeficiency F H := by
  apply le_of_forall_pos_le_add
  intro η hη
  have hhalf : 0 < η / 2 := half_pos hη
  obtain ⟨G₁, hG₁, herr₁⟩ :=
    exists_decoder_le_finiteDeficiency_add_of_nonempty E F hEF hhalf
  obtain ⟨G₂, hG₂, herr₂⟩ :=
    exists_decoder_le_finiteDeficiency_add_of_nonempty F H hFH hhalf
  have hbound : finiteDeficiency E H ≤
      (finiteDeficiency E F + η / 2) + (finiteDeficiency F H + η / 2) := by
    apply finiteDeficiency_le_of_decoder E H (stochasticRuleComp G₁ G₂)
      (stochasticRuleComp_mem_stochasticRules hG₁ hG₂)
    intro θ
    exact (decodeErr_stochasticRuleComp_le_add E F H G₁ G₂ hG₂ θ).trans
      (add_le_add (herr₁ θ) (herr₂ θ))
  linarith

/-- **Deficiency triangle inequality.**  For valid finite experiments `E`,
`F`, `H` over an arbitrary nonempty world class,
`finiteDeficiency E H ≤ finiteDeficiency E F + finiteDeficiency F H`.
Validity supplies nonemptiness of the decoder candidate sets (every decoder
has error at most one) and, through `nonempty_of_isFiniteExperiment`,
nonemptiness of the intermediate and target signal spaces. -/
theorem finiteDeficiency_triangle [Nonempty Θ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (H : FiniteExperiment Θ Z)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hH : IsFiniteExperiment H) :
    finiteDeficiency E H ≤ finiteDeficiency E F + finiteDeficiency F H := by
  have : Nonempty Y := nonempty_of_isFiniteExperiment F hF
  have : Nonempty Z := nonempty_of_isFiniteExperiment H hH
  exact finiteDeficiency_triangle_of_nonempty E F H
    (finiteDeficiencyCandidates_nonempty_of_valid E F hE hF)
    (finiteDeficiencyCandidates_nonempty_of_valid F H hF hH)

/-- **Deficiency triangle inequality on a finite world class.**  With finitely
many worlds no normalization is needed: any decoder to a nonempty signal
space has bounded worst-case error, so every candidate set is nonempty and
the inequality holds for arbitrary real matrices. -/
theorem finiteDeficiency_triangle_of_fintype
    [Fintype Θ] [Nonempty Θ] [Nonempty Y] [Nonempty Z]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (H : FiniteExperiment Θ Z) :
    finiteDeficiency E H ≤ finiteDeficiency E F + finiteDeficiency F H :=
  finiteDeficiency_triangle_of_nonempty E F H
    (finiteDeficiencyCandidates_nonempty E F)
    (finiteDeficiencyCandidates_nonempty F H)

/-! ## Discharging the finitary-order transitivity hypothesis -/

/-- Transitivity of the finitary process order for the concrete finite
directed deficiency on one fixed finite signal type `S`, over a finite
nonempty world class.  This is `finitaryDominates_trans` with its abstract
triangle hypothesis discharged by `finiteDeficiency_triangle_of_fintype`;
because that hypothesis quantifies over every element of the signal-indexed
type, the finite-world version (which needs no validity) is the one that
specializes literally.  Prefix experiments living on horizon-dependent trace
types are not covered by this fixed-`S` specialization. -/
theorem finitaryDominates_trans_finiteDeficiency
    {P S : Type*} [Fintype S] [Nonempty S] [Fintype Θ] [Nonempty Θ]
    (K : P → ℕ → FiniteExperiment Θ S) {π σ τ : P}
    (hπσ : FinitaryDominates K finiteDeficiency π σ)
    (hστ : FinitaryDominates K finiteDeficiency σ τ) :
    FinitaryDominates K finiteDeficiency π τ :=
  finitaryDominates_trans K finiteDeficiency
    (fun E F H => finiteDeficiency_triangle_of_fintype E F H) hπσ hστ

/-- Transitivity of the finitary process order for the concrete finite
directed deficiency on one fixed finite signal type `S`, over an arbitrary
nonempty world class, for a chain of valid experiments.  The abstract
`finitaryDominates_trans` is applied on the subtype of valid experiments,
where `finiteDeficiency_triangle` supplies the triangle hypothesis; the
conclusion is then read back on the original chain.  Prefix experiments
living on horizon-dependent trace types are not covered by this fixed-`S`
specialization. -/
theorem finitaryDominates_trans_finiteDeficiency_of_valid
    {P S : Type*} [Fintype S] [Nonempty Θ]
    (K : P → ℕ → FiniteExperiment Θ S)
    (hK : ∀ π n, IsFiniteExperiment (K π n)) {π σ τ : P}
    (hπσ : FinitaryDominates K finiteDeficiency π σ)
    (hστ : FinitaryDominates K finiteDeficiency σ τ) :
    FinitaryDominates K finiteDeficiency π τ := by
  let V := {E : FiniteExperiment Θ S // IsFiniteExperiment E}
  let K' : P → ℕ → V := fun ρ n => ⟨K ρ n, hK ρ n⟩
  let δ' : V → V → ℝ := fun E F => finiteDeficiency E.1 F.1
  have htriangle : ∀ E F H : V, δ' E H ≤ δ' E F + δ' F H :=
    fun E F H => finiteDeficiency_triangle E.1 F.1 H.1 E.2 F.2 H.2
  exact finitaryDominates_trans K' δ' htriangle hπσ hστ

end IdExp
