import Formal.DecisionDeficiencyDuality
import Formal.ArbitraryBlackwell
import Formal.FiniteDecoderAttainment

/-!
# Quantitative decision witnesses on arbitrary world classes

Finite source and target alphabets make the common-decoder simplex compact.
A uniform error bound is therefore feasible on the whole class exactly when
it is feasible on every finite restriction.  Combined with finite optimized
Bayes duality, this gives an exact quantitative, finite-support decision
interpretation without any measurable structure on the world class.
-/

namespace IdExp

open Finset Set

variable {Θ X Y : Type*} [Fintype X] [Fintype Y]

/-- A common decoder bound is determined by nonempty finite restrictions.
The world class need not be finite, measurable, or topological. -/
theorem finiteDeficiency_le_of_all_finite_restrictions
    [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) (c : ℝ)
    (hlocal : ∀ (S : Finset Θ), S.Nonempty →
      finiteDeficiency (restrictFiniteExperiment S E) (restrictFiniteExperiment S F) ≤ c) :
    finiteDeficiency E F ≤ c := by
  let C : Θ → Set (X → Y → ℝ) := fun θ => {G | decodeErr E F G θ ≤ c}
  have hclosed (θ : Θ) : IsClosed (C θ) :=
    isClosed_le (continuous_decodeErr E F θ) continuous_const
  have hfinite : ∀ S : Finset Θ,
      (stochasticRules X Y ∩ ⋂ θ ∈ S, C θ).Nonempty := by
    intro S
    by_cases hS : S.Nonempty
    · let _ : Nonempty {θ // θ ∈ S} := by
        obtain ⟨θ, hθ⟩ := hS
        exact ⟨⟨θ, hθ⟩⟩
      obtain ⟨G, hG, herr⟩ := exists_decoder_eq_finiteDeficiency
        (restrictFiniteExperiment S E) (restrictFiniteExperiment S F)
      refine ⟨G, hG, ?_⟩
      simp only [Set.mem_iInter]
      intro θ hθ
      exact (herr ⟨θ, hθ⟩).trans (hlocal S hS)
    · obtain ⟨G, hG⟩ := stochasticRules_nonempty_of_nonempty (X := X) (Y := Y)
      refine ⟨G, hG, ?_⟩
      rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simp
  obtain ⟨G, hG, hall⟩ := (isCompact_stochasticRules X Y).inter_iInter_nonempty
    C hclosed hfinite
  exact finiteDeficiency_le_of_decoder E F G hG c fun θ => Set.mem_iInter.mp hall θ

/-- Restricting the world class cannot increase deficiency for valid finite
signal experiments. -/
theorem finiteDeficiency_restrict_le [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (S : Finset Θ) (hS : S.Nonempty) :
    finiteDeficiency (restrictFiniteExperiment S E) (restrictFiniteExperiment S F) ≤
      finiteDeficiency E F := by
  let _ : Nonempty {θ // θ ∈ S} := by
    obtain ⟨θ, hθ⟩ := hS
    exact ⟨⟨θ, hθ⟩⟩
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨G, hG, herr⟩ := exists_decoder_le_finiteDeficiency_add E F hE hF hη
  exact finiteDeficiency_le_of_decoder _ _ G hG _ fun θ => herr θ.1

/-- A quantitative failure of a uniform simulation bound already has a
finite set of worlds witnessing the failure. -/
theorem exists_finite_restriction_deficiency_gt [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    {r : ℝ} (hr : r < finiteDeficiency E F) :
    ∃ S : Finset Θ, S.Nonempty ∧
      r < finiteDeficiency (restrictFiniteExperiment S E) (restrictFiniteExperiment S F) := by
  by_contra h
  push Not at h
  exact (not_le_of_gt hr) (finiteDeficiency_le_of_all_finite_restrictions E F r h)

/-- Every sub-deficiency level is exceeded by the optimized disadvantage
in one finite-support prior and unit-range decision problem. -/
theorem exists_finiteSupport_bayesGap_gt_of_lt_finiteDeficiency
    [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    {r : ℝ} (hr : r < finiteDeficiency E F) :
    ∃ (S : Finset Θ), S.Nonempty ∧
      ∃ (α : {θ // θ ∈ S} → ℝ) (u : {θ // θ ∈ S} → Y → ℝ),
        IsDist α ∧ (∀ θ y, u θ y ∈ Set.Icc (0 : ℝ) 1) ∧
        r < finiteBayesValue (restrictFiniteExperiment S F) α u -
          finiteBayesValue (restrictFiniteExperiment S E) α u := by
  obtain ⟨S, hS, hgap⟩ := exists_finite_restriction_deficiency_gt E F hr
  let _ : Nonempty {θ // θ ∈ S} := by
    obtain ⟨θ, hθ⟩ := hS
    exact ⟨⟨θ, hθ⟩⟩
  obtain ⟨α, u, hα, hu, hval⟩ := exists_finiteBayesValue_gap_gt_of_lt_finiteDeficiency
    (restrictFiniteExperiment S E) (restrictFiniteExperiment S F)
    (fun θ => hE θ.1) (fun θ => hF θ.1) hgap
  exact ⟨S, hS, α, u, hα, hu, hval⟩

/-- Optimized decision disadvantages on all finite restrictions. The prior
is a genuine probability distribution on its finite support, with no prior
or measurable structure imposed on the entire world class. -/
def finiteSupportBayesValueGaps [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) : Set ℝ :=
  {c | ∃ (S : Finset Θ), S.Nonempty ∧
    ∃ (α : {θ // θ ∈ S} → ℝ) (u : {θ // θ ∈ S} → Y → ℝ),
      IsDist α ∧ (∀ θ y, u θ y ∈ Set.Icc (0 : ℝ) 1) ∧
      c = finiteBayesValue (restrictFiniteExperiment S F) α u -
        finiteBayesValue (restrictFiniteExperiment S E) α u}

/-- Exact quantitative decision duality on an arbitrary nonempty world
class. Both signal alphabets are finite; finite-support priors suffice. -/
theorem finiteDeficiency_eq_sSup_finiteSupportBayesValueGaps
    [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    finiteDeficiency E F = sSup (finiteSupportBayesValueGaps E F) := by
  classical
  have hbound : ∀ c ∈ finiteSupportBayesValueGaps E F, c ≤ finiteDeficiency E F := by
    rintro c ⟨S, hS, α, u, hα, hu, rfl⟩
    let _ : Nonempty {θ // θ ∈ S} := by
      obtain ⟨θ, hθ⟩ := hS
      exact ⟨⟨θ, hθ⟩⟩
    exact (finiteBayesValue_sub_le_finiteDeficiency
      (restrictFiniteExperiment S E) (restrictFiniteExperiment S F)
      (fun θ => hE θ.1) (fun θ => hF θ.1) α hα u hu).trans
        (finiteDeficiency_restrict_le E F hE hF S hS)
  have hbdd : BddAbove (finiteSupportBayesValueGaps E F) := ⟨_, hbound⟩
  have hne : (finiteSupportBayesValueGaps E F).Nonempty := by
    let S : Finset Θ := {Classical.arbitrary Θ}
    have hS : S.Nonempty := Finset.singleton_nonempty _
    let _ : Nonempty {θ // θ ∈ S} := ⟨⟨Classical.arbitrary Θ, Finset.mem_singleton_self _⟩⟩
    exact ⟨_, S, hS, uniformPrior _, fun _ _ => 0, isDist_uniformPrior,
      fun _ _ => ⟨le_rfl, zero_le_one⟩, rfl⟩
  apply le_antisymm
  · by_contra h
    obtain ⟨S, hS, α, u, hα, hu, hgap⟩ :=
      exists_finiteSupport_bayesGap_gt_of_lt_finiteDeficiency E F hE hF (lt_of_not_ge h)
    have hle := le_csSup hbdd (show
      finiteBayesValue (restrictFiniteExperiment S F) α u -
        finiteBayesValue (restrictFiniteExperiment S E) α u ∈ finiteSupportBayesValueGaps E F
      from ⟨S, hS, α, u, hα, hu, rfl⟩)
    exact (not_lt_of_ge hle) hgap
  · exact csSup_le hne hbound

end IdExp
