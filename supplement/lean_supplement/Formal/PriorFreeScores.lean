import Formal.InformationPolytopeAdmissibility
import Formal.QuadraticScoringRule

/-!
# Prior-free scores as envelopes over priors

A proper scoring rule elicits a belief, so its value needs a prior.  Without a
prior, the decision-theoretic content that survives is Blackwell monotonicity,
and the natural prior-free scores are envelopes of prior-based values over
the simplex.  On a finite world class:

* the *best-prior* information gain is the channel capacity
  `C(E) = max_α I_α(E)`.  It is attained, Blackwell monotone, and strictly
  preserves domination whenever the dominated experiment has a full-support
  capacity-achieving prior — and only such priors can witness strictness,
  since a prior with a null world ignores what the experiment says there;
* the *worst-prior* information gain is zero: a point-mass prior has nothing
  to learn.  (The worst-prior *regret* against a target is the uniform
  deficiency, checked elsewhere as the finite-support prior envelope.)
* the symmetric choice, information at the uniform prior, is a prior-free
  score that is strictly Blackwell monotone, because the uniform prior has
  full support.
-/

namespace IdExp

noncomputable section

set_option linter.unusedSectionVars false

variable {Θ X Y : Type*} [Fintype Θ] [Nonempty Θ] [Fintype X] [Fintype Y]

/-! ## Information is continuous in the prior -/

theorem continuousOn_information_prior (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) :
    ContinuousOn (fun α : Θ → ℝ => finiteBayesInformation α E) (stdSimplex ℝ Θ) := by
  have hmass : Continuous fun α : Θ → ℝ => finiteBayesMass α E := by
    refine continuous_pi fun x => ?_
    unfold finiteBayesMass
    exact continuous_finset_sum _ fun θ _ => (continuous_apply θ).mul continuous_const
  have hcont : Continuous fun α : Θ → ℝ => ent (finiteBayesMass α E) - ∑ θ, α θ * ent (E θ) :=
    (continuous_ent.comp hmass).sub
      (continuous_finset_sum _ fun θ _ => (continuous_apply θ).mul continuous_const)
  exact hcont.continuousOn.congr fun α hα => finiteBayesInformation_eq_ent_mass_sub α hα E hE

/-! ## Channel capacity: the best-prior envelope -/

/-- `C(E) = sup_α I_α(E)` over the prior simplex. -/
def capacity (E : FiniteExperiment Θ X) : ℝ :=
  sSup ((fun α => finiteBayesInformation α E) '' stdSimplex ℝ Θ)

theorem stdSimplex_nonempty' : (stdSimplex ℝ Θ).Nonempty := by
  classical
  exact ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary Θ)⟩

/-- **Capacity is attained.** -/
theorem exists_capacity_achieving (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) :
    ∃ α ∈ stdSimplex ℝ Θ, IsMaxOn (fun α => finiteBayesInformation α E) (stdSimplex ℝ Θ) α :=
  (isCompact_stdSimplex ℝ Θ).exists_isMaxOn stdSimplex_nonempty' (continuousOn_information_prior E hE)

theorem capacity_eq_of_isMaxOn (E : FiniteExperiment Θ X) {α : Θ → ℝ} (hα : α ∈ stdSimplex ℝ Θ)
    (hmax : IsMaxOn (fun α => finiteBayesInformation α E) (stdSimplex ℝ Θ) α) :
    capacity E = finiteBayesInformation α E := by
  have hmax' := isMaxOn_iff.1 hmax
  apply le_antisymm
  · apply csSup_le (stdSimplex_nonempty'.image _)
    rintro _ ⟨β, hβ, rfl⟩
    exact hmax' β hβ
  · refine le_csSup ⟨finiteBayesInformation α E, ?_⟩ (Set.mem_image_of_mem _ hα)
    rintro _ ⟨β, hβ, rfl⟩
    exact hmax' β hβ

theorem information_le_capacity (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    {α : Θ → ℝ} (hα : α ∈ stdSimplex ℝ Θ) : finiteBayesInformation α E ≤ capacity E := by
  obtain ⟨β, hβ, hmax⟩ := exists_capacity_achieving E hE
  rw [capacity_eq_of_isMaxOn E hβ hmax]
  exact (isMaxOn_iff.1 hmax) α hα

/-- **Capacity is Blackwell monotone**: garbling cannot increase it. -/
theorem capacity_garble_le (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) :
    capacity (finiteDecisionLaw E G) ≤ capacity E := by
  apply csSup_le (stdSimplex_nonempty'.image _)
  rintro _ ⟨α, hα, rfl⟩
  exact (finiteBayesInformation_garble_le α hα E hE G hG).trans (information_le_capacity E hE hα)

theorem capacity_mono [Nonempty Y] (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (F : FiniteExperiment Θ Y) (h0 : finiteDeficiency E F = 0) : capacity F ≤ capacity E := by
  obtain ⟨G, hG, hGF⟩ := finiteBlackwellLE_of_finiteDeficiency_eq_zero E F h0
  rw [← hGF]
  exact capacity_garble_le E hE G hG

/-- **Strictness at full-support maximizers.**  If `E` simulates `F` exactly,
`F` has at least the capacity of `E`, and some full-support prior attains
`F`'s capacity, then `F` simulates `E` exactly. -/
theorem capacity_strict [Nonempty X] [Nonempty Y] (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F)
    (h0 : finiteDeficiency E F = 0) (hle : capacity E ≤ capacity F)
    {β : Θ → ℝ} (hβ : β ∈ stdSimplex ℝ Θ) (hβpos : ∀ θ, 0 < β θ)
    (hβmax : IsMaxOn (fun α => finiteBayesInformation α F) (stdSimplex ℝ Θ) β) :
    finiteDeficiency F E = 0 := by
  obtain ⟨G, hG, hGF⟩ := finiteBlackwellLE_of_finiteDeficiency_eq_zero E F h0
  have h1 : finiteBayesInformation β F = capacity F := (capacity_eq_of_isMaxOn F hβ hβmax).symm
  have h2 : finiteBayesInformation β E ≤ capacity E := information_le_capacity E hE hβ
  have h3 : finiteBayesInformation β F ≤ finiteBayesInformation β E := by
    rw [← hGF]
    exact finiteBayesInformation_garble_le β hβ E hE G hG
  have heq : finiteBayesInformation β (finiteDecisionLaw E G) = finiteBayesInformation β E := by
    rw [hGF]
    linarith
  obtain ⟨R, hR, hRE⟩ := exists_reverse_of_information_eq β hβ hβpos E hE G hG heq
  rw [hGF] at hRE
  exact finiteDeficiency_eq_zero_of_finiteBlackwellLE F E ⟨R, hR, hRE⟩

/-! ## The worst-prior envelope is zero -/

theorem finiteBayesInformation_nonneg (α : Θ → ℝ) (hα : IsDist α) (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) : 0 ≤ finiteBayesInformation α E := by
  have hG : (fun (_ : X) (_ : Unit) => (1 : ℝ)) ∈ stochasticRules X Unit := fun _ _ => ⟨fun _ => zero_le_one, by simp⟩
  have h := finiteBayesInformation_garble_le α hα E hE _ hG
  have htriv : finiteDecisionLaw E (fun (_ : X) (_ : Unit) => (1 : ℝ)) = trivialExperiment Θ := by
    funext θ u
    unfold finiteDecisionLaw trivialExperiment
    simp [(hE θ).2]
  rw [htriv] at h
  have h0 : finiteBayesInformation α (trivialExperiment Θ) = 0 := by
    unfold finiteBayesInformation
    rw [finiteBayesPotential_trivialExperiment ent α hα, sub_self]
  linarith

/-- A point-mass prior has nothing to learn. -/
theorem finiteBayesInformation_single [DecidableEq Θ] (θ₀ : Θ) (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) : finiteBayesInformation (Pi.single θ₀ 1) E = 0 := by
  have hα : IsDist (Pi.single θ₀ (1 : ℝ) : Θ → ℝ) := single_mem_stdSimplex ℝ θ₀
  rw [finiteBayesInformation_eq_ent_mass_sub _ hα E hE]
  have hmass : finiteBayesMass (Pi.single θ₀ (1 : ℝ)) E = E θ₀ := by
    funext x
    unfold finiteBayesMass
    simp [Pi.single_apply]
  rw [hmass]
  simp [Pi.single_apply]

theorem worstPriorInformation_eq_zero (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) :
    sInf ((fun α => finiteBayesInformation α E) '' stdSimplex ℝ Θ) = 0 := by
  classical
  apply le_antisymm
  · exact csInf_le ⟨0, fun _ ⟨α, hα, h⟩ => h ▸ finiteBayesInformation_nonneg α hα E hE⟩
      ⟨Pi.single (Classical.arbitrary Θ) 1, single_mem_stdSimplex ℝ _,
        finiteBayesInformation_single _ E hE⟩
  · apply le_csInf (stdSimplex_nonempty'.image _)
    rintro _ ⟨α, hα, rfl⟩
    exact finiteBayesInformation_nonneg α hα E hE

/-! ## The symmetric choice: information at the uniform prior -/

theorem uniformPrior_pos' (θ : Θ) : 0 < uniformPrior Θ θ := by
  unfold uniformPrior
  have : (0 : ℝ) < Fintype.card Θ := by exact_mod_cast Fintype.card_pos
  positivity

theorem uniformPrior_isDist' : IsDist (uniformPrior Θ) := by
  refine ⟨fun θ => (uniformPrior_pos' θ).le, ?_⟩
  unfold uniformPrior
  have : (Fintype.card Θ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **Uniform-prior information is a strictly Blackwell-monotone prior-free score.** -/
theorem uniform_information_strict [Nonempty X] [Nonempty Y] (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (F : FiniteExperiment Θ Y) (h0 : finiteDeficiency E F = 0)
    (hle : finiteBayesInformation (uniformPrior Θ) E ≤ finiteBayesInformation (uniformPrior Θ) F) :
    finiteDeficiency F E = 0 :=
  information_strict_of_deficiency_eq_zero (uniformPrior Θ) uniformPrior_isDist' uniformPrior_pos'
    E hE F h0 hle

end

end IdExp
