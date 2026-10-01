import Formal.DeficiencyDuality

/-!
# Deficiency is the worst optimized bounded decision disadvantage

The finite Bayes value below is a literal optimization over every randomized
decision rule.  Its finite maximum has the familiar signalwise formula and
is attained by a deterministic rule.  Normalizing the box dual of directed
deficiency then proves the sharp converse to quantitative decision readiness.
The target signal alphabet itself suffices as the decision alphabet.
-/

set_option linter.unusedSectionVars false

namespace IdExp

open Finset Set

variable {Θ X Y D : Type*} [Fintype Θ] [Fintype X] [Fintype Y] [Fintype D]

/-- Unnormalized posterior expected utility at one acquired signal.  No
division by a signal probability is needed, including at null signals. -/
def finiteDecisionScore (E : FiniteExperiment Θ X) (α : Θ → ℝ)
    (u : Θ → D → ℝ) (x : X) (d : D) : ℝ :=
  ∑ θ, α θ * E θ x * u θ d

/-- Optimized finite Bayesian value, written as the sum of signalwise
maxima. The theorem `finiteBayesValue_isGreatest` identifies it with the
maximum over all world-independent randomized decision rules. -/
noncomputable def finiteBayesValue [Nonempty D]
    (E : FiniteExperiment Θ X) (α : Θ → ℝ) (u : Θ → D → ℝ) : ℝ :=
  ∑ x, Finset.univ.sup' Finset.univ_nonempty (finiteDecisionScore E α u x)

theorem linearPayoff_finiteDecisionLaw_eq_score
    (E : FiniteExperiment Θ X) (α : Θ → ℝ) (u : Θ → D → ℝ)
    (q : X → D → ℝ) :
    linearPayoff α u (finiteDecisionLaw E q) =
      ∑ x, ∑ d, q x d * finiteDecisionScore E α u x d := by
  unfold linearPayoff finiteDecisionLaw finiteDecisionScore
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ θ, ∑ x, ∑ d, α θ * (E θ x * q x d * u θ d) := by
      apply Finset.sum_congr rfl
      intro θ _
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ θ, ∑ d, α θ * (E θ x * q x d * u θ d) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro θ _
      ring

/-- Every randomized rule has value at most the signalwise optimum. -/
theorem linearPayoff_le_finiteBayesValue [Nonempty D]
    (E : FiniteExperiment Θ X) (α : Θ → ℝ) (u : Θ → D → ℝ)
    (q : X → D → ℝ) (hq : q ∈ stochasticRules X D) :
    linearPayoff α u (finiteDecisionLaw E q) ≤ finiteBayesValue E α u := by
  rw [linearPayoff_finiteDecisionLaw_eq_score]
  apply Finset.sum_le_sum
  intro x _
  calc
    ∑ d, q x d * finiteDecisionScore E α u x d ≤
        ∑ d, q x d * Finset.univ.sup' Finset.univ_nonempty
          (finiteDecisionScore E α u x) :=
      Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left
        (Finset.le_sup' (finiteDecisionScore E α u x) (Finset.mem_univ d))
        ((hq x (Set.mem_univ x)).1 d)
    _ = _ := by rw [← Finset.sum_mul, (hq x (Set.mem_univ x)).2, one_mul]

/-- A deterministic rule attains the optimum; the result permits null
signals and arbitrary real coefficients. -/
theorem exists_selection_eq_finiteBayesValue [Nonempty D]
    (E : FiniteExperiment Θ X) (α : Θ → ℝ) (u : Θ → D → ℝ) :
    ∃ σ : X → D, ∑ x, finiteDecisionScore E α u x (σ x) =
      finiteBayesValue E α u := by
  classical
  choose σ _ hσ using fun x => Finset.exists_mem_eq_sup'
    (s := Finset.univ) Finset.univ_nonempty (finiteDecisionScore E α u x)
  exact ⟨σ, Finset.sum_congr rfl fun x _ => (hσ x).symm⟩

theorem linearPayoff_selectionRule
    (E : FiniteExperiment Θ X) (α : Θ → ℝ) (u : Θ → D → ℝ)
    [DecidableEq D] (σ : X → D) :
    linearPayoff α u (finiteDecisionLaw E (selectionRule σ)) =
      ∑ x, finiteDecisionScore E α u x (σ x) := by
  rw [linearPayoff_finiteDecisionLaw_eq_score]
  simp [selectionRule]

/-- The displayed Bayes value is exactly the greatest payoff in the full
randomized attainable-decision menu. -/
theorem finiteBayesValue_isGreatest [Nonempty D]
    (E : FiniteExperiment Θ X) (α : Θ → ℝ) (u : Θ → D → ℝ) :
    IsGreatest (linearPayoff α u '' finiteMatrixCapabilityMenu (D := D) E)
      (finiteBayesValue E α u) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_selection_eq_finiteBayesValue E α u
  constructor
  · exact ⟨_, ⟨selectionRule σ, selectionRule_mem_stochasticRules σ, rfl⟩,
      (linearPayoff_selectionRule E α u σ).trans hσ⟩
  · rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact linearPayoff_le_finiteBayesValue E α u q hq

/-- Exact garbling preserves the optimized finite decision value, directly
from the complete randomized decision menu. -/
theorem finiteBayesValue_mono_of_finiteBlackwellLE [Nonempty D]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (h : FiniteBlackwellLE F E) (α : Θ → ℝ) (u : Θ → D → ℝ) :
    finiteBayesValue F α u ≤ finiteBayesValue E α u := by
  obtain ⟨G, hG, hGF⟩ := h
  obtain ⟨_, ⟨q, hq, rfl⟩, hopt⟩ := (finiteBayesValue_isGreatest F α u).1
  have hcomp := stochasticRuleComp_mem_stochasticRules hG hq
  have hupper := linearPayoff_le_finiteBayesValue E α u
    (stochasticRuleComp G q) hcomp
  rw [finiteDecisionLaw_stochasticRuleComp, hGF] at hupper
  simpa only [hopt] using hupper

/-- Valid experiments and unit-range utilities have optimized value in
`[0,1]`, uniformly in the finite decision alphabet. -/
theorem finiteBayesValue_mem_unitInterval [Nonempty D]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (α : Θ → ℝ) (hα : IsDist α) (u : Θ → D → ℝ)
    (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) :
    finiteBayesValue E α u ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨_, ⟨q, hq, rfl⟩, hopt⟩ := (finiteBayesValue_isGreatest E α u).1
  rw [← hopt]
  have hp := finiteDecisionLaw_valid E hE q hq
  constructor
  · exact Finset.sum_nonneg fun θ _ => mul_nonneg (hα.1 θ)
      (Finset.sum_nonneg fun d _ => mul_nonneg ((hp θ).1 d) (hu θ d).1)
  · calc
      linearPayoff α u (finiteDecisionLaw E q) ≤ ∑ θ, α θ * 1 := by
        apply Finset.sum_le_sum
        intro θ _
        apply mul_le_mul_of_nonneg_left _ (hα.1 θ)
        calc
          ∑ d, finiteDecisionLaw E q θ d * u θ d ≤
              ∑ d, finiteDecisionLaw E q θ d := Finset.sum_le_sum fun d _ =>
            mul_le_of_le_one_right ((hp θ).1 d) (hu θ d).2
          _ = 1 := (hp θ).2
      _ = 1 := by simpa using hα.2

/-- The unit-range payoff loss for a supplied decoder, after both decision
problems have been optimized. -/
theorem finiteBayesValue_sub_le_of_decoder [Nonempty D]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (α : Θ → ℝ) (hα : IsDist α) (u : Θ → D → ℝ)
    (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
    (c : ℝ) (herr : ∀ θ, decodeErr E F G θ ≤ c) :
    finiteBayesValue F α u - finiteBayesValue E α u ≤ c := by
  obtain ⟨_, ⟨q, hq, rfl⟩, hqopt⟩ := (finiteBayesValue_isGreatest F α u).1
  have hcomp := stochasticRuleComp_mem_stochasticRules hG hq
  have hupper := linearPayoff_le_finiteBayesValue E α u
    (stochasticRuleComp G q) hcomp
  have hpoint (θ : Θ) :
      (∑ d, finiteDecisionLaw F q θ d * u θ d) -
        (∑ d, finiteDecisionLaw E (stochasticRuleComp G q) θ d * u θ d) ≤ c := by
    have hvF := finiteDecisionLaw_valid F hF q hq θ
    have hvE := finiteDecisionLaw_valid E hE _ hcomp θ
    have htv := expectation_sub_le_finiteTV
      (finiteDecisionLaw F q θ) (finiteDecisionLaw E (stochasticRuleComp G q) θ)
      (u θ) (hvF.2.trans hvE.2.symm) (fun d => (hu θ d).1) (fun d => (hu θ d).2)
    apply htv.trans
    rw [finiteTV_symm]
    exact (decodeErr_stochasticRuleComp_le E F G q hq θ).trans (herr θ)
  have hweighted : linearPayoff α u (finiteDecisionLaw F q) -
      linearPayoff α u (finiteDecisionLaw E (stochasticRuleComp G q)) ≤ c := by
    unfold linearPayoff
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ θ, α θ * ((∑ d, finiteDecisionLaw F q θ d * u θ d) -
          ∑ d, finiteDecisionLaw E (stochasticRuleComp G q) θ d * u θ d) := by
        simp_rw [mul_sub]
      _ ≤ ∑ θ, α θ * c := Finset.sum_le_sum fun θ _ =>
        mul_le_mul_of_nonneg_left (hpoint θ) (hα.1 θ)
      _ = c := by rw [← Finset.sum_mul, hα.2, one_mul]
  linarith

/-- Sharp finite quantitative readiness for every nonempty finite decision
alphabet, after optimizing all randomized rules. -/
theorem finiteBayesValue_sub_le_finiteDeficiency [Nonempty Θ] [Nonempty D]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (α : Θ → ℝ) (hα : IsDist α) (u : Θ → D → ℝ)
    (hu : ∀ θ d, u θ d ∈ Set.Icc (0 : ℝ) 1) :
    finiteBayesValue F α u - finiteBayesValue E α u ≤ finiteDeficiency E F := by
  have : Nonempty Y := nonempty_of_isFiniteExperiment F hF
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨G, hG, herr⟩ := exists_decoder_le_finiteDeficiency_add E F hE hF hη
  exact finiteBayesValue_sub_le_of_decoder E F hE hF α hα u hu G hG _ herr

/-- A box-dual coefficient can be written as prior mass times a unit-range
utility. Zero-prior worlds receive utility zero and cause no division issue. -/
theorem exists_unitUtility_of_boxWeights
    (α : Θ → ℝ) (hα : IsDist α) (w : Θ → Y → ℝ)
    (hw0 : ∀ θ y, 0 ≤ w θ y) (hwle : ∀ θ y, w θ y ≤ α θ) :
    ∃ u : Θ → Y → ℝ, (∀ θ y, u θ y ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ θ y, α θ * u θ y = w θ y := by
  refine ⟨fun θ y => w θ y / α θ, ?_, ?_⟩
  · intro θ y
    by_cases hzero : α θ = 0
    · simp [hzero]
    · have hpos : 0 < α θ := lt_of_le_of_ne (hα.1 θ) (Ne.symm hzero)
      exact ⟨div_nonneg (hw0 θ y) hpos.le, (div_le_one hpos).2 (hwle θ y)⟩
  · intro θ y
    by_cases hzero : α θ = 0
    · have hwzero : w θ y = 0 := le_antisymm (by simpa [hzero] using hwle θ y) (hw0 θ y)
      simp [hzero, hwzero]
    · exact mul_div_cancel₀ _ hzero

/-- Every strict lower bound on deficiency is witnessed by an actual
optimized Bayes-value difference with utilities in `[0,1]`. The decision
alphabet is the target signal alphabet itself. -/
theorem exists_finiteBayesValue_gap_gt_of_lt_finiteDeficiency
    [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    {r : ℝ} (hr : r < finiteDeficiency E F) :
    ∃ (α : Θ → ℝ) (u : Θ → Y → ℝ), IsDist α ∧
      (∀ θ y, u θ y ∈ Set.Icc (0 : ℝ) 1) ∧
      r < finiteBayesValue F α u - finiteBayesValue E α u := by
  classical
  obtain ⟨α, w, hα, hw0, hwle, hgap⟩ :=
    exists_boxDual_gt_of_lt_finiteDeficiency E F hE hF hr
  obtain ⟨u, hu, hweight⟩ := exists_unitUtility_of_boxWeights α hα w hw0 hwle
  obtain ⟨σ, hσ⟩ := exists_selection_eq_finiteBayesValue E α u
  have hsource : ∑ x, ∑ θ, E θ x * w θ (σ x) = finiteBayesValue E α u := by
    rw [← hσ]
    apply Finset.sum_congr rfl
    intro x _
    unfold finiteDecisionScore
    apply Finset.sum_congr rfl
    intro θ _
    rw [← hweight]
    ring
  have htarget : ∑ θ, ∑ y, w θ y * F θ y ≤ finiteBayesValue F α u := by
    have hmem := (finiteBayesValue_isGreatest F α u).2
      (Set.mem_image_of_mem (linearPayoff α u) (self_mem_finiteMatrixCapabilityMenu F))
    have heq : linearPayoff α u F = ∑ θ, ∑ y, w θ y * F θ y := by
      unfold linearPayoff
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro θ _
      apply Finset.sum_congr rfl
      intro y _
      rw [← hweight]
      ring
    rwa [heq] at hmem
  refine ⟨α, u, hα, hu, ?_⟩
  have hstrict := hgap σ
  rw [hsource] at hstrict
  exact hstrict.trans_le (sub_le_sub_right htarget _)

/-- The range of optimized bounded decision disadvantages, allowing every
prior and utility, with the decision alphabet fixed to the target alphabet. -/
def finiteBayesValueGaps [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) : Set ℝ :=
  {c | ∃ (α : Θ → ℝ) (u : Θ → Y → ℝ), IsDist α ∧
    (∀ θ y, u θ y ∈ Set.Icc (0 : ℝ) 1) ∧
    c = finiteBayesValue F α u - finiteBayesValue E α u}

/-- Exact quantitative decision interpretation of directed deficiency.
Both experiments are optimized over all randomized decision rules. -/
theorem finiteDeficiency_eq_sSup_finiteBayesValueGaps
    [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    finiteDeficiency E F = sSup (finiteBayesValueGaps E F) := by
  classical
  have hbdd : BddAbove (finiteBayesValueGaps E F) := by
    refine ⟨finiteDeficiency E F, ?_⟩
    rintro _ ⟨α, u, hα, hu, rfl⟩
    exact finiteBayesValue_sub_le_finiteDeficiency E F hE hF α hα u hu
  have hne : (finiteBayesValueGaps E F).Nonempty :=
    ⟨_, uniformPrior Θ, fun _ _ => 0, isDist_uniformPrior,
      fun _ _ => ⟨le_rfl, zero_le_one⟩, rfl⟩
  apply le_antisymm
  · by_contra h
    obtain ⟨α, u, hα, hu, hgap⟩ := exists_finiteBayesValue_gap_gt_of_lt_finiteDeficiency
      E F hE hF (lt_of_not_ge h)
    have hle := le_csSup hbdd (show
      finiteBayesValue F α u - finiteBayesValue E α u ∈ finiteBayesValueGaps E F
      from ⟨α, u, hα, hu, rfl⟩)
    exact (not_lt_of_ge hle) hgap
  · apply csSup_le hne
    rintro _ ⟨α, u, hα, hu, rfl⟩
    exact finiteBayesValue_sub_le_finiteDeficiency E F hE hF α hα u hu

end IdExp
