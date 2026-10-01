import Formal.Experiment
import Mathlib.Analysis.Convex.StdSimplex

/-!
# The finite Blackwell value converse

This file proves the separating-hyperplane direction of Blackwell's theorem in its native
finite stochastic-matrix form. A randomized decision rule is a row-stochastic matrix. Its
class-conditional action law is the matrix product with the experiment. The attainable menu is
therefore a compact convex image of a product of simplices. Dominance of every linear optimized
value forces the target experiment into that menu, which is precisely existence of a garbling.
-/

open Set

namespace IdExp

/-- A finite experiment written as its stochastic matrix. Row normalization is carried separately
by `IsFiniteExperiment`. -/
abbrev FiniteExperiment (Θ X : Type*) := Θ → X → ℝ

/-- Every row of a finite experiment is a probability vector. -/
def IsFiniteExperiment {Θ X : Type*} [Fintype X] (E : FiniteExperiment Θ X) : Prop :=
  ∀ θ, E θ ∈ stdSimplex ℝ X

/-- The compact convex set of randomized rules from observations `X` to actions `D`. -/
def stochasticRules (X D : Type*) [Fintype D] : Set (X → D → ℝ) :=
  Set.univ.pi fun _ => stdSimplex ℝ D

theorem convex_stochasticRules (X D : Type*) [Fintype D] :
    Convex ℝ (stochasticRules X D) := by
  exact convex_pi fun _ _ => convex_stdSimplex ℝ D

theorem isCompact_stochasticRules (X D : Type*) [Fintype D] :
    IsCompact (stochasticRules X D) := by
  exact isCompact_univ_pi fun _ => isCompact_stdSimplex ℝ D

/-- Class-conditional action probabilities obtained by applying a randomized rule. -/
def finiteDecisionLaw {Θ X D : Type*} [Fintype X]
    (E : FiniteExperiment Θ X) (q : X → D → ℝ) : Θ → D → ℝ :=
  fun θ d => ∑ x, E θ x * q x d


/-- A stochastic post-processing of a finite stochastic experiment is again a
finite stochastic experiment.  The parameter type need not be finite. -/
theorem finiteDecisionLaw_valid
    {Θ X Y : Type*} [Fintype X] [Fintype Y]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) :
    IsFiniteExperiment (finiteDecisionLaw E G) := by
  intro θ
  constructor
  · intro y
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg ((hE θ).1 x) ((hG x (Set.mem_univ x)).1 y)
  · unfold finiteDecisionLaw
    rw [Finset.sum_comm]
    calc
      ∑ x, ∑ y, E θ x * G x y = ∑ x, E θ x * ∑ y, G x y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
      _ = ∑ x, E θ x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [(hG x (Set.mem_univ x)).2, mul_one]
      _ = 1 := (hE θ).2


/-- Composition of two finite stochastic rules, written as matrix
multiplication. -/
noncomputable def stochasticRuleComp {X Y Z : Type*} [Fintype Y]
    (G : X → Y → ℝ) (H : Y → Z → ℝ) : X → Z → ℝ :=
  fun x z => ∑ y, G x y * H y z

/-- The composite of row-stochastic rules is row-stochastic. -/
theorem stochasticRuleComp_mem_stochasticRules
    {X Y Z : Type*} [Fintype Y] [Fintype Z]
    {G : X → Y → ℝ} (hG : G ∈ stochasticRules X Y)
    {H : Y → Z → ℝ} (hH : H ∈ stochasticRules Y Z) :
    stochasticRuleComp G H ∈ stochasticRules X Z := by
  intro x _
  exact finiteDecisionLaw_valid G (fun x => hG x (Set.mem_univ x)) H hH x

/-- Applying a composite rule is the same as applying its two factors in
sequence. -/
theorem finiteDecisionLaw_stochasticRuleComp
    {Θ X Y Z : Type*} [Fintype X] [Fintype Y]
    (E : FiniteExperiment Θ X) (G : X → Y → ℝ) (H : Y → Z → ℝ) :
    finiteDecisionLaw E (stochasticRuleComp G H) =
      finiteDecisionLaw (finiteDecisionLaw E G) H := by
  funext θ z
  unfold finiteDecisionLaw stochasticRuleComp
  calc
    ∑ x, E θ x * ∑ y, G x y * H y z =
        ∑ x, ∑ y, (E θ x * G x y) * H y z := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ∑ y, ∑ x, (E θ x * G x y) * H y z := Finset.sum_comm
    _ = ∑ y, (∑ x, E θ x * G x y) * H y z := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]

theorem continuous_finiteDecisionLaw {Θ X D : Type*} [Fintype X]
    (E : FiniteExperiment Θ X) : Continuous (finiteDecisionLaw (D := D) E) := by
  unfold finiteDecisionLaw
  fun_prop

/-- The downstream capability menu of a finite experiment for action space `D`. -/
def finiteMatrixCapabilityMenu {Θ X D : Type*} [Fintype X] [Fintype D]
    (E : FiniteExperiment Θ X) : Set (Θ → D → ℝ) :=
  finiteDecisionLaw E '' stochasticRules X D

theorem isCompact_finiteMatrixCapabilityMenu {Θ X D : Type*} [Fintype X] [Fintype D]
    (E : FiniteExperiment Θ X) : IsCompact (finiteMatrixCapabilityMenu (D := D) E) :=
  (isCompact_stochasticRules X D).image (continuous_finiteDecisionLaw E)

theorem isClosed_finiteMatrixCapabilityMenu {Θ X D : Type*} [Fintype X] [Fintype D]
    (E : FiniteExperiment Θ X) : IsClosed (finiteMatrixCapabilityMenu (D := D) E) :=
  (isCompact_finiteMatrixCapabilityMenu E).isClosed

theorem convex_finiteMatrixCapabilityMenu {Θ X D : Type*} [Fintype X] [Fintype D]
    (E : FiniteExperiment Θ X) : Convex ℝ (finiteMatrixCapabilityMenu (D := D) E) := by
  rintro _ ⟨q, hq, rfl⟩ _ ⟨r, hr, rfl⟩ a b ha hb hab
  refine ⟨a • q + b • r, convex_stochasticRules X D hq hr ha hb hab, ?_⟩
  funext θ d
  simp only [finiteDecisionLaw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    ∑ x, E θ x * (a * q x d + b * r x d) =
        ∑ x, (a * (E θ x * q x d) + b * (E θ x * r x d)) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = a * ∑ x, E θ x * q x d + b * ∑ x, E θ x * r x d := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Matrix Blackwell dominance: `F` is obtainable by a stochastic garbling of `E`. -/
def FiniteBlackwellLE {Θ X Y : Type*} [Fintype X] [Fintype Y]
    (F : FiniteExperiment Θ Y) (E : FiniteExperiment Θ X) : Prop :=
  F ∈ finiteMatrixCapabilityMenu (D := Y) E

/-- The identity stochastic rule belongs to the rule simplex on every finite space. -/
theorem identity_mem_stochasticRules (Y : Type*) [Fintype Y] [DecidableEq Y] :
    (fun y d : Y => if y = d then (1 : ℝ) else 0) ∈ stochasticRules Y Y := by
  classical
  intro y _
  constructor
  · intro d
    by_cases h : y = d <;> simp [h]
  · simp

/-- Every finite experiment is in its own capability menu, via the identity rule. -/
theorem self_mem_finiteMatrixCapabilityMenu
    {Θ Y : Type*} [Fintype Y] (F : FiniteExperiment Θ Y) :
    F ∈ finiteMatrixCapabilityMenu (D := Y) F := by
  classical
  let ident : Y → Y → ℝ := fun y d => if y = d then 1 else 0
  refine ⟨ident, identity_mem_stochasticRules Y, ?_⟩
  funext θ d
  simp [finiteDecisionLaw, ident]

/-- Finite Blackwell comparison is reflexive, including on an empty signal
space (where the row condition is vacuous). -/
theorem finiteBlackwellLE_refl
    {Θ Y : Type*} [Fintype Y] (F : FiniteExperiment Θ Y) :
    FiniteBlackwellLE F F :=
  self_mem_finiteMatrixCapabilityMenu F

/-- Finite Blackwell comparison is transitive: composing the two garblings
composes their stochastic matrices. -/
theorem finiteBlackwellLE_trans
    {Θ X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {F : FiniteExperiment Θ X} {E : FiniteExperiment Θ Y}
    {D : FiniteExperiment Θ Z}
    (hFE : FiniteBlackwellLE F E) (hED : FiniteBlackwellLE E D) :
    FiniteBlackwellLE F D := by
  obtain ⟨G, hG, hEG⟩ := hFE
  obtain ⟨H, hH, hDH⟩ := hED
  refine ⟨stochasticRuleComp H G,
    stochasticRuleComp_mem_stochasticRules hH hG, ?_⟩
  rw [finiteDecisionLaw_stochasticRuleComp, hDH, hEG]

/-- Universal optimized linear-value dominance. The existential feasible law is the optimizer-free
form of `sup_{z in M(E)} f z ≥ f F`; compactness guarantees an optimizer if one is desired. -/
def DominatesEveryFiniteValue {Θ X Y : Type*} [Fintype Θ] [Fintype X] [Fintype Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) : Prop :=
  ∀ f : StrongDual ℝ (Θ → Y → ℝ),
    ∃ z ∈ finiteMatrixCapabilityMenu (D := Y) E, f F ≤ f z

/-- Failure of finite Blackwell dominance has a single strict downstream-value witness.
This is the operational separation half: some task values `F` above every law attainable from `E`. -/
theorem exists_strict_value_witness_of_not_finiteBlackwellLE
    {Θ X Y : Type*} [Fintype Θ] [Fintype X] [Fintype Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (h : ¬ FiniteBlackwellLE F E) :
    ∃ f : StrongDual ℝ (Θ → Y → ℝ),
      ∀ z ∈ finiteMatrixCapabilityMenu (D := Y) E, f z < f F := by
  obtain ⟨f, t, hmenu, hF⟩ := geometric_hahn_banach_closed_point
    (convex_finiteMatrixCapabilityMenu E)
    (isClosed_finiteMatrixCapabilityMenu E) h
  exact ⟨f, fun z hz => (hmenu z hz).trans hF⟩

/-- Non-garbling is equivalent to existence of a strict separating decision problem. -/
theorem not_finiteBlackwellLE_iff_exists_strict_value_witness
    {Θ X Y : Type*} [Fintype Θ] [Fintype X] [Fintype Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) :
    ¬ FiniteBlackwellLE F E ↔
      ∃ f : StrongDual ℝ (Θ → Y → ℝ),
        ∀ z ∈ finiteMatrixCapabilityMenu (D := Y) E, f z < f F := by
  constructor
  · exact exists_strict_value_witness_of_not_finiteBlackwellLE E F
  · rintro ⟨f, hf⟩ hmem
    exact (lt_irrefl (f F)) (hf F hmem)

/-- **Finite Blackwell value converse.** If `E` weakly outperforms `F` for every linear downstream
value functional, then `F` is a stochastic garbling of `E`. -/
theorem finiteBlackwellLE_of_dominatesEveryFiniteValue
    {Θ X Y : Type*} [Fintype Θ] [Fintype X] [Fintype Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (h : DominatesEveryFiniteValue E F) : FiniteBlackwellLE F E := by
  exact mem_closedConvex_of_universal_value
    (finiteMatrixCapabilityMenu (D := Y) E)
    (convex_finiteMatrixCapabilityMenu E)
    (isClosed_finiteMatrixCapabilityMenu E) F h

/-- Literal optimized-menu comparison: for every finite action space and linear decision payoff,
every behavior attainable after `F` is weakly beaten in value by some behavior attainable after
`E`. Compactness lets one equivalently speak of maximum values. -/
def DominatesEveryOptimizedFiniteValue
    {Θ X Y : Type} [Fintype Θ] [Fintype X] [Fintype Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) : Prop :=
  ∀ (D : Type) [Fintype D], ∀ f : StrongDual ℝ (Θ → D → ℝ),
    ∀ zF ∈ finiteMatrixCapabilityMenu (D := D) F,
      ∃ zE ∈ finiteMatrixCapabilityMenu (D := D) E, f zF ≤ f zE

/-- **Blackwell's optimized-value converse.** If the best attainable value after `E` is at least
the best attainable value after `F` in every finite linear decision problem, then `F` is a
stochastic garbling of `E`. Only the action space `Y` and F's identity rule are needed. -/
theorem finiteBlackwellLE_of_dominatesEveryOptimizedFiniteValue
    {Θ X Y : Type} [Fintype Θ] [Fintype X] [Fintype Y] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (h : DominatesEveryOptimizedFiniteValue E F) : FiniteBlackwellLE F E := by
  apply finiteBlackwellLE_of_dominatesEveryFiniteValue E F
  intro f
  exact h Y f F (self_mem_finiteMatrixCapabilityMenu F)

/-- The complete finite Blackwell theorem in value form. Membership in the garbling menu is
 equivalent to dominance for every downstream linear value functional. -/
theorem finiteBlackwellLE_iff_dominatesEveryFiniteValue
    {Θ X Y : Type*} [Fintype Θ] [Fintype X] [Fintype Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) :
    FiniteBlackwellLE F E ↔ DominatesEveryFiniteValue E F := by
  constructor
  · intro h f
    exact ⟨F, h, le_rfl⟩
  · exact finiteBlackwellLE_of_dominatesEveryFiniteValue E F

end IdExp
