import Formal.FiniteProbability
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Blackwell order as universal downstream decision power

An experiment is a class-indexed family of observation laws. If F is a garbling of E, composing
any downstream rule for F with that garbling gives a rule for E with exactly the same
class-conditional action law. Thus the result is prior-free and utility-free. Optimization enters
only afterwards: whenever optimal rules exist, the optimal value under E is at least that under F.

The difficult reverse implication is the finite Blackwell separation theorem. Its precise interface
is isolated below as BlackwellValueConverse and proved in `BlackwellConverse.lean`; no converse
axiom is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option linter.unusedSectionVars false

namespace IdExp

/-- A statistical experiment: one observation law for each latent class. -/
abbrev Experiment (Θ X : Type*) [MeasurableSpace X] := Θ → Measure X

/-- F is Blackwell-below E when F can be obtained by garbling E. -/
def BlackwellLE {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (F : Experiment Θ Y) (E : Experiment Θ X) : Prop :=
  ∃ κ : Kernel X Y, IsMarkovKernel κ ∧
    ∀ θ, (E θ).bind (fun x => κ x) = F θ

/-- Every experiment is a garbling of itself. -/
theorem blackwellLE_refl {Θ X : Type*} [MeasurableSpace X]
    (E : Experiment Θ X) : BlackwellLE E E := by
  refine ⟨Kernel.id, inferInstance, fun θ => ?_⟩
  simp [Kernel.id, Kernel.deterministic_apply]

/-- Garblings compose, so the Blackwell relation is transitive. -/
theorem blackwellLE_trans {Θ X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (E : Experiment Θ X) (F : Experiment Θ Y) (G : Experiment Θ Z)
    (hFE : BlackwellLE F E) (hGF : BlackwellLE G F) : BlackwellLE G E := by
  obtain ⟨κ, hκ, hEκ⟩ := hFE
  obtain ⟨η, hη, hFη⟩ := hGF
  letI : IsMarkovKernel κ := hκ
  letI : IsMarkovKernel η := hη
  refine ⟨η.comp κ, inferInstance, fun θ => ?_⟩
  simp only [Kernel.comp_apply]
  rw [← Measure.bind_bind (Kernel.measurable κ).aemeasurable
    (Kernel.measurable η).aemeasurable, hEκ θ, hFη θ]

/-- The class-conditional terminal-action distribution produced by a rule. -/
noncomputable def actionLaw {Θ X D : Type*} [MeasurableSpace X] [MeasurableSpace D]
    (E : Experiment Θ X) (r : Kernel X D) (θ : Θ) : Measure D :=
  (E θ).bind (fun x => r x)

/-- E can reproduce the action law of every decision rule based on F. -/
def SimulatesAllRules {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (E : Experiment Θ X) (F : Experiment Θ Y) : Prop :=
  ∀ (D : Type) [MeasurableSpace D], ∀ rF : Kernel Y D, IsMarkovKernel rF →
    ∃ rE : Kernel X D, IsMarkovKernel rE ∧
      ∀ θ, actionLaw E rE θ = actionLaw F rF θ

/-- Constructive Blackwell theorem: every rule after a garbling is simulated
after the original experiment, class by class, by composing kernels. -/
theorem blackwellLE_simulatesAllRules {Θ X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (E : Experiment Θ X) (F : Experiment Θ Y) (h : BlackwellLE F E) :
    SimulatesAllRules E F := by
  obtain ⟨κ, hκ, hgarb⟩ := h
  intro D _ rF hrF
  letI : IsMarkovKernel κ := hκ
  letI : IsMarkovKernel rF := hrF
  refine ⟨rF.comp κ, inferInstance, fun θ => ?_⟩
  simp only [actionLaw, Kernel.comp_apply]
  rw [← Measure.bind_bind (Kernel.measurable κ).aemeasurable
    (Kernel.measurable rF).aemeasurable]
  rw [hgarb θ]

/-- Expected downstream utility for a prior, experiment, and randomized rule. -/
noncomputable def decisionValue {Θ X D : Type*} [Fintype Θ]
    [MeasurableSpace X] [MeasurableSpace D]
    (α : Θ → ℝ) (u : Θ → D → ℝ) (E : Experiment Θ X) (r : Kernel X D) : ℝ :=
  ∑ θ, α θ * ∫ d, u θ d ∂ actionLaw E r θ

/-- Equal class-conditional action laws have equal value for every prior and utility. -/
theorem decisionValue_eq_of_actionLaw_eq {Θ X Y : Type*} {D : Type} [Fintype Θ]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace D]
    (α : Θ → ℝ) (u : Θ → D → ℝ) (E : Experiment Θ X) (F : Experiment Θ Y)
    (rE : Kernel X D) (rF : Kernel Y D)
    (h : ∀ θ, actionLaw E rE θ = actionLaw F rF θ) :
    decisionValue α u E rE = decisionValue α u F rF := by
  unfold decisionValue
  apply Finset.sum_congr rfl
  intro θ _
  rw [h θ]

/-- For every prior, utility, action space, and rule based on F, E has a rule
with exactly the same value. -/
theorem blackwellLE_preserves_every_decision_value {Θ X Y : Type*} [Fintype Θ]
    [MeasurableSpace X] [MeasurableSpace Y]
    (E : Experiment Θ X) (F : Experiment Θ Y) (h : BlackwellLE F E)
    (D : Type) [MeasurableSpace D] (α : Θ → ℝ) (u : Θ → D → ℝ)
    (rF : Kernel Y D) (hrF : IsMarkovKernel rF) :
    ∃ rE : Kernel X D, IsMarkovKernel rE ∧
      decisionValue α u E rE = decisionValue α u F rF := by
  obtain ⟨rE, hrE, hlaw⟩ := blackwellLE_simulatesAllRules E F h D rF hrF
  exact ⟨rE, hrE, decisionValue_eq_of_actionLaw_eq α u E F rE rF hlaw⟩

/-- A rule is optimal when it weakly beats every Markov decision rule. -/
def IsOptimalRule {Θ X D : Type*} [Fintype Θ]
    [MeasurableSpace X] [MeasurableSpace D]
    (α : Θ → ℝ) (u : Θ → D → ℝ) (E : Experiment Θ X) (r : Kernel X D) : Prop :=
  IsMarkovKernel r ∧ ∀ s : Kernel X D, IsMarkovKernel s →
    decisionValue α u E s ≤ decisionValue α u E r

/-- If F has an optimal rule, E has a rule attaining at least that value. -/
theorem exists_rule_ge_optimal_of_blackwellLE {Θ X Y : Type*} {D : Type} [Fintype Θ]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace D]
    (α : Θ → ℝ) (u : Θ → D → ℝ) (E : Experiment Θ X) (F : Experiment Θ Y)
    (h : BlackwellLE F E) (rF : Kernel Y D) (hoptF : IsOptimalRule α u F rF) :
    ∃ rE : Kernel X D, IsMarkovKernel rE ∧
      decisionValue α u F rF ≤ decisionValue α u E rE := by
  obtain ⟨rE, hrE, hval⟩ :=
    blackwellLE_preserves_every_decision_value E F h D α u rF hoptF.1
  exact ⟨rE, hrE, hval.ge⟩

/-- Whenever optimal rules are supplied on both experiments, the optimum after
the more informative experiment is no smaller. -/
theorem optimal_value_mono_of_blackwellLE {Θ X Y : Type*} {D : Type} [Fintype Θ]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace D]
    (α : Θ → ℝ) (u : Θ → D → ℝ) (E : Experiment Θ X) (F : Experiment Θ Y)
    (h : BlackwellLE F E) (rE : Kernel X D) (rF : Kernel Y D)
    (hoptE : IsOptimalRule α u E rE) (hoptF : IsOptimalRule α u F rF) :
    decisionValue α u F rF ≤ decisionValue α u E rE := by
  obtain ⟨sE, hsE, hval⟩ :=
    exists_rule_ge_optimal_of_blackwellLE α u E F h rF hoptF
  exact hval.trans (hoptE.2 sE hsE)

/-- A strict reversal in optimal downstream value certifies failure of the proposed
Blackwell dominance. Decision problems are therefore separating witnesses for the order. -/
theorem not_blackwellLE_of_optimal_value_lt {Θ X Y : Type*} {D : Type} [Fintype Θ]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace D]
    (α : Θ → ℝ) (u : Θ → D → ℝ) (E : Experiment Θ X) (F : Experiment Θ Y)
    (rE : Kernel X D) (rF : Kernel Y D)
    (hoptE : IsOptimalRule α u E rE) (hoptF : IsOptimalRule α u F rF)
    (hlt : decisionValue α u E rE < decisionValue α u F rF) :
    ¬ BlackwellLE F E := by
  intro h
  exact (not_lt_of_ge (optimal_value_mono_of_blackwellLE α u E F h rE rF hoptE hoptF)) hlt

/-- Two downstream tasks preferring opposite experiments certify Blackwell incomparability. -/
theorem blackwell_incomparable_of_opposite_task_witnesses
    {Θ X Y : Type*} {D₁ D₂ : Type} [Fintype Θ]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace D₁] [MeasurableSpace D₂]
    (E : Experiment Θ X) (F : Experiment Θ Y)
    (α₁ : Θ → ℝ) (u₁ : Θ → D₁ → ℝ) (e₁ : Kernel X D₁) (f₁ : Kernel Y D₁)
    (oe₁ : IsOptimalRule α₁ u₁ E e₁) (of₁ : IsOptimalRule α₁ u₁ F f₁)
    (h₁ : decisionValue α₁ u₁ E e₁ < decisionValue α₁ u₁ F f₁)
    (α₂ : Θ → ℝ) (u₂ : Θ → D₂ → ℝ) (e₂ : Kernel X D₂) (f₂ : Kernel Y D₂)
    (oe₂ : IsOptimalRule α₂ u₂ E e₂) (of₂ : IsOptimalRule α₂ u₂ F f₂)
    (h₂ : decisionValue α₂ u₂ F f₂ < decisionValue α₂ u₂ E e₂) :
    ¬ BlackwellLE F E ∧ ¬ BlackwellLE E F :=
  ⟨not_blackwellLE_of_optimal_value_lt α₁ u₁ E F e₁ f₁ oe₁ of₁ h₁,
    not_blackwellLE_of_optimal_value_lt α₂ u₂ F E f₂ e₂ of₂ oe₂ h₂⟩

/-- Blackwell-equivalent experiments simulate all rules in both directions. -/
theorem blackwell_equiv_simulates_both_ways {Θ X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (E : Experiment Θ X) (F : Experiment Θ Y)
    (hEF : BlackwellLE F E) (hFE : BlackwellLE E F) :
    SimulatesAllRules E F ∧ SimulatesAllRules F E :=
  ⟨blackwellLE_simulatesAllRules E F hEF, blackwellLE_simulatesAllRules F E hFE⟩

/-- Full revelation as an ordinary experiment. -/
noncomputable def fullExperiment (Θ : Type*) [MeasurableSpace Θ] : Experiment Θ Θ :=
  fun θ => Measure.dirac θ

/-- Universal rule simulation recovers the garbling: ask to simulate the identity rule on F. -/
theorem simulatesAllRules_blackwellLE {Θ X Y : Type}
    [MeasurableSpace X] [MeasurableSpace Y]
    (E : Experiment Θ X) (F : Experiment Θ Y)
    (h : SimulatesAllRules E F) : BlackwellLE F E := by
  let ident : Kernel Y Y := Kernel.id
  have hi : IsMarkovKernel ident := inferInstance
  obtain ⟨rE, hrE, hlaw⟩ := h Y ident hi
  refine ⟨rE, hrE, fun θ => ?_⟩
  have hθ := hlaw θ
  simpa [actionLaw, ident, Kernel.id_comp] using hθ

/-- Behavioral form of Blackwell's theorem: garbling is equivalent to universal
class-conditional simulation of downstream rules. This direction needs no separation theorem. -/
theorem blackwellLE_iff_simulatesAllRules {Θ X Y : Type}
    [MeasurableSpace X] [MeasurableSpace Y]
    (E : Experiment Θ X) (F : Experiment Θ Y) :
    BlackwellLE F E ↔ SimulatesAllRules E F :=
  ⟨blackwellLE_simulatesAllRules E F, simulatesAllRules_blackwellLE E F⟩

/-- **The separating-hyperplane core of Blackwell's value converse.**
If a point has no smaller value than some feasible point for every continuous linear payoff,
then it belongs to every closed convex capability menu. The contrapositive is the Blackwell
separation argument: a point outside the menu is strictly preferred by one downstream task. -/
theorem mem_closedConvex_of_universal_value
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [LocallyConvexSpace ℝ V]
    (C : Set V) (hconv : Convex ℝ C) (hclosed : IsClosed C) (x : V)
    (hvalue : ∀ f : StrongDual ℝ V, ∃ c ∈ C, f x ≤ f c) :
    x ∈ C := by
  by_contra hx
  obtain ⟨f, t, hC, hxf⟩ :=
    geometric_hahn_banach_closed_point hconv hclosed hx
  obtain ⟨c, hc, hle⟩ := hvalue f
  exact (not_lt_of_ge hle) ((hC c hc).trans hxf)

/-- Membership in a closed convex capability menu is equivalent to weakly winning every
linear decision problem against some feasible behavior. This is the scalar-value form of
the Blackwell capability theorem. -/
theorem mem_closedConvex_iff_universal_value
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [LocallyConvexSpace ℝ V]
    (C : Set V) (hconv : Convex ℝ C) (hclosed : IsClosed C) (x : V) :
    x ∈ C ↔ ∀ f : StrongDual ℝ V, ∃ c ∈ C, f x ≤ f c := by
  constructor
  · intro hx f
    exact ⟨x, hx, le_rfl⟩
  · exact mem_closedConvex_of_universal_value C hconv hclosed x

/-- Coordinates of a finite class-conditional action law. -/
noncomputable def finiteActionVector {Θ X D : Type*} [MeasurableSpace X] [MeasurableSpace D]
    (E : Experiment Θ X) (r : Kernel X D) : Θ → D → ℝ :=
  fun θ d => (actionLaw E r θ).real {d}

/-- The capability menu of an experiment for a fixed finite action space, represented by its
class-conditional action probabilities. -/
def finiteCapabilityMenu {Θ X D : Type*} [MeasurableSpace X] [MeasurableSpace D]
    (E : Experiment Θ X) : Set (Θ → D → ℝ) :=
  {v | ∃ r : Kernel X D, IsMarkovKernel r ∧ finiteActionVector E r = v}

/-- **Blackwell value converse, conditional only on the standard menu geometry.**
For finite discrete spaces the rule menu is closed and convex. If every linear payoff of F's
identity rule can be matched by a rule after E, separation puts that identity law in E's menu;
the witnessing rule is exactly a garbling from E to F. -/
theorem blackwellLE_of_universal_linear_value
    {Θ X Y : Type} [Fintype Θ] [Fintype X] [Fintype Y]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (E : Experiment Θ X) (F : Experiment Θ Y)
    (hEprob : ∀ θ, IsProbabilityMeasure (E θ))
    (hFprob : ∀ θ, IsProbabilityMeasure (F θ))
    (hconv : Convex ℝ (finiteCapabilityMenu (D := Y) E))
    (hclosed : IsClosed (finiteCapabilityMenu (D := Y) E))
    (hvalue : ∀ f : StrongDual ℝ (Θ → Y → ℝ),
      ∃ rE : Kernel X Y, IsMarkovKernel rE ∧
        f (finiteActionVector F Kernel.id) ≤ f (finiteActionVector E rE)) :
    BlackwellLE F E := by
  have hmem : finiteActionVector F Kernel.id ∈ finiteCapabilityMenu (D := Y) E := by
    apply mem_closedConvex_of_universal_value
      (finiteCapabilityMenu (D := Y) E) hconv hclosed
    intro f
    obtain ⟨rE, hrE, hle⟩ := hvalue f
    exact ⟨finiteActionVector E rE, ⟨rE, hrE, rfl⟩, hle⟩
  obtain ⟨rE, hrE, hlaw⟩ := hmem
  refine ⟨rE, hrE, fun θ => ?_⟩
  letI : IsMarkovKernel rE := hrE
  letI : IsProbabilityMeasure (E θ) := hEprob θ
  letI : IsProbabilityMeasure (F θ) := hFprob θ
  have hi : IsMarkovKernel (Kernel.id : Kernel Y Y) := inferInstance
  letI : IsMarkovKernel (Kernel.id : Kernel Y Y) := hi
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro y
  have hcoord := congrFun (congrFun hlaw θ) y
  simpa [finiteActionVector, actionLaw, Kernel.id_comp] using hcoord

/-- Under the finite menu's closed-convex geometry, Blackwell dominance is equivalent
to dominance for every linear downstream value functional. The forward direction composes the
identity rule; the reverse direction is `blackwellLE_of_universal_linear_value`. -/
theorem blackwellLE_iff_universal_linear_value
    {Θ X Y : Type} [Fintype Θ] [Fintype X] [Fintype Y]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (E : Experiment Θ X) (F : Experiment Θ Y)
    (hEprob : ∀ θ, IsProbabilityMeasure (E θ))
    (hFprob : ∀ θ, IsProbabilityMeasure (F θ))
    (hconv : Convex ℝ (finiteCapabilityMenu (D := Y) E))
    (hclosed : IsClosed (finiteCapabilityMenu (D := Y) E)) :
    BlackwellLE F E ↔
      ∀ f : StrongDual ℝ (Θ → Y → ℝ),
        ∃ rE : Kernel X Y, IsMarkovKernel rE ∧
          f (finiteActionVector F Kernel.id) ≤ f (finiteActionVector E rE) := by
  constructor
  · intro h f
    obtain ⟨rE, hrE, hlaw⟩ :=
      blackwellLE_simulatesAllRules E F h Y Kernel.id inferInstance
    refine ⟨rE, hrE, ?_⟩
    have hv : finiteActionVector E rE = finiteActionVector F Kernel.id := by
      funext θ y
      simp only [finiteActionVector]
      rw [hlaw θ]
    rw [hv]
  · exact blackwellLE_of_universal_linear_value E F hEprob hFprob hconv hclosed

/-- Exact interface for the classical finite value converse. Unlike rule simulation,
recovering a garbling from inequalities between optimized scalar values is the
finite-dimensional separating-hyperplane content of Blackwell's theorem.
Proved in `Formal/BlackwellConverse.lean` (`blackwellValueConverse`). -/
def BlackwellValueConverse : Prop :=
  ∀ (Θ X Y : Type) [Fintype Θ] [Fintype X] [Fintype Y] [Nonempty Θ]
    [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y],
    ∀ (E : Experiment Θ X) (F : Experiment Θ Y),
      (∀ θ, IsProbabilityMeasure (E θ)) →
      (∀ θ, IsProbabilityMeasure (F θ)) →
      (∀ (D : Type) [Fintype D] [Nonempty D] [MeasurableSpace D]
        [MeasurableSingletonClass D], ∀ (α : Θ → ℝ), IsDist α → ∀ (u : Θ → D → ℝ)
          (rE : Kernel X D) (rF : Kernel Y D),
          IsOptimalRule α u E rE → IsOptimalRule α u F rF →
          decisionValue α u F rF ≤ decisionValue α u E rE) →
      BlackwellLE F E

end IdExp
