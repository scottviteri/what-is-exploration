import Formal.BlackwellConverse

/-!
# Blackwell's value converse for an arbitrary parameter class

Finite observation alphabets make the stochastic-decoder space compact even when the parameter
class is infinite.  Consequently, if every finite restriction of two experiments admits a
garbling, one decoder works on the whole class: otherwise finitely many closed decoder constraints
would already have empty intersection.  Combining this compactness lemma with the finite value
converse removes the `Fintype Θ` assumption from the project-relevant finite-signal theorem.

The operational hypothesis quantifies over every nonempty finite subset of parameters, every
finite downstream action space, every prior on that subset, and every utility.  Equivalently, it
quantifies over all finitely supported decision problems on an arbitrary parameter class.
-/

open MeasureTheory ProbabilityTheory
open Set
open scoped ENNReal
set_option linter.unusedSectionVars false

namespace IdExp

section MatrixCompactness

variable {Θ X Y : Type*} [Fintype X] [Fintype Y]

/-- Restrict a finite-signal experiment to a finite subset of an otherwise arbitrary parameter
class. -/
def restrictFiniteExperiment (S : Finset Θ) (E : FiniteExperiment Θ X) :
    FiniteExperiment {θ // θ ∈ S} X :=
  fun θ => E θ.1

/-- The closed constraint that a stochastic matrix decode `E θ` exactly into `F θ`.  Stochasticity
is kept in the ambient compact set `stochasticRules X Y`. -/
def exactDecoderConstraint (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) (θ : Θ) :
    Set (X → Y → ℝ) :=
  {G | finiteDecisionLaw E G θ = F θ}

theorem isClosed_exactDecoderConstraint (E : FiniteExperiment Θ X)
    (F : FiniteExperiment Θ Y) (θ : Θ) :
    IsClosed (exactDecoderConstraint E F θ) := by
  unfold exactDecoderConstraint
  exact isClosed_eq
    ((continuous_apply θ).comp (continuous_finiteDecisionLaw (D := Y) E)) continuous_const

/-- **Finite-witness compactness for garblings.**  With finite signal alphabets, if every finite
set of parameters has a common stochastic decoder from `E` to `F`, then one decoder works for all
parameters simultaneously.  The parameter type itself is completely arbitrary. -/
theorem finiteBlackwellLE_of_all_finite_restrictions
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hlocal : ∀ S : Finset Θ,
      FiniteBlackwellLE (restrictFiniteExperiment S F) (restrictFiniteExperiment S E)) :
    FiniteBlackwellLE F E := by
  have hfinite : ∀ S : Finset Θ,
      (stochasticRules X Y ∩ ⋂ θ ∈ S, exactDecoderConstraint E F θ).Nonempty := by
    intro S
    obtain ⟨G, hG, hdecode⟩ := hlocal S
    refine ⟨G, hG, ?_⟩
    simp only [mem_iInter]
    intro θ hθ
    change finiteDecisionLaw E G θ = F θ
    have hθ' := congrFun (congrFun hdecode ⟨θ, hθ⟩)
    exact funext hθ'
  obtain ⟨G, hG, hall⟩ :=
    (isCompact_stochasticRules X Y).inter_iInter_nonempty
      (exactDecoderConstraint E F)
      (isClosed_exactDecoderConstraint E F) hfinite
  refine ⟨G, hG, ?_⟩
  funext θ y
  exact congrFun (mem_iInter.mp hall θ) y

end MatrixCompactness

section KernelCompactness

variable {Θ X Y : Type} [Fintype X] [Fintype Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSingletonClass X] [MeasurableSingletonClass Y]

/-- Restrict a measure-kernel experiment to a finite subset of its parameter class. -/
def restrictExperiment (S : Finset Θ) (E : Experiment Θ X) :
    Experiment {θ // θ ∈ S} X :=
  fun θ => E θ.1

/-- A global garbling remains a garbling after restricting the parameter class. -/
theorem blackwellLE_restrictExperiment
    (E : Experiment Θ X) (F : Experiment Θ Y) (S : Finset Θ)
    (h : BlackwellLE F E) :
    BlackwellLE (restrictExperiment S F) (restrictExperiment S E) := by
  obtain ⟨κ, hκ, hdecode⟩ := h
  exact ⟨κ, hκ, fun θ => hdecode θ.1⟩


/-- Exact Blackwell dominance on every finite parameter restriction implies exact dominance on the
whole arbitrary parameter class, provided the two signal alphabets are finite. -/
theorem blackwellLE_of_all_finite_restrictions
    (E : Experiment Θ X) (F : Experiment Θ Y)
    (hE : ∀ θ, IsProbabilityMeasure (E θ))
    (hF : ∀ θ, IsProbabilityMeasure (F θ))
    (hlocal : ∀ S : Finset Θ,
      BlackwellLE (restrictExperiment S F) (restrictExperiment S E)) :
    BlackwellLE F E := by
  have hmatrix : FiniteBlackwellLE (matrixOf F) (matrixOf E) := by
    apply finiteBlackwellLE_of_all_finite_restrictions
    intro S
    obtain ⟨κ, hκ, hdecode⟩ := hlocal S
    letI : IsMarkovKernel κ := hκ
    refine ⟨ruleMatrix κ, ruleMatrix_mem_stochasticRules κ, ?_⟩
    change finiteDecisionLaw (matrixOf (restrictExperiment S E)) (ruleMatrix κ) =
      matrixOf (restrictExperiment S F)
    funext θ y
    have hbind := congrArg (fun μ : Measure Y => μ.real {y}) (hdecode θ)
    have haction := congrFun
      (congrFun
        (finiteActionVector_eq_finiteDecisionLaw
          (restrictExperiment S E) (fun θ => hE θ.1) κ) θ) y
    simpa [restrictFiniteExperiment, restrictExperiment, matrixOf, finiteActionVector,
      actionLaw] using haction.symm.trans hbind
  obtain ⟨G, hG, hGF⟩ := hmatrix
  have hM := isMarkovKernel_kernelOfMatrix G hG
  refine ⟨kernelOfMatrix G, hM, fun θ => ?_⟩
  letI : IsMarkovKernel (kernelOfMatrix G) := hM
  have haction := congrFun
    (congrFun (finiteActionVector_eq_finiteDecisionLaw E hE (kernelOfMatrix G)) θ)
  rw [ruleMatrix_kernelOfMatrix G hG] at haction
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro y
  have hGFθ := congrFun (congrFun hGF θ) y
  exact haction y |>.trans hGFθ

/-- Decision-value dominance on all finite parameter restrictions.  This is the prior-free way to
state "all finitely supported priors": each decision problem names a nonempty finite subset `S` of
the arbitrary parameter class, then chooses any prior and utility on `S`. -/
def DominatesEveryFiniteRestrictionValue
    (E : Experiment Θ X) (F : Experiment Θ Y) : Prop :=
  ∀ (S : Finset Θ), S.Nonempty →
    ∀ (D : Type) [Fintype D] [Nonempty D] [MeasurableSpace D]
      [MeasurableSingletonClass D],
      ∀ (α : {θ // θ ∈ S} → ℝ), IsDist α →
      ∀ (u : {θ // θ ∈ S} → D → ℝ)
        (rE : Kernel X D) (rF : Kernel Y D),
        IsOptimalRule α u (restrictExperiment S E) rE →
        IsOptimalRule α u (restrictExperiment S F) rF →
        decisionValue α u (restrictExperiment S F) rF ≤
          decisionValue α u (restrictExperiment S E) rE

/-- **Arbitrary-parameter, finite-signal Blackwell value converse.**  Let the parameter class be
arbitrary and the two signal alphabets finite.  If `E` has at least the optimized value of `F` for
every finite-support prior and every finite downstream decision problem, then one world-independent
Markov kernel garbles `E` into `F` on the entire parameter class.

Only the signal and downstream action alphabets are finite; `Θ` has no finiteness, countability,
measurable-space, or topological assumption. -/
theorem blackwellValueConverse_arbitraryParameter
    (E : Experiment Θ X) (F : Experiment Θ Y)
    [Nonempty Θ]
    (hE : ∀ θ, IsProbabilityMeasure (E θ))
    (hF : ∀ θ, IsProbabilityMeasure (F θ))
    (hval : DominatesEveryFiniteRestrictionValue E F) :
    BlackwellLE F E := by
  apply blackwellLE_of_all_finite_restrictions E F hE hF
  intro S
  by_cases hS : S.Nonempty
  · letI : Nonempty {θ // θ ∈ S} := by
      obtain ⟨θ, hθ⟩ := hS
      exact ⟨⟨θ, hθ⟩⟩
    apply blackwellValueConverse
    · exact fun θ => hE θ.1
    · exact fun θ => hF θ.1
    · exact hval S hS
  · have hempty : IsEmpty {θ // θ ∈ S} := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      infer_instance
    letI : IsEmpty {θ // θ ∈ S} := hempty
    have hY : Nonempty Y := by
      obtain ⟨θ⟩ := ‹Nonempty Θ›
      by_contra h
      rw [not_nonempty_iff] at h
      have h0 : (F θ) Set.univ = 0 := by
        rw [Set.univ_eq_empty_iff.mpr h, measure_empty]
      rw [measure_univ] at h0
      exact one_ne_zero h0
    letI : Nonempty Y := hY
    classical
    let q : X → Y → ℝ := fun _ y => if y = Classical.choice hY then 1 else 0
    have hq : q ∈ stochasticRules X Y := by
      intro x _
      constructor
      · intro y
        by_cases hy : y = Classical.choice hY <;> simp [q, hy]
      · simp [q]
    have hk := isMarkovKernel_kernelOfMatrix q hq
    refine ⟨kernelOfMatrix q, hk, fun θ => isEmptyElim θ⟩

/-- The complete finite-signal Blackwell theorem for an arbitrary parameter class.  Exact
garbling is equivalent to optimized-value dominance on every finite restriction, hence to
dominance for every finitely supported prior and finite downstream decision problem. -/
theorem blackwellLE_iff_dominatesEveryFiniteRestrictionValue
    [Nonempty Θ]
    (E : Experiment Θ X) (F : Experiment Θ Y)
    (hE : ∀ θ, IsProbabilityMeasure (E θ))
    (hF : ∀ θ, IsProbabilityMeasure (F θ)) :
    BlackwellLE F E ↔ DominatesEveryFiniteRestrictionValue E F := by
  constructor
  · intro h S hS D _ _ _ _ α hα u rE rF hoptE hoptF
    exact optimal_value_mono_of_blackwellLE α u
      (restrictExperiment S E) (restrictExperiment S F)
      (blackwellLE_restrictExperiment E F S h) rE rF hoptE hoptF
  · exact blackwellValueConverse_arbitraryParameter E F hE hF

/-- Any failure of Blackwell dominance between finite-signal experiments on an arbitrary parameter
class is already witnessed on a finite subset of parameters. -/
theorem exists_finite_restriction_not_blackwellLE_of_not_blackwellLE
    (E : Experiment Θ X) (F : Experiment Θ Y)
    (hE : ∀ θ, IsProbabilityMeasure (E θ))
    (hF : ∀ θ, IsProbabilityMeasure (F θ))
    (h : ¬ BlackwellLE F E) :
    ∃ S : Finset Θ, ¬ BlackwellLE (restrictExperiment S F) (restrictExperiment S E) := by
  by_contra hnone
  push Not at hnone
  exact h (blackwellLE_of_all_finite_restrictions E F hE hF hnone)

end KernelCompactness

end IdExp
