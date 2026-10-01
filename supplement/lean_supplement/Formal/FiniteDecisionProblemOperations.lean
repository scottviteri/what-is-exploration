import Formal.DecisionEnvelope
import Formal.MixturePurposeValue

/-!
# Algebra of finite-support decision problems

The bundled arbitrary-world decision problems use the same exact garbling and
recorded-mixture calculus as finite-world purposes. Restricting to the supplied
finite support transports these operations without choosing a prior on the
ambient world class.
-/

namespace IdExp

open Finset Set

universe u

variable {Θ X Y I : Type u} [Fintype X] [Fintype Y]

/-- Exact garbling is monotone for every bundled finite-support purpose. -/
theorem finiteDecisionProblemValue_mono_of_blackwell
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (h : FiniteBlackwellLE F E) (P : FiniteSupportDecisionProblem Θ) :
    finiteDecisionProblemValue F P ≤ finiteDecisionProblemValue E P := by
  obtain ⟨G, hG, hGF⟩ := h
  apply finiteBayesValue_mono_of_finiteBlackwellLE _ _ _ P.prior P.utility
  exact ⟨G, hG, funext fun θ => congrFun hGF θ.1⟩

/-- Mutually simulable encodings have identical task values. -/
theorem finiteDecisionProblemValue_eq_of_blackwellEquiv
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hFE : FiniteBlackwellLE F E) (hEF : FiniteBlackwellLE E F)
    (P : FiniteSupportDecisionProblem Θ) :
    finiteDecisionProblemValue E P = finiteDecisionProblemValue F P :=
  le_antisymm (finiteDecisionProblemValue_mono_of_blackwell F E hEF P)
    (finiteDecisionProblemValue_mono_of_blackwell E F hFE P)

/-- Retaining an independently sampled experiment label makes every task's
optimized value exactly linear in the mixture weights. The world class is
arbitrary and no common full-support prior is imposed. -/
theorem finiteDecisionProblemValue_mixtureCollector [Fintype I] [Nonempty I]
    (E : I → FiniteExperiment Θ X) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (P : FiniteSupportDecisionProblem Θ) :
    finiteDecisionProblemValue (mixtureCollector E w) P =
      ∑ i, w i * finiteDecisionProblemValue (E i) P := by
  let _ : Nonempty {θ // θ ∈ P.support} := by
    obtain ⟨θ, hθ⟩ := P.support_nonempty
    exact ⟨⟨θ, hθ⟩⟩
  exact purposeValue_mixtureCollector
    (fun i => restrictFiniteExperiment P.support (E i)) w hw (P.prior, P.utility)

/-- A quantitative envelope bound is exactly one uniform bound for every
purpose and every alternative experiment, with both quantifiers inside the
error threshold. -/
theorem finiteDecisionEnvelope_le_iff [Nonempty Θ]
    {J : Type u} [Nonempty J] {Z : J → Type u} [∀ j, Fintype (Z j)]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (F : ∀ j, FiniteExperiment Θ (Z j)) (hF : ∀ j, IsFiniteExperiment (F j))
    (c : ℝ) :
    finiteDecisionEnvelope E F ≤ c ↔
      ∀ (P : FiniteSupportDecisionProblem Θ) j,
        finiteDecisionProblemValue (F j) P - finiteDecisionProblemValue E P ≤ c := by
  have hbdd (P : FiniteSupportDecisionProblem Θ) :
      BddAbove (Set.range fun j => finiteDecisionProblemValue (F j) P) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact (finiteDecisionProblemValue_mem_unitInterval _ (hF j) P).2
  have henvbdd : BddAbove (Set.range fun P : FiniteSupportDecisionProblem Θ =>
      finiteExperimentalBenchmark F P - finiteDecisionProblemValue E P) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨P, rfl⟩
    linarith [(finiteExperimentalBenchmark_mem_unitInterval F hF P).2,
      (finiteDecisionProblemValue_mem_unitInterval E hE P).1]
  constructor
  · intro h P j
    have hj := le_csSup (hbdd P) (Set.mem_range_self j)
    have hP := (le_csSup henvbdd (Set.mem_range_self P)).trans h
    change finiteDecisionProblemValue (F j) P ≤ finiteExperimentalBenchmark F P at hj
    linarith
  · intro h
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨P, rfl⟩
    have hB : finiteExperimentalBenchmark F P ≤ c + finiteDecisionProblemValue E P := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨j, rfl⟩
      linarith [h P j]
    linarith

end IdExp
