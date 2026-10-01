import Formal.DecisionFiniteWitness

/-!
# A decision benchmark over a family of alternative experiments

A task bundles a finite-support prior, a nonempty finite decision alphabet,
and a utility in `[0,1]`.  Its experimental benchmark optimizes the experiment
for that task.  The worst difference between this benchmark and one acquired
experiment is exactly the supremum of directed deficiencies to the family.
No single task or prior is selected by the envelope.
-/

set_option maxHeartbeats 800000

namespace IdExp

open Finset Set

universe u v

/-- A bounded finite decision problem on an arbitrary world class. -/
structure FiniteSupportDecisionProblem (Θ : Type u) where
  support : Finset Θ
  support_nonempty : support.Nonempty
  decisions : Type u
  decisionFinite : Fintype decisions
  decisionNonempty : Nonempty decisions
  prior : {θ // θ ∈ support} → ℝ
  prior_valid : IsDist prior
  utility : {θ // θ ∈ support} → decisions → ℝ
  utility_valid : ∀ θ d, utility θ d ∈ Set.Icc (0 : ℝ) 1

attribute [instance] FiniteSupportDecisionProblem.decisionFinite
attribute [instance] FiniteSupportDecisionProblem.decisionNonempty

noncomputable instance finiteSupportDecisionProblemNonempty
    (Θ : Type u) [Nonempty Θ] : Nonempty (FiniteSupportDecisionProblem Θ) := by
  classical
  let S : Finset Θ := {Classical.arbitrary Θ}
  let _ : Nonempty {θ // θ ∈ S} := ⟨⟨Classical.arbitrary Θ, Finset.mem_singleton_self _⟩⟩
  exact ⟨⟨S, Finset.singleton_nonempty _, PUnit, inferInstance, inferInstance,
    uniformPrior _, isDist_uniformPrior, fun _ _ => 0,
    fun _ _ => ⟨le_rfl, zero_le_one⟩⟩⟩

variable {Θ X : Type u} [Fintype X]

/-- Optimized value of the task, evaluated on its specified finite support. -/
noncomputable def finiteDecisionProblemValue (E : FiniteExperiment Θ X)
    (P : FiniteSupportDecisionProblem Θ) : ℝ :=
  finiteBayesValue (restrictFiniteExperiment P.support E) P.prior P.utility

theorem finiteDecisionProblemValue_mem_unitInterval
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (P : FiniteSupportDecisionProblem Θ) :
    finiteDecisionProblemValue E P ∈ Set.Icc (0 : ℝ) 1 :=
  finiteBayesValue_mem_unitInterval (restrictFiniteExperiment P.support E) (fun θ => hE θ.1)
    P.prior P.prior_valid P.utility P.utility_valid

/-- Every bounded finite task's optimized disadvantage is bounded by the
uniform deficiency, including when the ambient world class is infinite. -/
theorem finiteDecisionProblemValue_sub_le_deficiency [Nonempty Θ]
    {Y : Type u} [Fintype Y] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (P : FiniteSupportDecisionProblem Θ) :
    finiteDecisionProblemValue F P - finiteDecisionProblemValue E P ≤
      finiteDeficiency E F := by
  let _ : Nonempty {θ // θ ∈ P.support} := by
    obtain ⟨θ, hθ⟩ := P.support_nonempty
    exact ⟨⟨θ, hθ⟩⟩
  exact (finiteBayesValue_sub_le_finiteDeficiency
    (restrictFiniteExperiment P.support E) (restrictFiniteExperiment P.support F)
    (fun θ => hE θ.1) (fun θ => hF θ.1)
    P.prior P.prior_valid P.utility P.utility_valid).trans
      (finiteDeficiency_restrict_le E F hE hF P.support P.support_nonempty)

/-- Optimizing over every bounded finite task gives exactly deficiency. -/
theorem finiteDeficiency_eq_sSup_decisionProblemGaps [Nonempty Θ]
    {Y : Type u} [Fintype Y] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    finiteDeficiency E F = sSup (Set.range fun P : FiniteSupportDecisionProblem Θ =>
      finiteDecisionProblemValue F P - finiteDecisionProblemValue E P) := by
  let gaps := Set.range fun P : FiniteSupportDecisionProblem Θ =>
    finiteDecisionProblemValue F P - finiteDecisionProblemValue E P
  have hbdd : BddAbove gaps := by
    refine ⟨finiteDeficiency E F, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact finiteDecisionProblemValue_sub_le_deficiency E F hE hF P
  apply le_antisymm
  · by_contra h
    obtain ⟨S, hS, α, u, hα, hu, hgap⟩ :=
      exists_finiteSupport_bayesGap_gt_of_lt_finiteDeficiency E F hE hF (lt_of_not_ge h)
    let P : FiniteSupportDecisionProblem Θ :=
      ⟨S, hS, Y, inferInstance, inferInstance, α, hα, u, hu⟩
    have hle := le_csSup hbdd (Set.mem_range_self P)
    exact (not_lt_of_ge hle) hgap
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨P, rfl⟩
    exact finiteDecisionProblemValue_sub_le_deficiency E F hE hF P

variable {J : Type v} {Y : J → Type u} [∀ j, Fintype (Y j)]

/-- The best value achievable by selecting an alternative experiment after
knowing the task, before knowing the true world. -/
noncomputable def finiteExperimentalBenchmark
    (F : ∀ j, FiniteExperiment Θ (Y j)) (P : FiniteSupportDecisionProblem Θ) : ℝ :=
  sSup (Set.range fun j => finiteDecisionProblemValue (F j) P)

/-- Worst task disadvantage relative to the purpose-specific alternative
experimental benchmark. -/
noncomputable def finiteDecisionEnvelope
    (E : FiniteExperiment Θ X) (F : ∀ j, FiniteExperiment Θ (Y j)) : ℝ :=
  sSup (Set.range fun P : FiniteSupportDecisionProblem Θ =>
    finiteExperimentalBenchmark F P - finiteDecisionProblemValue E P)

theorem finiteExperimentalBenchmark_mem_unitInterval [Nonempty J]
    (F : ∀ j, FiniteExperiment Θ (Y j)) (hF : ∀ j, IsFiniteExperiment (F j))
    (P : FiniteSupportDecisionProblem Θ) :
    finiteExperimentalBenchmark F P ∈ Set.Icc (0 : ℝ) 1 := by
  have hbdd : BddAbove (Set.range fun j => finiteDecisionProblemValue (F j) P) :=
    ⟨1, fun _ ⟨j, hj⟩ => hj ▸ (finiteDecisionProblemValue_mem_unitInterval (F j) (hF j) P).2⟩
  constructor
  · exact (finiteDecisionProblemValue_mem_unitInterval
      (F (Classical.arbitrary J)) (hF _) P).1.trans
        (le_csSup hbdd (Set.mem_range_self (Classical.arbitrary J)))
  · exact csSup_le (Set.range_nonempty _) fun _ ⟨j, hj⟩ =>
      hj ▸ (finiteDecisionProblemValue_mem_unitInterval (F j) (hF j) P).2

/-- The actual double optimization over tasks and alternative experiments
is exactly the worst-target deficiency.  Decision alphabets and experiment
signal alphabets may differ, and the world class is arbitrary. -/
theorem finiteDecisionEnvelope_eq_sSup_deficiency
    [Nonempty Θ] [Nonempty J] [∀ j, Nonempty (Y j)]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (F : ∀ j, FiniteExperiment Θ (Y j)) (hF : ∀ j, IsFiniteExperiment (F j)) :
    finiteDecisionEnvelope E F = sSup (Set.range fun j => finiteDeficiency E (F j)) := by
  classical
  let δ := sSup (Set.range fun j => finiteDeficiency E (F j))
  have hδbdd : BddAbove (Set.range fun j => finiteDeficiency E (F j)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨j, rfl⟩
    let G := selectionRule (fun _ : X => Classical.arbitrary (Y j))
    have hG : G ∈ stochasticRules X (Y j) := selectionRule_mem_stochasticRules _
    exact finiteDeficiency_le_of_decoder E (F j) G hG 1
      (fun θ => decodeErr_le_one E (F j) hE (hF j) G hG θ)
  have henvbdd : BddAbove (Set.range fun P : FiniteSupportDecisionProblem Θ =>
      finiteExperimentalBenchmark F P - finiteDecisionProblemValue E P) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨P, rfl⟩
    have hB := finiteExperimentalBenchmark_mem_unitInterval F hF P
    have hE' := finiteDecisionProblemValue_mem_unitInterval E hE P
    change finiteExperimentalBenchmark F P - finiteDecisionProblemValue E P ≤ 1
    linarith [hB.2, hE'.1]
  have hBbdd (P : FiniteSupportDecisionProblem Θ) :
      BddAbove (Set.range fun j => finiteDecisionProblemValue (F j) P) :=
    ⟨1, fun _ ⟨j, hj⟩ => hj ▸ (finiteDecisionProblemValue_mem_unitInterval (F j) (hF j) P).2⟩
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨P, rfl⟩
    have hB : finiteExperimentalBenchmark F P ≤ δ + finiteDecisionProblemValue E P := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨j, rfl⟩
      have hgap := finiteDecisionProblemValue_sub_le_deficiency E (F j) hE (hF j) P
      have hδ := le_csSup hδbdd (Set.mem_range_self j)
      change finiteDeficiency E (F j) ≤ δ at hδ
      linarith
    linarith
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨j, rfl⟩
    change finiteDeficiency E (F j) ≤ finiteDecisionEnvelope E F
    rw [finiteDeficiency_eq_sSup_decisionProblemGaps E (F j) hE (hF j)]
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨P, rfl⟩
    have hB := le_csSup (hBbdd P) (Set.mem_range_self j)
    change finiteDecisionProblemValue (F j) P ≤ finiteExperimentalBenchmark F P at hB
    exact (sub_le_sub_right hB _).trans (le_csSup henvbdd (Set.mem_range_self P))

end IdExp
