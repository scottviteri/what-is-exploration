import Formal.NativeProcess
import Formal.ScoreProcessMonotonicity
import Formal.RecoveryBridge

/-!
# Finitary dominance through terminal experiments, and strictly finitary scores

The written proof of the paper's proposition "finite-world posterior objectives
are strictly finitary" (`prop:finite-world-strict-finitary`) has an
order-theoretic core that needs nothing about worlds, priors, or potentials.
Suppose every process `π` has a *terminal* object `T π` which simulates each of
its own prefixes exactly and is approximated by them arbitrarily well.  Then

* `π` finitarily dominates `σ` **iff** the terminal object of `π` simulates the
  terminal object of `σ` exactly (`finitaryDominates_iff_terminal`);
* consequently any score of terminal objects that is strictly monotone for the
  simulation relation induces a **strictly finitarily monotone** process score
  (`terminalScore_lt_of_strict_finitaryDominates`);
* when a finitarily greatest process exists, the maximizers of that process score
  are exactly the finitarily greatest processes
  (`terminalScore_maximizer_iff_finitarilyGreatest`);
* and if a prefix score increases to the terminal score, the process supremum of
  `ScoreProcessMonotonicity` equals the terminal score
  (`processScoreSup_eq_terminal`).

The only hypotheses are nonnegativity and the triangle inequality of the
directed deficiency, the two terminal properties, and the score's monotonicity.
On a finite world class the terminal object is the full path experiment: the
prefix-to-terminal approximation is the written uniform-deficiency convergence,
exact terminal garbling is the written dominated-kernel argument, and strict
monotonicity of the expected posterior potential at terminal experiments is the
written strict conditional Jensen step.  Those three instantiations are not in
this module; it isolates the assembly that the proposition rests on.
-/

namespace IdExp

section Abstract

variable {P X : Type*}

/-- A terminal assignment for a prefix chain: `T π` simulates every prefix of
`π` exactly, and the prefixes of `π` simulate `T π` to arbitrarily small error
from some time on. -/
structure IsTerminalFor (K : P → ℕ → X) (δ : X → X → ℝ) (T : P → X) : Prop where
  simulates_prefix : ∀ π t, δ (T π) (K π t) = 0
  approximated : ∀ π ε, 0 < ε → ∃ N, ∀ t, N ≤ t → δ (K π t) (T π) < ε

/-- A nonnegative deficiency bounded by every positive number is zero. -/
theorem eq_zero_of_forall_pos_lt {r : ℝ} (hr : 0 ≤ r) (h : ∀ ε, 0 < ε → r < ε) : r = 0 := by
  by_contra hne
  have hpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hne)
  exact lt_irrefl _ (h r hpos)

variable (K : P → ℕ → X) (δ : X → X → ℝ) (T : P → X)

/-- **Finitary dominance is terminal simulation.**  Under the triangle
inequality, `π` finitarily dominates `σ` exactly when `π`'s terminal object
simulates `σ`'s terminal object with zero deficiency. -/
theorem finitaryDominates_iff_terminal
    (hδ : ∀ x y, 0 ≤ δ x y) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (hT : IsTerminalFor K δ T) (π σ : P) :
    FinitaryDominates K δ π σ ↔ δ (T π) (T σ) = 0 := by
  constructor
  · intro hdom
    -- the terminal object of `π` simulates every rival prefix exactly
    have hpref : ∀ n, δ (T π) (K σ n) = 0 := by
      intro n
      apply eq_zero_of_forall_pos_lt (hδ _ _)
      intro ε hε
      obtain ⟨N, hN⟩ := hdom n ε hε
      have h1 := htri (T π) (K π N) (K σ n)
      have h2 := hT.simulates_prefix π N
      have h3 := hN N le_rfl
      linarith
    -- and hence the rival terminal object, by approximation
    apply eq_zero_of_forall_pos_lt (hδ _ _)
    intro ε hε
    obtain ⟨N, hN⟩ := hT.approximated σ ε hε
    have h1 := htri (T π) (K σ N) (T σ)
    have h2 := hpref N
    have h3 := hN N le_rfl
    linarith
  · intro hterm n ε hε
    obtain ⟨N, hN⟩ := hT.approximated π ε hε
    refine ⟨N, fun t ht => ?_⟩
    have h1 := htri (K π t) (T π) (K σ n)
    have h2 := htri (T π) (T σ) (K σ n)
    have h3 := hT.simulates_prefix σ n
    have h4 := hN t ht
    linarith

/-- Transitivity of finitary dominance through terminal objects. -/
theorem finitaryDominates_trans_of_terminal
    (hδ : ∀ x y, 0 ≤ δ x y) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (hT : IsTerminalFor K δ T) {π σ ρ : P}
    (h1 : FinitaryDominates K δ π σ) (h2 : FinitaryDominates K δ σ ρ) :
    FinitaryDominates K δ π ρ := by
  rw [finitaryDominates_iff_terminal K δ T hδ htri hT] at *
  have := htri (T π) (T σ) (T ρ)
  have := hδ (T π) (T ρ)
  linarith

/-- A score on experiments is monotone for exact simulation, and strict when the
simulation is one-sided. -/
structure IsStrictSimulationScore (δ : X → X → ℝ) (S : X → ℝ) : Prop where
  mono : ∀ x y, δ x y = 0 → S y ≤ S x
  strict : ∀ x y, δ x y = 0 → δ y x ≠ 0 → S y < S x

/-- The process score induced by a terminal score. -/
def terminalScore (S : X → ℝ) (π : P) : ℝ := S (T π)

/-- **Monotone in the finitary order.** -/
theorem terminalScore_le_of_finitaryDominates
    (hδ : ∀ x y, 0 ≤ δ x y) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (hT : IsTerminalFor K δ T) {S : X → ℝ} (hS : IsStrictSimulationScore δ S)
    {π σ : P} (hdom : FinitaryDominates K δ π σ) :
    terminalScore T S σ ≤ terminalScore T S π :=
  hS.mono _ _ ((finitaryDominates_iff_terminal K δ T hδ htri hT π σ).1 hdom)

/-- **Strictly finitarily monotone.**  A one-sided finitary dominance gives a
strict score comparison. -/
theorem terminalScore_lt_of_strict_finitaryDominates
    (hδ : ∀ x y, 0 ≤ δ x y) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (hT : IsTerminalFor K δ T) {S : X → ℝ} (hS : IsStrictSimulationScore δ S)
    {π σ : P} (hdom : FinitaryDominates K δ π σ) (hnot : ¬ FinitaryDominates K δ σ π) :
    terminalScore T S σ < terminalScore T S π := by
  rw [finitaryDominates_iff_terminal K δ T hδ htri hT] at hdom hnot
  exact hS.strict _ _ hdom hnot

/-- Mutual finitary dominance gives equal terminal scores. -/
theorem terminalScore_eq_of_mutual_finitaryDominates
    (hδ : ∀ x y, 0 ≤ δ x y) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (hT : IsTerminalFor K δ T) {S : X → ℝ} (hS : IsStrictSimulationScore δ S)
    {π σ : P} (h1 : FinitaryDominates K δ π σ) (h2 : FinitaryDominates K δ σ π) :
    terminalScore T S σ = terminalScore T S π :=
  le_antisymm (terminalScore_le_of_finitaryDominates K δ T hδ htri hT hS h1)
    (terminalScore_le_of_finitaryDominates K δ T hδ htri hT hS h2)

/-- A finitarily greatest process has the largest terminal score. -/
theorem terminalScore_le_of_finitarilyGreatest
    (hδ : ∀ x y, 0 ≤ δ x y) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (hT : IsTerminalFor K δ T) {S : X → ℝ} (hS : IsStrictSimulationScore δ S)
    {π : P} (hgreat : FinitarilyGreatest K δ π) (σ : P) :
    terminalScore T S σ ≤ terminalScore T S π :=
  terminalScore_le_of_finitaryDominates K δ T hδ htri hT hS (hgreat σ)

/-- **Maximizers are exactly the greatest processes.**  When some process is
finitarily greatest, a process attains the maximal terminal score iff it is
itself finitarily greatest. -/
theorem terminalScore_maximizer_iff_finitarilyGreatest
    (hδ : ∀ x y, 0 ≤ δ x y) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (hT : IsTerminalFor K δ T) {S : X → ℝ} (hS : IsStrictSimulationScore δ S)
    {π : P} (hgreat : FinitarilyGreatest K δ π) (σ : P) :
    (∀ ρ, terminalScore T S ρ ≤ terminalScore T S σ) ↔ FinitarilyGreatest K δ σ := by
  constructor
  · intro hmax
    -- `σ` must dominate `π`, otherwise `π` would score strictly higher
    have hσπ : FinitaryDominates K δ σ π := by
      by_contra hnot
      have hlt := terminalScore_lt_of_strict_finitaryDominates K δ T hδ htri hT hS
        (hgreat σ) hnot
      exact absurd (hmax π) (not_le.2 hlt)
    intro ρ
    exact finitaryDominates_trans_of_terminal K δ T hδ htri hT hσπ (hgreat ρ)
  · intro hσ ρ
    exact terminalScore_le_of_finitaryDominates K δ T hδ htri hT hS (hσ ρ)

/-- If a prefix score never exceeds the terminal score and approaches it, the
process supremum of the prefix scores is the terminal score. -/
theorem processScoreSup_eq_terminal (J : X → ℝ) (S : X → ℝ) (π : P)
    (hle : ∀ t, J (K π t) ≤ S (T π))
    (happrox : ∀ ε, 0 < ε → ∃ t, S (T π) - ε < J (K π t)) :
    processScoreSup K J π = terminalScore T S π := by
  unfold processScoreSup terminalScore
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨t, rfl⟩
    exact hle t
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨t, ht⟩ := happrox ε hε
    have hbdd : BddAbove (Set.range fun t => J (K π t)) := ⟨S (T π), by
      rintro _ ⟨t, rfl⟩; exact hle t⟩
    have := le_csSup hbdd ⟨t, rfl⟩
    linarith

end Abstract

/-! ## The actual causal chain on a finite world class

On a nonempty finite class the complete path experiment `K_{π,∞}` is the
terminal object: `RecoveryBridge` proves prefix continuity
(`exists_causalPrefixDeficiency_lt`) and the two triangle chains
(`finiteMeasureDeficiency_terminal_le`, `finiteDeficiency_trace_le_prefix_add_terminal`).
The abstract argument above then gives the pairwise statement that the
existing greatest-process theorem (`causalFinitarilyGreatest_iff_terminallyGreatest`)
is the universal case of. -/

section Causal

open MeasureTheory

variable {A O Θ : Type*} [Fintype A] [Fintype O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]
  [Nonempty A] [Nonempty O] [Fintype Θ] [Nonempty Θ]

/-- **Finitary dominance is terminal simulation (finite class).**  `π`
finitarily dominates `σ` iff the complete path experiment of `π` has directed
deficiency zero to the complete path experiment of `σ`. -/
theorem causalFinitaryDominates_iff_terminal_deficiency_zero
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π σ : ValidCausalPolicy A O) :
    CausalFinitaryDominates Qs π σ ↔
      finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (causalPathExperiment Qs hQ σ) = 0 := by
  constructor
  · intro hdom
    refine le_antisymm ?_ (finiteMeasureDeficiency_nonneg_of_prob _ _
      (isProbabilityMeasure_causalPathExperiment' Qs hQ π)
      (isProbabilityMeasure_causalPathExperiment' Qs hQ σ))
    apply le_of_forall_pos_le_add
    intro ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    obtain ⟨s, hs⟩ := exists_causalPrefixDeficiency_lt Qs hQ σ hhalf
    obtain ⟨T, hT⟩ := hdom s (ε / 2) hhalf
    refine le_of_lt ?_
    calc finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (causalPathExperiment Qs hQ σ)
        ≤ finiteDeficiency (causalFiniteExperiment π.1 Qs T) (causalFiniteExperiment σ.1 Qs s) +
            finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ σ s)
              (causalPathExperiment Qs hQ σ) :=
          finiteMeasureDeficiency_terminal_le Qs hQ π σ T s
      _ < ε / 2 + ε / 2 := add_lt_add (hT T le_rfl) (hs s le_rfl)
      _ = 0 + ε := by ring
  · intro hzero n ε hε
    obtain ⟨T, hT⟩ := exists_causalPrefixDeficiency_lt Qs hQ π hε
    refine ⟨T, fun t ht => ?_⟩
    calc finiteDeficiency (causalFiniteExperiment π.1 Qs t) (causalFiniteExperiment σ.1 Qs n)
        ≤ finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
              (causalPathExperiment Qs hQ π) +
            finiteMeasureDeficiency (causalPathExperiment Qs hQ π)
              (causalPathExperiment Qs hQ σ) :=
          finiteDeficiency_trace_le_prefix_add_terminal Qs hQ π σ t n
      _ = finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
            (causalPathExperiment Qs hQ π) := by rw [hzero, add_zero]
      _ < ε := hT t ht

variable (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))

/-- A terminal score is monotone in causal finitary dominance. -/
theorem causalTerminalScore_le_of_finitaryDominates
    {S : (Θ → FiniteMeasure (CausalTraj A O)) → ℝ}
    (hS : IsStrictSimulationScore finiteMeasureDeficiency S)
    {π σ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π σ) :
    S (causalPathExperiment Qs hQ σ) ≤ S (causalPathExperiment Qs hQ π) :=
  hS.mono _ _ ((causalFinitaryDominates_iff_terminal_deficiency_zero Qs hQ π σ).1 hdom)

/-- **Strictly finitarily monotone terminal scores (finite class).**  If `π`
finitarily dominates `σ` and `σ` does not finitarily dominate `π`, a score of
complete path experiments that strictly respects exact simulation strictly
prefers `π`. -/
theorem causalTerminalScore_lt_of_strict_finitaryDominates
    {S : (Θ → FiniteMeasure (CausalTraj A O)) → ℝ}
    (hS : IsStrictSimulationScore finiteMeasureDeficiency S)
    {π σ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π σ)
    (hnot : ¬ CausalFinitaryDominates Qs σ π) :
    S (causalPathExperiment Qs hQ σ) < S (causalPathExperiment Qs hQ π) := by
  rw [causalFinitaryDominates_iff_terminal_deficiency_zero Qs hQ] at hdom hnot
  exact hS.strict _ _ hdom hnot

/-- **Maximizers are exactly the natively sufficient policies.**  When some
policy is natively sufficient, a policy maximizes a strictly simulation-
monotone terminal score iff it is itself natively sufficient. -/
theorem causalTerminalScore_maximizer_iff_nativelySufficient
    {S : (Θ → FiniteMeasure (CausalTraj A O)) → ℝ}
    (hS : IsStrictSimulationScore finiteMeasureDeficiency S)
    (hexists : ∃ π : ValidCausalPolicy A O, CausalNativelySufficient Qs π)
    (σ : ValidCausalPolicy A O) :
    (∀ ρ : ValidCausalPolicy A O,
        S (causalPathExperiment Qs hQ ρ) ≤ S (causalPathExperiment Qs hQ σ)) ↔
      CausalNativelySufficient Qs σ := by
  obtain ⟨π, hπ⟩ := hexists
  have hπg : CausalFinitarilyGreatest Qs π :=
    (causalNativelySufficient_iff_finitarilyGreatest Qs hQ π).1 hπ
  rw [causalNativelySufficient_iff_finitarilyGreatest Qs hQ σ]
  constructor
  · intro hmax
    have hσπ : CausalFinitaryDominates Qs σ π := by
      by_contra hnot
      have hlt := causalTerminalScore_lt_of_strict_finitaryDominates Qs hQ hS (hπg σ) hnot
      exact absurd (hmax π) (not_le.2 hlt)
    intro ρ
    exact causalFinitaryDominates_trans Qs hQ hσπ (hπg ρ)
  · intro hσg ρ
    exact causalTerminalScore_le_of_finitaryDominates Qs hQ hS (hσg ρ)

end Causal

end IdExp
