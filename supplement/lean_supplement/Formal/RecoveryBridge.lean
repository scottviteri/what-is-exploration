import Formal.MeasureDeficiency
import Formal.CausalPrefixContinuity

/-!
# The finite recovery bridge: native sufficiency is terminal deficiency zero

**Relevance:** direct current-paper support for the first sentence of
`thm:finite-recovery` (deficiency-zero form) and for the native-to-terminal
comparison of `rem:uniform-depth` in `Paper/draft/main.tex`; it also packages
the finite-class specialization of `prop:l1-prefix` in the paper's explicit
trace encoding.

`CausalProcess.lean` proves, for an arbitrary nonempty world class, that
concrete native sufficiency (`CausalNativelySufficient`) is the same as being
a greatest process in the finitary order (`CausalFinitarilyGreatest`):
`finiteDeficiency (K_{π,t}) (K_{ρ,n}) → 0` for every valid policy `ρ` and
every depth `n`.  This module closes the gap between that finitary statement
and the terminal one on the complete path space `CausalTraj A O`:

* `causalPrefixKernel t` is the deterministic prefix garbling, so the trace
  experiment `K_{π,t}` is an exact garbling of the complete path experiment
  `K_{π,∞}` (`finiteMarkovDecode_causalPrefixKernel`), giving
  `δ(K_{π,∞}, K_{π,t}) = 0` (`finiteMeasureDeficiency_path_trace_eq_zero`),
  source monotonicity `δ(K_{π,∞}, F) ≤ δ(K_{π,t}, F)`
  (`finiteMeasureDeficiency_path_le_trace`) and target monotonicity
  `δ(E, K_{σ,n}) ≤ δ(E, K_{σ,∞})` (`finiteMeasureDeficiency_to_trace_le_to_path`);
* the trace measure experiment is literally the row experiment of the paper's
  finite trace matrix (`causalTraceMeasureExperiment_eq_rowExperiment`), so
  the matrix deficiency between two finite trace experiments is the measure
  deficiency between their trace laws
  (`finiteMeasureDeficiency_trace_trace_eq_finiteDeficiency`);
* the two triangle chains of the paper's proof,
  `finiteDeficiency (K_{π,t}) (K_{σ,n}) ≤ δ(K_{π,t}, K_{π,∞}) + δ(K_{π,∞}, K_{σ,∞})`
  (`finiteDeficiency_trace_le_prefix_add_terminal`) and
  `δ(K_{π,∞}, K_{σ,∞}) ≤ finiteDeficiency (K_{π,T}) (K_{σ,s}) + δ(K_{σ,s}, K_{σ,∞})`
  (`finiteMeasureDeficiency_terminal_le`), hold over an arbitrary nonempty
  world class;
* for a nonempty **finite** class, prefix continuity
  (`tendsto_causalPrefixDeficiency`, epsilon form
  `exists_causalPrefixDeficiency_lt`) sends the prefix terms to zero, and the
  main theorems `causalFinitarilyGreatest_iff_terminallyGreatest`,
  `causalNativelySufficient_iff_terminallyGreatest` and
  `causalNativelySufficient_iff_terminalDeficiencyZero` state: a valid policy
  is natively sufficient iff its complete path experiment has directed
  deficiency zero to the complete path experiment of every valid policy, i.e.
  iff `K_{π,∞}` is a greatest attainable experiment in the deficiency-zero
  (Le Cam) order (`CausalTerminallyGreatest`);
* corollaries for `rem:uniform-depth`: under native sufficiency
  `δ(K_{π,∞}, K_{σ,n}) = 0` for every finite trace experiment and
  `Γ_{≤n}(K_{π,t}) ≤ δ(K_{π,t}, K_{π,∞})`
  (`causalNativeDeficiency_le_prefixDeficiency_of_nativelySufficient`), and,
  without any sufficiency hypothesis, the quantitative
  `Γ_{≤n}(K_{π,t}) ≤ δ(K_{π,t}, K_{π,∞}) + causalTerminalDeficiency Qs hQ π`
  where `causalTerminalDeficiency` is the supremum over valid policies of
  `δ(K_{π,∞}, K_{σ,∞})`.

All deficiencies on the path and trace spaces are `finiteMeasureDeficiency`
from `DominatedPrefix.lean` (infimum over bundled Markov decoders of the
uniform total-variation error).  Zero deficiency is the Le Cam comparison;
attainment by an exact garbling on the infinite path space is not claimed
here.
-/

set_option linter.unusedSectionVars false

namespace IdExp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {A O Θ : Type*} [Fintype A] [Fintype O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]
  [Nonempty A] [Nonempty O]

/-! ## The prefix garbling kernel -/

/-- The deterministic prefix kernel from the complete path space to the
length-`t` trace space, bundled as a Markov decoder. -/
noncomputable def causalPrefixKernel (t : ℕ) :
    FiniteMarkovKernel (CausalTraj A O) (CausalFiniteTrace A O t) :=
  ⟨Kernel.deterministic (causalPrefixMap t) (measurable_causalPrefixMap t),
    Kernel.isMarkovKernel_deterministic _⟩

/-- The trace experiment `K_{π,t}` is the exact prefix garbling of the complete
path experiment `K_{π,∞}`. -/
theorem finiteMarkovDecode_causalPrefixKernel (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) (t : ℕ) (θ : Θ) :
    finiteMarkovDecode (causalPrefixKernel t) (causalPathExperiment Qs hQ π θ) =
      causalTraceMeasureExperiment Qs hQ π t θ :=
  (causalTraceMeasureExperiment_eq_decode_path Qs hQ π t θ).symm

theorem isProbabilityMeasure_causalPathExperiment' (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) :
    ∀ θ, IsProbabilityMeasure (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)) :=
  fun _ => inferInstance

theorem isProbabilityMeasure_causalTraceMeasureExperiment' (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) (t : ℕ) :
    ∀ θ, IsProbabilityMeasure
      (causalTraceMeasureExperiment Qs hQ π t θ : Measure (CausalFiniteTrace A O t)) :=
  fun _ => inferInstance

/-! ## Zero deficiency to prefixes, and the two monotonicities -/

/-- `δ(K_{π,∞}, K_{π,t}) = 0`: a prefix of the complete path experiment is an
exact garbling of it. -/
theorem finiteMeasureDeficiency_path_trace_eq_zero [Nonempty Θ]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (t : ℕ) :
    finiteMeasureDeficiency (causalPathExperiment Qs hQ π)
      (causalTraceMeasureExperiment Qs hQ π t) = 0 :=
  finiteMeasureDeficiency_garbling_eq_zero _ _ (causalPrefixKernel t)
    (finiteMarkovDecode_causalPrefixKernel Qs hQ π t)

/-- Source monotonicity: the complete path experiment is at least as good a
source as any of its finite prefixes, `δ(K_{π,∞}, F) ≤ δ(K_{π,t}, F)`. -/
theorem finiteMeasureDeficiency_path_le_trace [Nonempty Θ]
    {Y : Type*} [MeasurableSpace Y] [Nonempty Y]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (t : ℕ) (F : Θ → FiniteMeasure Y)
    (hF : ∀ θ, IsProbabilityMeasure (F θ : Measure Y)) :
    finiteMeasureDeficiency (causalPathExperiment Qs hQ π) F ≤
      finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t) F :=
  finiteMeasureDeficiency_le_of_source_garbling_of_prob _ _ (causalPrefixKernel t)
    (finiteMarkovDecode_causalPrefixKernel Qs hQ π t) F
    (isProbabilityMeasure_causalTraceMeasureExperiment' Qs hQ π t) hF

/-- Target monotonicity: a finite prefix of a complete path experiment is an
easier target than the complete experiment, `δ(E, K_{σ,n}) ≤ δ(E, K_{σ,∞})`. -/
theorem finiteMeasureDeficiency_to_trace_le_to_path [Nonempty Θ]
    {X : Type*} [MeasurableSpace X]
    (E : Θ → FiniteMeasure X) (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X))
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (σ : ValidCausalPolicy A O) (n : ℕ) :
    finiteMeasureDeficiency E (causalTraceMeasureExperiment Qs hQ σ n) ≤
      finiteMeasureDeficiency E (causalPathExperiment Qs hQ σ) :=
  finiteMeasureDeficiency_mono_target_of_prob E _ _ (causalPrefixKernel n)
    (finiteMarkovDecode_causalPrefixKernel Qs hQ σ n) hE
    (isProbabilityMeasure_causalPathExperiment' Qs hQ σ)

/-! ## The trace measure experiment is the paper's finite trace matrix -/

/-- The pushforward trace law is exactly the row measure of the paper's
finite trace experiment `causalFiniteExperiment`. -/
theorem causalTraceMeasureExperiment_eq_rowExperiment (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) (t : ℕ) :
    causalTraceMeasureExperiment Qs hQ π t = rowExperiment (causalFiniteExperiment π.1 Qs t) := by
  funext θ
  exact finiteMeasureOfRow_eq_of_forall_singleton _ _
    (causalTraceMeasureExperiment_singleton Qs hQ π t θ)

/-- The measure deficiency between two finite trace experiments is the matrix
deficiency between the paper's finite trace matrices. -/
theorem finiteMeasureDeficiency_trace_trace_eq_finiteDeficiency (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π σ : ValidCausalPolicy A O) (t s : ℕ) :
    finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
        (causalTraceMeasureExperiment Qs hQ σ s) =
      finiteDeficiency (causalFiniteExperiment π.1 Qs t) (causalFiniteExperiment σ.1 Qs s) := by
  rw [causalTraceMeasureExperiment_eq_rowExperiment Qs hQ π t,
    causalTraceMeasureExperiment_eq_rowExperiment Qs hQ σ s]
  exact finiteMeasureDeficiency_eq_finiteDeficiency _ _
    (causalFiniteExperiment_valid π.1 π.2 Qs hQ t) (causalFiniteExperiment_valid σ.1 σ.2 Qs hQ s)

/-! ## The two triangle chains (arbitrary nonempty world class) -/

/-- **Finitary deficiency is bounded by prefix plus terminal deficiency.**
`finiteDeficiency (K_{π,t}) (K_{σ,n}) ≤ δ(K_{π,t}, K_{π,∞}) + δ(K_{π,∞}, K_{σ,∞})`:
triangle through `K_{π,∞}`, then garble the target `K_{σ,∞}` down to its
depth-`n` prefix. -/
theorem finiteDeficiency_trace_le_prefix_add_terminal [Nonempty Θ]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π σ : ValidCausalPolicy A O) (t n : ℕ) :
    finiteDeficiency (causalFiniteExperiment π.1 Qs t) (causalFiniteExperiment σ.1 Qs n) ≤
      finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
          (causalPathExperiment Qs hQ π) +
        finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (causalPathExperiment Qs hQ σ) := by
  rw [← finiteMeasureDeficiency_trace_trace_eq_finiteDeficiency Qs hQ π σ t n]
  calc finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
        (causalTraceMeasureExperiment Qs hQ σ n)
      ≤ finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
            (causalPathExperiment Qs hQ π) +
          finiteMeasureDeficiency (causalPathExperiment Qs hQ π)
            (causalTraceMeasureExperiment Qs hQ σ n) :=
        finiteMeasureDeficiency_triangle_of_prob _ _ _
          (isProbabilityMeasure_causalTraceMeasureExperiment' Qs hQ π t)
          (isProbabilityMeasure_causalPathExperiment' Qs hQ π)
          (isProbabilityMeasure_causalTraceMeasureExperiment' Qs hQ σ n)
    _ ≤ _ :=
        add_le_add le_rfl
          (finiteMeasureDeficiency_to_trace_le_to_path _
            (isProbabilityMeasure_causalPathExperiment' Qs hQ π) Qs hQ σ n)

/-- **Terminal deficiency is bounded by finitary deficiency plus the target's
prefix deficiency.**
`δ(K_{π,∞}, K_{σ,∞}) ≤ finiteDeficiency (K_{π,T}) (K_{σ,s}) + δ(K_{σ,s}, K_{σ,∞})`:
the source `K_{π,∞}` is at least as good as its prefix `K_{π,T}`, then
triangle through `K_{σ,s}`. -/
theorem finiteMeasureDeficiency_terminal_le [Nonempty Θ]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π σ : ValidCausalPolicy A O) (T s : ℕ) :
    finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (causalPathExperiment Qs hQ σ) ≤
      finiteDeficiency (causalFiniteExperiment π.1 Qs T) (causalFiniteExperiment σ.1 Qs s) +
        finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ σ s)
          (causalPathExperiment Qs hQ σ) := by
  rw [← finiteMeasureDeficiency_trace_trace_eq_finiteDeficiency Qs hQ π σ T s]
  calc finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (causalPathExperiment Qs hQ σ)
      ≤ finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π T)
          (causalPathExperiment Qs hQ σ) :=
        finiteMeasureDeficiency_path_le_trace Qs hQ π T _
          (isProbabilityMeasure_causalPathExperiment' Qs hQ σ)
    _ ≤ _ :=
        finiteMeasureDeficiency_triangle_of_prob _ _ _
          (isProbabilityMeasure_causalTraceMeasureExperiment' Qs hQ π T)
          (isProbabilityMeasure_causalTraceMeasureExperiment' Qs hQ σ s)
          (isProbabilityMeasure_causalPathExperiment' Qs hQ σ)

/-- Terminal deficiency is bounded by the native deficiency of a prefix at the
target's horizon plus the target's prefix deficiency:
`δ(K_{π,∞}, K_{σ,∞}) ≤ Γ_{≤s}(K_{π,T}) + δ(K_{σ,s}, K_{σ,∞})`. -/
theorem finiteMeasureDeficiency_terminal_le_native_add_prefix [Nonempty Θ]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π σ : ValidCausalPolicy A O) (T s : ℕ) :
    finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (causalPathExperiment Qs hQ σ) ≤
      causalNativeDeficiency (causalFiniteExperiment π.1 Qs T) Qs s +
        finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ σ s)
          (causalPathExperiment Qs hQ σ) :=
  (finiteMeasureDeficiency_terminal_le Qs hQ π σ T s).trans
    (add_le_add
      (finiteDeficiency_causalPolicy_le_native_at_horizon _
        (causalFiniteExperiment_valid π.1 π.2 Qs hQ T) σ.1 σ.2 Qs hQ s)
      le_rfl)

/-! ## Terminal greatest experiments -/

/-- `K_{π,∞}` is a greatest attainable complete path experiment in the
deficiency-zero (Le Cam) order: it has directed deficiency zero to the
complete path experiment of every valid causal policy. -/
def CausalTerminallyGreatest (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) : Prop :=
  ∀ σ : ValidCausalPolicy A O,
    finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (causalPathExperiment Qs hQ σ) = 0

/-- The terminal deficiency of a policy: the supremum over valid policies `σ`
of `δ(K_{π,∞}, K_{σ,∞})`. -/
noncomputable def causalTerminalDeficiency (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) : ℝ :=
  sSup (Set.range fun σ : ValidCausalPolicy A O =>
    finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (causalPathExperiment Qs hQ σ))

theorem causalTerminalDeficiency_bddAbove [Nonempty Θ] (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) :
    BddAbove (Set.range fun σ : ValidCausalPolicy A O =>
      finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (causalPathExperiment Qs hQ σ)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨σ, rfl⟩
  exact finiteMeasureDeficiency_le_one_of_prob _ _
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π)
    (isProbabilityMeasure_causalPathExperiment' Qs hQ σ)

theorem finiteMeasureDeficiency_path_le_causalTerminalDeficiency [Nonempty Θ]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π σ : ValidCausalPolicy A O) :
    finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (causalPathExperiment Qs hQ σ) ≤
      causalTerminalDeficiency Qs hQ π :=
  le_csSup (causalTerminalDeficiency_bddAbove Qs hQ π) ⟨σ, rfl⟩

theorem causalTerminalDeficiency_nonneg [Nonempty Θ] (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) :
    0 ≤ causalTerminalDeficiency Qs hQ π :=
  (finiteMeasureDeficiency_nonneg_of_prob _ _
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π)
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π)).trans
    (finiteMeasureDeficiency_path_le_causalTerminalDeficiency Qs hQ π π)

theorem causalTerminalDeficiency_le_one [Nonempty Θ] (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) :
    causalTerminalDeficiency Qs hQ π ≤ 1 := by
  refine csSup_le ⟨_, π, rfl⟩ ?_
  rintro _ ⟨σ, rfl⟩
  exact finiteMeasureDeficiency_le_one_of_prob _ _
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π)
    (isProbabilityMeasure_causalPathExperiment' Qs hQ σ)

/-- Terminal greatestness is the vanishing of the terminal deficiency. -/
theorem causalTerminallyGreatest_iff_causalTerminalDeficiency_eq_zero [Nonempty Θ]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    CausalTerminallyGreatest Qs hQ π ↔ causalTerminalDeficiency Qs hQ π = 0 := by
  constructor
  · intro h
    apply le_antisymm _ (causalTerminalDeficiency_nonneg Qs hQ π)
    refine csSup_le ⟨_, π, rfl⟩ ?_
    rintro _ ⟨σ, rfl⟩
    exact (h σ).le
  · intro h σ
    exact le_antisymm
      ((finiteMeasureDeficiency_path_le_causalTerminalDeficiency Qs hQ π σ).trans h.le)
      (finiteMeasureDeficiency_nonneg_of_prob _ _
        (isProbabilityMeasure_causalPathExperiment' Qs hQ π)
        (isProbabilityMeasure_causalPathExperiment' Qs hQ σ))

/-- Quantitative form of the first inequality of `rem:uniform-depth`, with no
sufficiency hypothesis and an arbitrary nonempty world class:
`Γ_{≤n}(K_{π,t}) ≤ δ(K_{π,t}, K_{π,∞}) + causalTerminalDeficiency Qs hQ π`. -/
theorem causalNativeDeficiency_le_prefixDeficiency_add_terminalDeficiency [Nonempty Θ]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (t n : ℕ) :
    causalNativeDeficiency (causalFiniteExperiment π.1 Qs t) Qs n ≤
      finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
          (causalPathExperiment Qs hQ π) +
        causalTerminalDeficiency Qs hQ π := by
  obtain ⟨τ, hτ⟩ := exists_causalPlan_eq_nativeDeficiency (causalFiniteExperiment π.1 Qs t) Qs n
  rw [hτ, finiteDeficiency_causalPlanObservation_eq_full _
    (causalFiniteExperiment_valid π.1 π.2 Qs hQ t) Qs hQ n τ]
  let σ : ValidCausalPolicy A O := ⟨causalPolicyOfPlan n τ, isCausalPolicy_causalPolicyOfPlan n τ⟩
  calc finiteDeficiency (causalFiniteExperiment π.1 Qs t)
        (causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n)
      = finiteDeficiency (causalFiniteExperiment π.1 Qs t) (causalFiniteExperiment σ.1 Qs n) := rfl
    _ ≤ finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
            (causalPathExperiment Qs hQ π) +
          finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (causalPathExperiment Qs hQ σ) :=
        finiteDeficiency_trace_le_prefix_add_terminal Qs hQ π σ t n
    _ ≤ _ :=
        add_le_add le_rfl (finiteMeasureDeficiency_path_le_causalTerminalDeficiency Qs hQ π σ)

/-! ## Finite classes: prefix continuity in epsilon form -/

section FiniteClass

variable [Fintype Θ] [Nonempty Θ]

/-- Epsilon form of finite-class prefix continuity in the paper's trace
encoding: for every `ε > 0` there is a depth beyond which
`δ(K_{π,t}, K_{π,∞}) < ε`. -/
theorem exists_causalPrefixDeficiency_lt (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T, ∀ t, T ≤ t →
      finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
        (causalPathExperiment Qs hQ π) < ε :=
  eventually_atTop.1 ((tendsto_order.1 (tendsto_causalPrefixDeficiency Qs hQ π)).2 ε hε)

/-! ## The main theorem -/

/-- **Finitary greatest iff terminally greatest (finite class).**  For a
nonempty finite class of valid causal response kernels, a valid policy is a
greatest process in the finitary order iff its complete path experiment has
directed deficiency zero to the complete path experiment of every valid
policy.

Forward: `δ(K_{π,∞}, K_{σ,∞}) ≤ finiteDeficiency (K_{π,T}) (K_{σ,s}) + δ(K_{σ,s}, K_{σ,∞})`
with both terms below `ε/2` for `s` given by prefix continuity of `σ` and `T`
given by finitary dominance at horizon `s`.
Backward: `finiteDeficiency (K_{π,t}) (K_{ρ,n}) ≤ δ(K_{π,t}, K_{π,∞}) + 0 → 0`
by prefix continuity of `π`. -/
theorem causalFinitarilyGreatest_iff_terminallyGreatest (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) :
    CausalFinitarilyGreatest Qs π ↔ CausalTerminallyGreatest Qs hQ π := by
  constructor
  · intro hgreat σ
    refine le_antisymm ?_ (finiteMeasureDeficiency_nonneg_of_prob _ _
      (isProbabilityMeasure_causalPathExperiment' Qs hQ π)
      (isProbabilityMeasure_causalPathExperiment' Qs hQ σ))
    apply le_of_forall_pos_le_add
    intro ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    obtain ⟨s, hs⟩ := exists_causalPrefixDeficiency_lt Qs hQ σ hhalf
    obtain ⟨T, hT⟩ := hgreat σ s (ε / 2) hhalf
    refine le_of_lt ?_
    calc finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (causalPathExperiment Qs hQ σ)
        ≤ finiteDeficiency (causalFiniteExperiment π.1 Qs T) (causalFiniteExperiment σ.1 Qs s) +
            finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ σ s)
              (causalPathExperiment Qs hQ σ) :=
          finiteMeasureDeficiency_terminal_le Qs hQ π σ T s
      _ < ε / 2 + ε / 2 := add_lt_add (hT T le_rfl) (hs s le_rfl)
      _ = 0 + ε := by ring
  · intro hzero ρ n ε hε
    obtain ⟨T, hT⟩ := exists_causalPrefixDeficiency_lt Qs hQ π hε
    refine ⟨T, fun t ht => ?_⟩
    calc finiteDeficiency (causalFiniteExperiment π.1 Qs t) (causalFiniteExperiment ρ.1 Qs n)
        ≤ finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
              (causalPathExperiment Qs hQ π) +
            finiteMeasureDeficiency (causalPathExperiment Qs hQ π)
              (causalPathExperiment Qs hQ ρ) :=
          finiteDeficiency_trace_le_prefix_add_terminal Qs hQ π ρ t n
      _ = finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
            (causalPathExperiment Qs hQ π) := by rw [hzero ρ, add_zero]
      _ < ε := hT t ht

/-- **Native sufficiency is terminal greatestness (finite class).**  For a
nonempty finite class of valid causal response kernels, a valid policy is
natively sufficient iff `K_{π,∞}` is a greatest attainable complete path
experiment in the deficiency-zero (Le Cam) order. -/
theorem causalNativelySufficient_iff_terminallyGreatest (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) :
    CausalNativelySufficient Qs π ↔ CausalTerminallyGreatest Qs hQ π := by
  rw [causalNativelySufficient_iff_finitarilyGreatest Qs hQ π]
  exact causalFinitarilyGreatest_iff_terminallyGreatest Qs hQ π

/-- **`thm:finite-recovery`, first sentence, deficiency-zero form.**  For a
nonempty finite class of valid causal response kernels and a valid policy `π`,
`π` is natively sufficient iff the complete path experiment `K_{π,∞}` has
directed deficiency zero to the complete path experiment `K_{σ,∞}` of every
valid policy `σ`. -/
theorem causalNativelySufficient_iff_terminalDeficiencyZero (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) :
    CausalNativelySufficient Qs π ↔
      ∀ σ : ValidCausalPolicy A O,
        finiteMeasureDeficiency (causalPathExperiment Qs hQ π)
          (causalPathExperiment Qs hQ σ) = 0 :=
  causalNativelySufficient_iff_terminallyGreatest Qs hQ π

/-- Native sufficiency is the vanishing of the terminal deficiency. -/
theorem causalNativelySufficient_iff_causalTerminalDeficiency_eq_zero
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    CausalNativelySufficient Qs π ↔ causalTerminalDeficiency Qs hQ π = 0 := by
  rw [causalNativelySufficient_iff_terminallyGreatest Qs hQ π]
  exact causalTerminallyGreatest_iff_causalTerminalDeficiency_eq_zero Qs hQ π

/-- Two natively sufficient policies have complete path experiments with
zero deficiency in both directions (Le Cam equivalent). -/
theorem causalNativelySufficient_mutual_terminalDeficiencyZero
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {π σ : ValidCausalPolicy A O}
    (hπ : CausalNativelySufficient Qs π) (hσ : CausalNativelySufficient Qs σ) :
    finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (causalPathExperiment Qs hQ σ) = 0 ∧
      finiteMeasureDeficiency (causalPathExperiment Qs hQ σ) (causalPathExperiment Qs hQ π) = 0 :=
  ⟨(causalNativelySufficient_iff_terminalDeficiencyZero Qs hQ π).1 hπ σ,
    (causalNativelySufficient_iff_terminalDeficiencyZero Qs hQ σ).1 hσ π⟩

/-! ## Corollaries for `rem:uniform-depth` -/

/-- Under native sufficiency the complete path experiment has deficiency zero
to every finite trace experiment of every valid policy:
`δ(K_{π,∞}, K_{σ,n}) = 0`. -/
theorem finiteMeasureDeficiency_path_to_finiteTrace_eq_zero_of_nativelySufficient
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {π : ValidCausalPolicy A O} (h : CausalNativelySufficient Qs π)
    (σ : ValidCausalPolicy A O) (n : ℕ) :
    finiteMeasureDeficiency (causalPathExperiment Qs hQ π)
      (causalTraceMeasureExperiment Qs hQ σ n) = 0 := by
  have hzero := (causalNativelySufficient_iff_terminalDeficiencyZero Qs hQ π).1 h σ
  apply le_antisymm
  · calc finiteMeasureDeficiency (causalPathExperiment Qs hQ π)
          (causalTraceMeasureExperiment Qs hQ σ n)
        ≤ finiteMeasureDeficiency (causalPathExperiment Qs hQ π)
            (causalPathExperiment Qs hQ σ) :=
          finiteMeasureDeficiency_to_trace_le_to_path _
            (isProbabilityMeasure_causalPathExperiment' Qs hQ π) Qs hQ σ n
      _ = 0 := hzero
  · exact finiteMeasureDeficiency_nonneg_of_prob _ _
      (isProbabilityMeasure_causalPathExperiment' Qs hQ π)
      (isProbabilityMeasure_causalTraceMeasureExperiment' Qs hQ σ n)

/-- Under native sufficiency the matrix deficiency from a finite prefix of
`π` to any finite trace experiment is at most the prefix deficiency
`δ(K_{π,t}, K_{π,∞})`. -/
theorem finiteDeficiency_trace_le_prefixDeficiency_of_nativelySufficient
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {π : ValidCausalPolicy A O} (h : CausalNativelySufficient Qs π)
    (σ : ValidCausalPolicy A O) (t n : ℕ) :
    finiteDeficiency (causalFiniteExperiment π.1 Qs t) (causalFiniteExperiment σ.1 Qs n) ≤
      finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
        (causalPathExperiment Qs hQ π) := by
  have hzero := (causalNativelySufficient_iff_terminalDeficiencyZero Qs hQ π).1 h σ
  calc finiteDeficiency (causalFiniteExperiment π.1 Qs t) (causalFiniteExperiment σ.1 Qs n)
      ≤ finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
            (causalPathExperiment Qs hQ π) +
          finiteMeasureDeficiency (causalPathExperiment Qs hQ π)
            (causalPathExperiment Qs hQ σ) :=
        finiteDeficiency_trace_le_prefix_add_terminal Qs hQ π σ t n
    _ = _ := by rw [hzero, add_zero]

/-- **First inequality of `rem:uniform-depth`.**  Under native sufficiency the
native deficiency of the depth-`t` prefix at every test depth `n` is bounded
by the prefix deficiency: `Γ_{≤n}(K_{π,t}) ≤ δ(K_{π,t}, K_{π,∞})`. -/
theorem causalNativeDeficiency_le_prefixDeficiency_of_nativelySufficient
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {π : ValidCausalPolicy A O} (h : CausalNativelySufficient Qs π) (t n : ℕ) :
    causalNativeDeficiency (causalFiniteExperiment π.1 Qs t) Qs n ≤
      finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
        (causalPathExperiment Qs hQ π) := by
  have hzero := (causalNativelySufficient_iff_causalTerminalDeficiency_eq_zero Qs hQ π).1 h
  have hbound := causalNativeDeficiency_le_prefixDeficiency_add_terminalDeficiency Qs hQ π t n
  rw [hzero, add_zero] at hbound
  exact hbound

/-- Under native sufficiency the native deficiency of the prefixes tends to
zero uniformly in the test depth: the paper's uniform-depth conclusion in
the finite-class setting, as a consequence of prefix continuity. -/
theorem tendsto_causalNativeDeficiency_of_nativelySufficient
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {π : ValidCausalPolicy A O} (h : CausalNativelySufficient Qs π) (n : ℕ) :
    Tendsto (fun t => causalNativeDeficiency (causalFiniteExperiment π.1 Qs t) Qs n)
      atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_causalPrefixDeficiency Qs hQ π) (fun t => ?_) (fun t => ?_)
  · obtain ⟨τ, hτ⟩ :=
      exists_causalPlan_eq_nativeDeficiency (causalFiniteExperiment π.1 Qs t) Qs n
    rw [hτ]
    exact finiteDeficiency_nonneg_of_valid _ _
      (causalFiniteExperiment_valid π.1 π.2 Qs hQ t)
      (causalPlanObservationExperiment_valid n τ Qs hQ)
  · exact causalNativeDeficiency_le_prefixDeficiency_of_nativelySufficient Qs hQ h t n

end FiniteClass

end IdExp
