import Formal.CausalSplicing
import Formal.CausalDeficiency
import Formal.CausalProcess
import Formal.CoverageBound
import Formal.ImportanceResampling

/-!
# Multi-episode causal coverage

This module connects the actual finite causal episode experiment to the
finite match/outcome rejection decoder in `CoverageBound.lean`.  Its scope is
the fixed behavior rule repeated independently after each reset and fixed
heterogeneous schedules. `AdaptiveEpisodicExecution.lean` supplies the separate
predictable sequential construction; `CausalPartialExecution.lean` proves the
from-ignorance certificate, and `CausalImportanceResampling.lean` supplies the
actual resampling decoder limit. The scheduler-gap modules instantiate the
strict comparison on literal causal transcripts.

The construction has three layers.

* `iidFiniteExperiment E N` is the experiment of `N` independent copies of a
  finite experiment `E`.  `iidStochasticRule G N` applies the same stochastic
  rule to each copy.  We prove that experiment validity and exact Blackwell
  garblings lift through this product.
* `causalEpisodicExperiment` specializes this product to the actual recorded
  action--observation trace of `N` reset episodes.
* For a fixed native plan, `causalEpisodeSummary` records whether the behavior
  trace agrees with the plan and retains its observation word.  Under uniform
  behavior its true row is exactly `|A|^{-n}` times the native target row, by
  `CausalSplicing.lean`.  The first-match decoder is then composed with this
  world-independent summary map.

Everything below is finite and uses only standard Mathlib axioms.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace IdExp

open Finset Set

noncomputable section

/-! ## Independent products of finite experiments and rules -/

variable {Θ X Y Z : Type*}

/-- Deterministic finite post-processing without exposing a decidable-equality
assumption in theorem statements. -/
def finiteMapRule [Fintype Y] (f : X → Y) : X → Y → ℝ := by
  classical
  exact fun x y => if y = f x then 1 else 0

theorem finiteMapRule_mem [Fintype Y] (f : X → Y) :
    finiteMapRule f ∈ stochasticRules X Y := by
  classical
  intro x _
  constructor
  · intro y
    by_cases h : y = f x <;> simp [finiteMapRule, h]
  · simp [finiteMapRule]

/-- The experiment formed by `N` independent copies of `E`. -/
def iidFiniteExperiment [Fintype X]
    (E : FiniteExperiment Θ X) (N : ℕ) :
    FiniteExperiment Θ (Fin N → X) :=
  fun θ x => ∏ i, E θ (x i)

theorem iidFiniteExperiment_valid [Fintype X]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) (N : ℕ) :
    IsFiniteExperiment (iidFiniteExperiment E N) := by
  intro θ
  constructor
  · intro x
    exact Finset.prod_nonneg fun i _ => (hE θ).1 (x i)
  · unfold iidFiniteExperiment
    rw [← Fintype.prod_sum]
    simp_rw [(hE θ).2]
    simp

/-- Apply the same stochastic rule independently to each of `N` signals. -/
def iidStochasticRule [Fintype Y]
    (G : X → Y → ℝ) (N : ℕ) :
    (Fin N → X) → (Fin N → Y) → ℝ :=
  fun x y => ∏ i, G (x i) (y i)

theorem iidStochasticRule_mem [Fintype Y]
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) (N : ℕ) :
    iidStochasticRule G N ∈ stochasticRules (Fin N → X) (Fin N → Y) := by
  intro x _
  constructor
  · intro y
    exact Finset.prod_nonneg fun i _ => ((hG (x i) (Set.mem_univ _)).1 (y i))
  · unfold iidStochasticRule
    rw [← Fintype.prod_sum]
    simp_rw [(hG _ (Set.mem_univ _)).2]
    simp

/-- Independent product commutes exactly with applying a stochastic rule. -/
theorem finiteDecisionLaw_iidStochasticRule
    [Fintype X] [Fintype Y]
    (E : FiniteExperiment Θ X) (G : X → Y → ℝ) (N : ℕ) :
    finiteDecisionLaw (iidFiniteExperiment E N) (iidStochasticRule G N) =
      iidFiniteExperiment (finiteDecisionLaw E G) N := by
  funext θ y
  unfold finiteDecisionLaw iidFiniteExperiment iidStochasticRule
  calc
    ∑ x : Fin N → X, (∏ i, E θ (x i)) * ∏ i, G (x i) (y i) =
        ∑ x : Fin N → X, ∏ i, (E θ (x i) * G (x i) (y i)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ x, E θ x * G x (y i) :=
      (Fintype.prod_sum (fun i x => E θ x * G x (y i))).symm

/-- Exact finite Blackwell garblings lift independently across episodes. -/
theorem iidFiniteBlackwellLE [Fintype X] [Fintype Y]
    {E : FiniteExperiment Θ X} {F : FiniteExperiment Θ Y}
    (hFE : FiniteBlackwellLE F E) (N : ℕ) :
    FiniteBlackwellLE (iidFiniteExperiment F N) (iidFiniteExperiment E N) := by
  rcases hFE with ⟨G, hG, hEq⟩
  refine ⟨iidStochasticRule G N, iidStochasticRule_mem G hG N, ?_⟩
  rw [finiteDecisionLaw_iidStochasticRule, hEq]

/-! ## The actual reset-episode transcript -/

variable {A O : Type*} [Fintype A] [Fintype O] [Nonempty A]

/-- The full recorded transcript of `N` independent reset episodes, each of
horizon `H`, under one fixed within-episode behavior policy. -/
def causalEpisodicExperiment
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    (H N : ℕ) : FiniteExperiment Θ (Fin N → CausalFiniteTrace A O H) :=
  iidFiniteExperiment (causalFiniteExperiment π Qs H) N

theorem causalEpisodicExperiment_valid
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (H N : ℕ) : IsFiniteExperiment (causalEpisodicExperiment π Qs H N) :=
  iidFiniteExperiment_valid _ (causalFiniteExperiment_valid π hπ Qs hQ H) N

/-- A longer recorded horizon Blackwell-dominates the shorter prefix in every
episode, and the dominance lifts to the complete reset transcript. -/
theorem causalEpisodicExperiment_prefix_blackwell_of_le
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {m H : ℕ} (hmH : m ≤ H) (N : ℕ) :
    FiniteBlackwellLE (causalEpisodicExperiment π Qs m N)
      (causalEpisodicExperiment π Qs H N) :=
  iidFiniteBlackwellLE
    (causalFiniteExperiment_prefix_blackwell_of_le π hπ Qs hQ hmH) N

/-! ## The plan-consistency summary -/

/-- The observable one-episode summary for a fixed native plan: whether the
recorded action trace agrees with the plan, together with the observation
word.  This is a deterministic and world-independent function of the full
recorded episode. -/
noncomputable def causalEpisodeSummary {n : ℕ} (τ : CausalPlan A O n)
    (w : CausalFiniteTrace A O n) : Bool × CausalObservationTrace O n := by
  classical
  exact (if CausalPlanAgreesTrace τ w then true else false,
    causalTraceObservations w)

/-- Deterministic summary channel from one causal episode. -/
def causalEpisodeSummaryRule {n : ℕ} (τ : CausalPlan A O n) :
    CausalFiniteTrace A O n → Bool × CausalObservationTrace O n → ℝ :=
  finiteMapRule (causalEpisodeSummary τ)

theorem causalEpisodeSummaryRule_mem {n : ℕ} (τ : CausalPlan A O n) :
    causalEpisodeSummaryRule τ ∈ stochasticRules
      (CausalFiniteTrace A O n) (Bool × CausalObservationTrace O n) :=
  finiteMapRule_mem _

/-- One-episode summary experiment obtained from the actual causal trace. -/
def causalEpisodeSummaryExperiment
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    {n : ℕ} (τ : CausalPlan A O n) :
    FiniteExperiment Θ (Bool × CausalObservationTrace O n) :=
  finiteDecisionLaw (causalFiniteExperiment π Qs n)
    (causalEpisodeSummaryRule τ)

theorem causalEpisodeSummaryExperiment_valid
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) :
    IsFiniteExperiment (causalEpisodeSummaryExperiment π Qs τ) :=
  finiteDecisionLaw_valid _ (causalFiniteExperiment_valid π hπ Qs hQ n)
    _ (causalEpisodeSummaryRule_mem τ)

/-- The matching row of the causal summary experiment is exactly the
single-episode splicing mass. -/
theorem causalEpisodeSummaryExperiment_true
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ)
    (o : CausalObservationTrace O n) :
    causalEpisodeSummaryExperiment π Qs τ θ (true, o) =
      causalSpliceMass π Qs τ θ o := by
  classical
  unfold causalEpisodeSummaryExperiment finiteDecisionLaw
    causalEpisodeSummaryRule finiteMapRule causalEpisodeSummary
    causalSpliceMass
  apply Finset.sum_congr rfl
  intro w _
  by_cases ha : CausalPlanAgreesTrace τ w
  · by_cases ho : causalTraceObservations w = o
    · simp [ha, ho]
    · have hone : (true, o) ≠ (true, causalTraceObservations w) := by
        intro h
        exact ho (Prod.mk.inj h).2.symm
      simp [ha, ho, hone]
  · simp [ha]

/-- Under uniform behavior the matching row of the actual causal summary is
`|A|^{-n}` times the native target law. -/
theorem causalEpisodeSummaryExperiment_true_uniform
    (Qs : Θ → CausalResponse A O) {n : ℕ} (τ : CausalPlan A O n)
    (θ : Θ) (o : CausalObservationTrace O n) :
    causalEpisodeSummaryExperiment (causalUniformPolicy A O) Qs τ θ (true, o) =
      (Fintype.card A : ℝ)⁻¹ ^ n *
        causalPlanObservationExperiment n τ Qs θ o := by
  rw [causalEpisodeSummaryExperiment_true,
    causalSpliceMass_eq_weight_mul_target, causalSpliceWeight_uniform]

/-! ### Completing the nonmatch row

The first-match theorem only uses the matching row.  To reuse its existing
finite proof literally, we normalize the arbitrary nonmatching row into a
probability vector.  The `p = 1` branch is harmless because that row then has
zero mass.
-/

/-- Normalize the nonmatching row of a valid `(match?, outcome)` law. -/
def failureOutcomeLaw {W : Type*} [Fintype W]
    (S : Bool × W → ℝ) (p : ℝ) (w0 : W) : W → ℝ := by
  classical
  exact fun w => if p = 1 then (if w = w0 then 1 else 0)
    else S (false, w) / (1 - p)

theorem sum_false_row
    {W : Type*} [Fintype W]
    {S : Bool × W → ℝ} {T : W → ℝ} {p : ℝ}
    (hS : IsDist S) (hT : IsDist T)
    (htrue : ∀ w, S (true, w) = p * T w) :
    ∑ w, S (false, w) = 1 - p := by
  have hmatch : ∑ w, S (true, w) = p := by
    simp_rw [htrue]
    rw [← Finset.mul_sum, hT.2, mul_one]
  have hall := hS.2
  rw [Fintype.sum_prod_type, Fintype.sum_bool, hmatch] at hall
  linarith

theorem false_row_eq_zero_of_p_eq_one
    {W : Type*} [Fintype W]
    {S : Bool × W → ℝ} {T : W → ℝ} {p : ℝ}
    (hS : IsDist S) (hT : IsDist T)
    (htrue : ∀ w, S (true, w) = p * T w)
    (hp : p = 1) (w : W) : S (false, w) = 0 := by
  have hsum : ∑ w, S (false, w) = 0 := by
    rw [sum_false_row hS hT htrue, hp, sub_self]
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun w _ => hS.1 (false, w))).1 hsum w (Finset.mem_univ w)

theorem failureOutcomeLaw_valid
    {W : Type*} [Fintype W]
    {S : Bool × W → ℝ} {T : W → ℝ} {p : ℝ}
    (hS : IsDist S) (hT : IsDist T)
    (htrue : ∀ w, S (true, w) = p * T w)
    (hp : p ≤ 1) (w0 : W) :
    IsDist (failureOutcomeLaw S p w0) := by
  classical
  by_cases hp1 : p = 1
  · have heq : failureOutcomeLaw S p w0 =
        (fun w => if w = w0 then (1 : ℝ) else 0) := by
      funext w
      simp [failureOutcomeLaw, hp1]
    rw [heq]
    exact CoverageBound.isDist_dirac w0
  · have hden : 0 < 1 - p := sub_pos.2 (lt_of_le_of_ne hp hp1)
    constructor
    · intro w
      simp only [failureOutcomeLaw, if_neg hp1]
      exact div_nonneg (hS.1 (false, w)) hden.le
    · simp only [failureOutcomeLaw, if_neg hp1]
      rw [← Finset.sum_div, sum_false_row hS hT htrue]
      exact div_self hden.ne'

/-- Every valid summary law with matching row `p*T` is exactly an `epLaw`;
the nonmatching outcome law may depend on the world, but the decoder does not.
-/
theorem summaryLaw_eq_epLaw
    {W : Type*} [Fintype W]
    {S : Bool × W → ℝ} {T : W → ℝ} {p : ℝ}
    (hS : IsDist S) (hT : IsDist T)
    (htrue : ∀ w, S (true, w) = p * T w)
    (w0 : W) :
    S = CoverageBound.epLaw p T (failureOutcomeLaw S p w0) := by
  classical
  funext z
  rcases z with ⟨b, w⟩
  cases b
  · simp only [CoverageBound.epLaw_false]
    by_cases hp1 : p = 1
    · rw [false_row_eq_zero_of_p_eq_one hS hT htrue hp1 w]
      simp [failureOutcomeLaw, hp1]
    · simp only [failureOutcomeLaw, if_neg hp1]
      field_simp
  · exact htrue w

/-! ## Multi-episode summary and its first-match decoder -/

/-- `N` independent copies of the actual one-episode summary experiment. -/
def causalSummaryTranscriptExperiment
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    {n : ℕ} (τ : CausalPlan A O n) (N : ℕ) :
    FiniteExperiment Θ (Fin N → Bool × CausalObservationTrace O n) :=
  iidFiniteExperiment (causalEpisodeSummaryExperiment π Qs τ) N

/-- The coordinatewise summary channel exactly sends the actual reset
transcript to the product summary experiment. -/
theorem causalEpisodic_to_summary
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    {n : ℕ} (τ : CausalPlan A O n) (N : ℕ) :
    finiteDecisionLaw (causalEpisodicExperiment π Qs n N)
        (iidStochasticRule (causalEpisodeSummaryRule τ) N) =
      causalSummaryTranscriptExperiment π Qs τ N := by
  exact finiteDecisionLaw_iidStochasticRule _ _ N

/-- First-match decoder on the summary transcript. -/
def summaryFirstMatchRule {n N : ℕ} (o0 : CausalObservationTrace O n) :
    (Fin N → Bool × CausalObservationTrace O n) →
      CausalObservationTrace O n → ℝ :=
  finiteMapRule (CoverageBound.firstMatch o0 N)

theorem summaryFirstMatchRule_mem {n N : ℕ}
    (o0 : CausalObservationTrace O n) :
    summaryFirstMatchRule o0 ∈ stochasticRules
      (Fin N → Bool × CausalObservationTrace O n)
      (CausalObservationTrace O n) :=
  finiteMapRule_mem _

/-- The actual causal decoder: summarize every recorded episode and return
the first matching observation word, with fallback `o0`. -/
def causalFirstMatchRule {n N : ℕ} (τ : CausalPlan A O n)
    (o0 : CausalObservationTrace O n) :
    (Fin N → CausalFiniteTrace A O n) → CausalObservationTrace O n → ℝ :=
  stochasticRuleComp (iidStochasticRule (causalEpisodeSummaryRule τ) N)
    (summaryFirstMatchRule o0)

theorem causalFirstMatchRule_mem {n N : ℕ} (τ : CausalPlan A O n)
    (o0 : CausalObservationTrace O n) :
    causalFirstMatchRule τ o0 ∈ stochasticRules
      (Fin N → CausalFiniteTrace A O n) (CausalObservationTrace O n) :=
  stochasticRuleComp_mem_stochasticRules
    (iidStochasticRule_mem _ (causalEpisodeSummaryRule_mem τ) N)
    (summaryFirstMatchRule_mem o0)

/-! ## Exact causal/abstract decoder identification -/

/-- Uniform matching probability for a depth-`n` plan. -/
def uniformMatchProb (A : Type*) [Fintype A] (n : ℕ) : ℝ :=
  (Fintype.card A : ℝ)⁻¹ ^ n

theorem uniformMatchProb_pos (A : Type*) [Fintype A] [Nonempty A] (n : ℕ) :
    0 < uniformMatchProb A n := by
  exact pow_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)) n

/-- The uniform match probability is at most one.  This proof derives the
bound from the actual normalized causal summary row, rather than from separate
cardinality arithmetic. -/
theorem uniformMatchProb_le_one
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ) :
    uniformMatchProb A n ≤ 1 := by
  let S := causalEpisodeSummaryExperiment (causalUniformPolicy A O) Qs τ θ
  let T := causalPlanObservationExperiment n τ Qs θ
  have hS : IsDist S :=
    (causalEpisodeSummaryExperiment_valid _ isCausalPolicy_uniform Qs hQ τ) θ
  have hT : IsDist T := (causalPlanObservationExperiment_valid n τ Qs hQ) θ
  have hmatch : ∑ o, S (true, o) = uniformMatchProb A n := by
    simp_rw [show ∀ o, S (true, o) = uniformMatchProb A n * T o by
      intro o
      exact causalEpisodeSummaryExperiment_true_uniform Qs τ θ o]
    rw [← Finset.mul_sum, hT.2, mul_one]
  have hfalse : 0 ≤ ∑ o, S (false, o) :=
    Finset.sum_nonneg fun o _ => hS.1 (false, o)
  have hall := hS.2
  rw [Fintype.sum_prod_type, Fintype.sum_bool, hmatch] at hall
  linarith

/-- Local-classical wrapper around the finite first-match output law. -/
def abstractCoverageOutputLaw {W : Type*} [Fintype W]
    (p : ℝ) (T R : W → ℝ) (w0 : W) (N : ℕ) : W → ℝ := by
  classical
  exact CoverageBound.outputLaw p T R w0 N

/-- Worldwise, the first-match decoder on the causal summary transcript has
exactly the already-verified `CoverageBound.outputLaw`.  The failure-row law
may vary with the world; the summary and first-match channels themselves do
not. -/
theorem causalSummary_firstMatch_output_eq
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ)
    (o0 : CausalObservationTrace O n) (N : ℕ) :
    finiteDecisionLaw
        (causalSummaryTranscriptExperiment (causalUniformPolicy A O) Qs τ N)
        (summaryFirstMatchRule o0) θ =
      abstractCoverageOutputLaw (uniformMatchProb A n)
        (causalPlanObservationExperiment n τ Qs θ)
        (failureOutcomeLaw
          (causalEpisodeSummaryExperiment (causalUniformPolicy A O) Qs τ θ)
          (uniformMatchProb A n) o0)
        o0 N := by
  classical
  let S := causalEpisodeSummaryExperiment (causalUniformPolicy A O) Qs τ θ
  let T := causalPlanObservationExperiment n τ Qs θ
  let p := uniformMatchProb A n
  let R := failureOutcomeLaw S p o0
  have hS : IsDist S :=
    (causalEpisodeSummaryExperiment_valid _ isCausalPolicy_uniform Qs hQ τ) θ
  have hT : IsDist T := (causalPlanObservationExperiment_valid n τ Qs hQ) θ
  have htrue : ∀ o, S (true, o) = p * T o := by
    intro o
    exact causalEpisodeSummaryExperiment_true_uniform Qs τ θ o
  have hrow : S = CoverageBound.epLaw p T R :=
    summaryLaw_eq_epLaw hS hT htrue o0
  change finiteDecisionLaw
      (causalSummaryTranscriptExperiment (causalUniformPolicy A O) Qs τ N)
      (summaryFirstMatchRule o0) θ =
    abstractCoverageOutputLaw p T R o0 N
  funext o
  unfold causalSummaryTranscriptExperiment iidFiniteExperiment
    summaryFirstMatchRule finiteMapRule finiteDecisionLaw
    abstractCoverageOutputLaw CoverageBound.outputLaw CoverageBound.transcriptLaw
  dsimp only [S] at hrow
  simp only
  rw [hrow]
  simp only [eq_comm]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  by_cases hx : o = CoverageBound.firstMatch o0 N x <;> simp [hx]

/-- Composing the coordinatewise summary with first-match processing gives
the same output law directly from the actual causal reset transcript. -/
theorem causalFirstMatch_decisionLaw_eq
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ)
    (o0 : CausalObservationTrace O n) (N : ℕ) :
    finiteDecisionLaw
        (causalEpisodicExperiment (causalUniformPolicy A O) Qs n N)
        (causalFirstMatchRule τ o0) θ =
      abstractCoverageOutputLaw (uniformMatchProb A n)
        (causalPlanObservationExperiment n τ Qs θ)
        (failureOutcomeLaw
          (causalEpisodeSummaryExperiment (causalUniformPolicy A O) Qs τ θ)
          (uniformMatchProb A n) o0)
        o0 N := by
  rw [show causalFirstMatchRule τ o0 =
      stochasticRuleComp (iidStochasticRule (causalEpisodeSummaryRule τ) N)
        (summaryFirstMatchRule o0) from rfl]
  rw [finiteDecisionLaw_stochasticRuleComp,
    causalEpisodic_to_summary]
  exact causalSummary_firstMatch_output_eq Qs hQ τ θ o0 N

/-- **Actual causal rejection-decoder bound.**  For one fixed native plan,
the decoder acting on `N` complete recorded reset episodes has worldwise error
at most `(1-|A|^{-n})^N`. -/
theorem decodeErr_causalFirstMatch_le
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ)
    (o0 : CausalObservationTrace O n) (N : ℕ) :
    decodeErr
        (causalEpisodicExperiment (causalUniformPolicy A O) Qs n N)
        (causalPlanObservationExperiment n τ Qs)
        (causalFirstMatchRule τ o0) θ ≤
      (1 - uniformMatchProb A n) ^ N := by
  classical
  letI : DecidableEq (CausalObservationTrace O n) := Classical.decEq _
  let S := causalEpisodeSummaryExperiment (causalUniformPolicy A O) Qs τ θ
  let T := causalPlanObservationExperiment n τ Qs θ
  let p := uniformMatchProb A n
  let R := failureOutcomeLaw S p o0
  have hS : IsDist S :=
    (causalEpisodeSummaryExperiment_valid _ isCausalPolicy_uniform Qs hQ τ) θ
  have hT : IsDist T := (causalPlanObservationExperiment_valid n τ Qs hQ) θ
  have htrue : ∀ o, S (true, o) = p * T o := by
    intro o
    exact causalEpisodeSummaryExperiment_true_uniform Qs τ θ o
  have hp : p ≤ 1 := uniformMatchProb_le_one Qs hQ τ θ
  have hR : IsDist R := failureOutcomeLaw_valid hS hT htrue hp o0
  change CoverageBound.tvDist
      (finiteDecisionLaw
        (causalEpisodicExperiment (causalUniformPolicy A O) Qs n N)
        (causalFirstMatchRule τ o0) θ) T ≤ (1 - p) ^ N
  rw [causalFirstMatch_decisionLaw_eq Qs hQ τ θ o0 N]
  change CoverageBound.tvDist (abstractCoverageOutputLaw p T R o0 N) T ≤
    (1 - p) ^ N
  unfold abstractCoverageOutputLaw
  exact CoverageBound.tvDist_outputLaw_le p hT hR hp o0 N

/-- The explicit decoder upper-bounds directed deficiency for an arbitrary
nonempty world class. -/
theorem finiteDeficiency_causalEpisodic_uniform_le
    [Nonempty Θ]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n)
    (o0 : CausalObservationTrace O n) (N : ℕ) :
    finiteDeficiency
        (causalEpisodicExperiment (causalUniformPolicy A O) Qs n N)
        (causalPlanObservationExperiment n τ Qs) ≤
      (1 - uniformMatchProb A n) ^ N := by
  apply finiteDeficiency_le_of_decoder _ _ (causalFirstMatchRule τ o0)
    (causalFirstMatchRule_mem τ o0) _
  intro θ
  exact decodeErr_causalFirstMatch_le Qs hQ τ θ o0 N

/-! ## Longer episode horizons and the complete depth audit -/

/-- Source monotonicity of finite deficiency for arbitrary world classes.
The library's duality-era helper assumes finite `Θ`; this direct decoder
composition needs only a nonempty class and validity of the intermediate and
target experiments. -/
theorem finiteDeficiency_mono_source_of_blackwellLE_arbitrary
    {Θ' X' Y' Z' : Type*}
    [Fintype X'] [Fintype Y'] [Fintype Z']
    [Nonempty Θ'] [Nonempty Z']
    (E : FiniteExperiment Θ' X') (D : FiniteExperiment Θ' Y')
    (F : FiniteExperiment Θ' Z')
    (hD : IsFiniteExperiment D) (hF : IsFiniteExperiment F)
    (hDE : FiniteBlackwellLE D E) :
    finiteDeficiency E F ≤ finiteDeficiency D F := by
  rcases hDE with ⟨G, hG, heq⟩
  apply le_csInf (finiteDeficiencyCandidates_nonempty_of_valid D F hD hF)
  rintro c ⟨H, hH, herr⟩
  apply finiteDeficiency_le_of_decoder E F (stochasticRuleComp G H)
    (stochasticRuleComp_mem_stochasticRules hG hH) c
  intro θ
  change finiteTV (finiteDecisionLaw E (stochasticRuleComp G H) θ) (F θ) ≤ c
  rw [finiteDecisionLaw_stochasticRuleComp, heq]
  exact herr θ

/-- A recorded horizon `H ≥ n` can ignore its suffix episodewise, so the same
uniform causal coverage certificate holds for one fixed depth-`n` plan. -/
theorem finiteDeficiency_causalEpisodic_uniform_le_of_le
    [Nonempty Θ] [Nonempty O]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n H : ℕ} (hnH : n ≤ H) (τ : CausalPlan A O n) (N : ℕ) :
    finiteDeficiency
        (causalEpisodicExperiment (causalUniformPolicy A O) Qs H N)
        (causalPlanObservationExperiment n τ Qs) ≤
      (1 - uniformMatchProb A n) ^ N := by
  let o0 : CausalObservationTrace O n := Classical.arbitrary _
  calc
    finiteDeficiency
        (causalEpisodicExperiment (causalUniformPolicy A O) Qs H N)
        (causalPlanObservationExperiment n τ Qs) ≤
      finiteDeficiency
        (causalEpisodicExperiment (causalUniformPolicy A O) Qs n N)
        (causalPlanObservationExperiment n τ Qs) :=
      finiteDeficiency_mono_source_of_blackwellLE_arbitrary _ _ _
        (causalEpisodicExperiment_valid _ isCausalPolicy_uniform Qs hQ n N)
        (causalPlanObservationExperiment_valid n τ Qs hQ)
        (causalEpisodicExperiment_prefix_blackwell_of_le
          _ isCausalPolicy_uniform Qs hQ hnH N)
    _ ≤ (1 - uniformMatchProb A n) ^ N :=
      finiteDeficiency_causalEpisodic_uniform_le Qs hQ τ o0 N

/-- **Uniform episodic coverage, actual causal transcript.**  At episode
horizon `H ≥ n`, the complete depth-`n` native audit of `N` i.i.d. uniform
episodes is at most `(1-|A|^{-n})^N`, for every nonempty world class. -/
theorem causalNativeDeficiency_causalEpisodic_uniform_le
    [Nonempty Θ] [Nonempty O]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n H : ℕ} (hnH : n ≤ H) (N : ℕ) :
    causalNativeDeficiency
        (causalEpisodicExperiment (causalUniformPolicy A O) Qs H N)
        Qs n ≤
      (1 - uniformMatchProb A n) ^ N := by
  obtain ⟨τ, hτ⟩ := exists_causalPlan_eq_nativeDeficiency
    (causalEpisodicExperiment (causalUniformPolicy A O) Qs H N) Qs n
  rw [hτ]
  exact finiteDeficiency_causalEpisodic_uniform_le_of_le Qs hQ hnH τ N

/-- Literal maximum over all native tests of depth at most `n`.  Existing
finite-horizon universality identifies it with the terminal-depth maximum, so
the causal transcript bound is exactly the paper's `Gamma_{≤n}` statement. -/
theorem causalNativeDeficiencyUpTo_causalEpisodic_uniform_le
    [Nonempty Θ] [Nonempty O]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n H : ℕ} (hnH : n ≤ H) (N : ℕ) :
    causalNativeDeficiencyUpTo
        (causalEpisodicExperiment (causalUniformPolicy A O) Qs H N)
        Qs n ≤
      (1 - uniformMatchProb A n) ^ N := by
  rw [causalNativeDeficiencyUpTo_eq_terminal
    (causalEpisodicExperiment (causalUniformPolicy A O) Qs H N)
    (causalEpisodicExperiment_valid _ isCausalPolicy_uniform Qs hQ H N)
    Qs hQ n]
  exact causalNativeDeficiency_causalEpisodic_uniform_le Qs hQ hnH N

/-- For every fixed native depth and sufficiently long episode horizon, the
literal episodic audit tends to zero geometrically as the number of reset
episodes grows. -/
theorem tendsto_causalNativeDeficiencyUpTo_causalEpisodic_uniform
    [Nonempty Θ] [Nonempty O]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n H : ℕ} (hnH : n ≤ H) :
    Filter.Tendsto
      (fun N => causalNativeDeficiencyUpTo
        (causalEpisodicExperiment (causalUniformPolicy A O) Qs H N)
        Qs n)
      Filter.atTop (nhds 0) := by
  let θ0 : Θ := Classical.arbitrary _
  have hp : uniformMatchProb A n ≤ 1 :=
    uniformMatchProb_le_one Qs hQ (Classical.arbitrary (CausalPlan A O n)) θ0
  apply squeeze_zero
  · intro N
    rw [causalNativeDeficiencyUpTo_eq_terminal
      (causalEpisodicExperiment (causalUniformPolicy A O) Qs H N)
      (causalEpisodicExperiment_valid _ isCausalPolicy_uniform Qs hQ H N)
      Qs hQ n]
    obtain ⟨τ, hτ⟩ := exists_causalPlan_eq_nativeDeficiency
      (causalEpisodicExperiment (causalUniformPolicy A O) Qs H N) Qs n
    rw [hτ]
    exact finiteDeficiency_nonneg_of_valid
      (causalEpisodicExperiment (causalUniformPolicy A O) Qs H N)
      (causalPlanObservationExperiment n τ Qs)
      (causalEpisodicExperiment_valid _ isCausalPolicy_uniform Qs hQ H N)
      (causalPlanObservationExperiment_valid n τ Qs hQ)
  · exact fun N =>
      causalNativeDeficiencyUpTo_causalEpisodic_uniform_le Qs hQ hnH N
  · exact CoverageBound.tendsto_coverage_bound
      (uniformMatchProb_pos A n) hp

/-! ## Arbitrary fixed behavior: the exact tilted transcript

The following results close the causal input side of the off-policy
formalization.  They do not add the self-normalized resampling limit again;
`ImportanceResampling.lean` already proves it for the resulting i.i.d. tilted
process.
-/

theorem causalPolicy_coordinate_le_one
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (h : CausalHistory A O) (a : A) : π h a ≤ 1 := by
  calc
    π h a ≤ ∑ b, π h b := Finset.single_le_sum
      (fun b _ => (hπ h).1 b) (Finset.mem_univ a)
    _ = 1 := (hπ h).2

theorem causalSpliceWeight_nonneg
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    {n : ℕ} (τ : CausalPlan A O n) (o : CausalObservationTrace O n) :
    0 ≤ causalSpliceWeight π τ o := by
  rw [causalSpliceWeight_eq_prod]
  exact Finset.prod_nonneg fun k _ =>
    (hπ (causalTracePrefix (causalTraceOfObservations τ o) k)).1 _

theorem causalSpliceWeight_le_one
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    {n : ℕ} (τ : CausalPlan A O n) (o : CausalObservationTrace O n) :
    causalSpliceWeight π τ o ≤ 1 := by
  rw [causalSpliceWeight_eq_prod]
  exact Finset.prod_le_one
    (fun k _ => (hπ (causalTracePrefix (causalTraceOfObservations τ o) k)).1 _)
    (fun k _ => causalPolicy_coordinate_le_one π hπ _ _)

/-- For arbitrary fixed behavior, the actual one-episode causal summary is
exactly the tilted law used by `ImportanceResampling.lean`.  The hypothesis
`p>0` is precisely positive consistency probability for this test and world.
-/
theorem causalEpisodeSummaryExperiment_eq_tiltedLaw
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ)
    (o0 : CausalObservationTrace O n)
    (hp : 0 < ImportanceResampling.consProb
      (causalSpliceWeight π τ)
      (causalPlanObservationExperiment n τ Qs θ)) :
    causalEpisodeSummaryExperiment π Qs τ θ =
      ImportanceResampling.tiltedLaw
        (causalSpliceWeight π τ)
        (causalPlanObservationExperiment n τ Qs θ)
        (failureOutcomeLaw
          (causalEpisodeSummaryExperiment π Qs τ θ)
          (ImportanceResampling.consProb
            (causalSpliceWeight π τ)
            (causalPlanObservationExperiment n τ Qs θ))
          o0) := by
  classical
  letI : DecidableEq (CausalObservationTrace O n) := Classical.decEq _
  let S := causalEpisodeSummaryExperiment π Qs τ θ
  let w := causalSpliceWeight π τ
  let T := causalPlanObservationExperiment n τ Qs θ
  let p := ImportanceResampling.consProb w T
  let U := ImportanceResampling.tiltedOutcome w T
  let R := failureOutcomeLaw S p o0
  have hS : IsDist S :=
    (causalEpisodeSummaryExperiment_valid π hπ Qs hQ τ) θ
  have hT : IsDist T := (causalPlanObservationExperiment_valid n τ Qs hQ) θ
  have hw0 : ∀ o, 0 ≤ w o := fun o => causalSpliceWeight_nonneg π hπ τ o
  have hU : IsDist U := ImportanceResampling.isDist_tiltedOutcome hw0 hT hp
  have htrueRaw : ∀ o, S (true, o) = w o * T o := by
    intro o
    change causalEpisodeSummaryExperiment π Qs τ θ (true, o) =
      causalSpliceWeight π τ o *
        causalPlanObservationExperiment n τ Qs θ o
    rw [causalEpisodeSummaryExperiment_true,
      causalSpliceMass_eq_weight_mul_target]
  have htrue : ∀ o, S (true, o) = p * U o := by
    intro o
    rw [htrueRaw]
    unfold U ImportanceResampling.tiltedOutcome
    exact (mul_div_cancel₀ (w o * T o) hp.ne').symm
  have hrow : S = CoverageBound.epLaw p U R :=
    summaryLaw_eq_epLaw hS hU htrue o0
  have htilt : ImportanceResampling.tiltedLaw w T R =
      CoverageBound.epLaw p U R :=
    ImportanceResampling.tiltedLaw_eq_epLaw hp.ne'
  change S = ImportanceResampling.tiltedLaw w T R
  exact hrow.trans htilt.symm

/-- Consequently, every finite summary transcript of the actual causal reset
experiment has exactly the tilted i.i.d. product likelihood assumed by the
importance-resampling proofs. -/
theorem causalSummaryTranscriptExperiment_eq_tilted
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ)
    (o0 : CausalObservationTrace O n) (N : ℕ)
    (hp : 0 < ImportanceResampling.consProb
      (causalSpliceWeight π τ)
      (causalPlanObservationExperiment n τ Qs θ)) :
    causalSummaryTranscriptExperiment π Qs τ N θ =
      ImportanceResampling.tiltedTranscriptLaw
        (causalSpliceWeight π τ)
        (causalPlanObservationExperiment n τ Qs θ)
        (failureOutcomeLaw
          (causalEpisodeSummaryExperiment π Qs τ θ)
          (ImportanceResampling.consProb
            (causalSpliceWeight π τ)
            (causalPlanObservationExperiment n τ Qs θ))
          o0)
        N := by
  let S := causalEpisodeSummaryExperiment π Qs τ θ
  let w := causalSpliceWeight π τ
  let T := causalPlanObservationExperiment n τ Qs θ
  let p := ImportanceResampling.consProb w T
  let R := failureOutcomeLaw S p o0
  change causalSummaryTranscriptExperiment π Qs τ N θ =
    ImportanceResampling.tiltedTranscriptLaw w T R N
  have hrow : S = ImportanceResampling.tiltedLaw w T R :=
    causalEpisodeSummaryExperiment_eq_tiltedLaw π hπ Qs hQ τ θ o0 hp
  funext x
  change (∏ i, S (x i)) = ∏ i, ImportanceResampling.tiltedLaw w T R (x i)
  rw [hrow]

/-! ## Bernoulli thinning as an actual stochastic summary channel -/

/-- Given one summary, draw the thinning coin and push it through `thin`.
This is the Markov channel implicit in `ImportanceResampling.thinnedLaw`. -/
def thinningSummaryRule {W : Type*} [Fintype W]
    (ε : ℝ) (w : W → ℝ) : (Bool × W) → (Bool × W) → ℝ := by
  classical
  exact fun a b => ∑ coin : Bool,
    (if coin then ImportanceResampling.acceptProb ε w a
      else 1 - ImportanceResampling.acceptProb ε w a) *
    (if ImportanceResampling.thin (a, coin) = b then 1 else 0)

theorem acceptProb_nonneg
    {W : Type*} [Fintype W]
    {ε : ℝ} {w : W → ℝ} (hε : 0 < ε) (hεw : ∀ o, ε ≤ w o)
    (a : Bool × W) : 0 ≤ ImportanceResampling.acceptProb ε w a := by
  rcases a with ⟨b, o⟩
  cases b
  · simp [ImportanceResampling.acceptProb]
  · simp only [ImportanceResampling.acceptProb, if_true]
    exact div_nonneg hε.le (hε.trans_le (hεw o)).le

theorem acceptProb_le_one
    {W : Type*} [Fintype W]
    {ε : ℝ} {w : W → ℝ} (hε : 0 < ε) (hεw : ∀ o, ε ≤ w o)
    (a : Bool × W) : ImportanceResampling.acceptProb ε w a ≤ 1 := by
  rcases a with ⟨b, o⟩
  cases b
  · simp [ImportanceResampling.acceptProb]
  · simp only [ImportanceResampling.acceptProb, if_true]
    exact (div_le_one (hε.trans_le (hεw o))).2 (hεw o)

theorem thinningSummaryRule_mem
    {W : Type*} [Fintype W]
    {ε : ℝ} {w : W → ℝ} (hε : 0 < ε) (hεw : ∀ o, ε ≤ w o) :
    thinningSummaryRule ε w ∈ stochasticRules (Bool × W) (Bool × W) := by
  classical
  intro a _
  constructor
  · intro b
    unfold thinningSummaryRule
    exact Finset.sum_nonneg fun coin _ => mul_nonneg
      (by cases coin
          · exact sub_nonneg.2 (acceptProb_le_one hε hεw a)
          · exact acceptProb_nonneg hε hεw a)
      (by split <;> norm_num)
  · unfold thinningSummaryRule
    rw [Finset.sum_comm]
    calc
      ∑ coin : Bool, ∑ b : Bool × W,
          (if coin then ImportanceResampling.acceptProb ε w a
            else 1 - ImportanceResampling.acceptProb ε w a) *
          (if ImportanceResampling.thin (a, coin) = b then 1 else 0) =
        ∑ coin : Bool,
          (if coin then ImportanceResampling.acceptProb ε w a
            else 1 - ImportanceResampling.acceptProb ε w a) := by
          apply Finset.sum_congr rfl
          intro coin _
          rw [← Finset.mul_sum]
          simp
      _ = 1 := by rw [Fintype.sum_bool]; simp

/-- Local-classical wrapper around the already-verified thinned law. -/
def abstractThinnedLaw {W : Type*} [Fintype W]
    (ε : ℝ) (w T R : W → ℝ) : Bool × W → ℝ := by
  classical
  exact ImportanceResampling.thinnedLaw ε w T R

/-- Applying the explicit thinning channel to the tilted one-episode law is
exactly the `thinnedLaw` already analyzed in `ImportanceResampling.lean`. -/
theorem finiteDecisionLaw_tilted_thinning
    {W : Type*} [Fintype W]
    (ε : ℝ) (w T R : W → ℝ) :
    finiteDecisionLaw
        (fun (_ : Unit) => ImportanceResampling.tiltedLaw w T R)
        (thinningSummaryRule ε w) () =
      abstractThinnedLaw ε w T R := by
  classical
  funext b
  unfold finiteDecisionLaw thinningSummaryRule
    abstractThinnedLaw ImportanceResampling.thinnedLaw ImportanceResampling.coinLaw
  nth_rewrite 2 [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coin _
  ring

theorem pow_floor_le_causalSpliceWeight
    (π : CausalPolicy A O) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hfloor : ∀ h a, ε ≤ π h a)
    {n : ℕ} (τ : CausalPlan A O n) (o : CausalObservationTrace O n) :
    ε ^ n ≤ causalSpliceWeight π τ o := by
  rw [causalSpliceWeight_eq_prod]
  calc
    ε ^ n = ∏ _k : Fin n, ε := by simp
    _ ≤ ∏ k : Fin n,
        π (causalTracePrefix (causalTraceOfObservations τ o) k)
          (τ (causalTraceDecisionPoint (causalTraceOfObservations τ o) k)) := by
      exact Finset.prod_le_prod (fun _ _ => hε0) (fun k _ => hfloor _ _)

/-- One causal episode after the explicit thinning channel. -/
def causalThinnedEpisodeExperiment
    (ε : ℝ) (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    {n : ℕ} (τ : CausalPlan A O n) :
    FiniteExperiment Θ (Bool × CausalObservationTrace O n) :=
  finiteDecisionLaw (causalEpisodeSummaryExperiment π Qs τ)
    (thinningSummaryRule ε (causalSpliceWeight π τ))

theorem causalThinnedEpisodeExperiment_valid
    {ε : ℝ} (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n)
    (hε : 0 < ε) (hεw : ∀ o, ε ≤ causalSpliceWeight π τ o) :
    IsFiniteExperiment (causalThinnedEpisodeExperiment ε π Qs τ) :=
  finiteDecisionLaw_valid _
    (causalEpisodeSummaryExperiment_valid π hπ Qs hQ τ) _
    (thinningSummaryRule_mem hε hεw)

/-- The thinned transcript consists of independent copies of the thinned
causal summary experiment. -/
def causalThinnedTranscriptExperiment
    (ε : ℝ) (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    {n : ℕ} (τ : CausalPlan A O n) (N : ℕ) :
    FiniteExperiment Θ (Fin N → Bool × CausalObservationTrace O n) :=
  iidFiniteExperiment (causalThinnedEpisodeExperiment ε π Qs τ) N

theorem causalThinnedTranscriptExperiment_valid
    {ε : ℝ} (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (N : ℕ)
    (hε : 0 < ε) (hεw : ∀ o, ε ≤ causalSpliceWeight π τ o) :
    IsFiniteExperiment (causalThinnedTranscriptExperiment ε π Qs τ N) :=
  iidFiniteExperiment_valid _
    (causalThinnedEpisodeExperiment_valid π hπ Qs hQ τ hε hεw) N

/-- Thinning the per-episode causal summaries is an exact Blackwell garbling
of the complete causal reset transcript. -/
theorem causalThinnedTranscript_blackwell
    {ε : ℝ} (π : CausalPolicy A O)
    (Qs : Θ → CausalResponse A O)
    {n : ℕ} (τ : CausalPlan A O n) (N : ℕ)
    (hε : 0 < ε) (hεw : ∀ o, ε ≤ causalSpliceWeight π τ o) :
    FiniteBlackwellLE (causalThinnedTranscriptExperiment ε π Qs τ N)
      (causalEpisodicExperiment π Qs n N) := by
  have hsummary : FiniteBlackwellLE
      (causalEpisodeSummaryExperiment π Qs τ)
      (causalFiniteExperiment π Qs n) :=
    ⟨causalEpisodeSummaryRule τ, causalEpisodeSummaryRule_mem τ, rfl⟩
  have hthin : FiniteBlackwellLE
      (causalThinnedEpisodeExperiment ε π Qs τ)
      (causalEpisodeSummaryExperiment π Qs τ) :=
    ⟨thinningSummaryRule ε (causalSpliceWeight π τ),
      thinningSummaryRule_mem hε hεw, rfl⟩
  exact iidFiniteBlackwellLE (finiteBlackwellLE_trans hthin hsummary) N

/-- The actual one-episode causal thinning experiment has the same row as the
abstract thinned law, world by world. -/
theorem causalThinnedEpisodeExperiment_eq_abstract
    {ε : ℝ} (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ)
    (o0 : CausalObservationTrace O n)
    (hp : 0 < ImportanceResampling.consProb
      (causalSpliceWeight π τ)
      (causalPlanObservationExperiment n τ Qs θ)) :
    causalThinnedEpisodeExperiment ε π Qs τ θ =
      abstractThinnedLaw ε
        (causalSpliceWeight π τ)
        (causalPlanObservationExperiment n τ Qs θ)
        (failureOutcomeLaw
          (causalEpisodeSummaryExperiment π Qs τ θ)
          (ImportanceResampling.consProb
            (causalSpliceWeight π τ)
            (causalPlanObservationExperiment n τ Qs θ))
          o0) := by
  let S := causalEpisodeSummaryExperiment π Qs τ θ
  let w := causalSpliceWeight π τ
  let T := causalPlanObservationExperiment n τ Qs θ
  let p := ImportanceResampling.consProb w T
  let R := failureOutcomeLaw S p o0
  have hrow : S = ImportanceResampling.tiltedLaw w T R :=
    causalEpisodeSummaryExperiment_eq_tiltedLaw π hπ Qs hQ τ θ o0 hp
  change finiteDecisionLaw (fun (_ : Unit) => S)
      (thinningSummaryRule ε w) () = abstractThinnedLaw ε w T R
  rw [hrow]
  exact finiteDecisionLaw_tilted_thinning ε w T R

/-- Local-classical wrapper around the thinned first-match output law. -/
def abstractThinnedOutputLaw {W : Type*} [Fintype W]
    (ε : ℝ) (w T R : W → ℝ) (w0 : W) (N : ℕ) : W → ℝ := by
  classical
  exact ImportanceResampling.thinnedOutputLaw ε w T R w0 N

/-- First-match decoding of the actual thinned transcript is exactly the
verified abstract thinned output law. -/
theorem causalThinned_firstMatch_output_eq
    {ε : ℝ} (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ)
    (o0 : CausalObservationTrace O n) (N : ℕ)
    (hp : 0 < ImportanceResampling.consProb
      (causalSpliceWeight π τ)
      (causalPlanObservationExperiment n τ Qs θ)) :
    finiteDecisionLaw (causalThinnedTranscriptExperiment ε π Qs τ N)
        (summaryFirstMatchRule o0) θ =
      abstractThinnedOutputLaw ε
        (causalSpliceWeight π τ)
        (causalPlanObservationExperiment n τ Qs θ)
        (failureOutcomeLaw
          (causalEpisodeSummaryExperiment π Qs τ θ)
          (ImportanceResampling.consProb
            (causalSpliceWeight π τ)
            (causalPlanObservationExperiment n τ Qs θ))
          o0)
        o0 N := by
  classical
  letI : DecidableEq (CausalObservationTrace O n) := Classical.decEq _
  let D := causalThinnedEpisodeExperiment ε π Qs τ θ
  let w := causalSpliceWeight π τ
  let T := causalPlanObservationExperiment n τ Qs θ
  let p := ImportanceResampling.consProb w T
  let R := failureOutcomeLaw
    (causalEpisodeSummaryExperiment π Qs τ θ) p o0
  have hrow : D = abstractThinnedLaw ε w T R :=
    causalThinnedEpisodeExperiment_eq_abstract π hπ Qs hQ τ θ o0 hp
  change finiteDecisionLaw
      (causalThinnedTranscriptExperiment ε π Qs τ N)
      (summaryFirstMatchRule o0) θ =
    abstractThinnedOutputLaw ε w T R o0 N
  funext o
  unfold causalThinnedTranscriptExperiment iidFiniteExperiment
    summaryFirstMatchRule finiteMapRule finiteDecisionLaw
    abstractThinnedOutputLaw ImportanceResampling.thinnedOutputLaw
    ImportanceResampling.thinnedTranscriptLaw
  dsimp only [D] at hrow
  unfold abstractThinnedLaw at hrow
  simp only
  rw [hrow]
  simp only [eq_comm]

theorem le_consProb_of_weight_floor
    {W : Type*} [Fintype W]
    {ε : ℝ} {w T : W → ℝ} (hT : IsDist T)
    (hεw : ∀ o, ε ≤ w o) :
    ε ≤ ImportanceResampling.consProb w T := by
  unfold ImportanceResampling.consProb
  calc
    ε = ∑ o, ε * T o := by rw [← Finset.mul_sum, hT.2, mul_one]
    _ ≤ ∑ o, w o * T o := Finset.sum_le_sum fun o _ =>
      mul_le_mul_of_nonneg_right (hεw o) (hT.1 o)

/-- First-match decoding of the actual thinned causal-summary transcript has
the existing exponential worldwise TV guarantee. -/
theorem decodeErr_causalThinned_firstMatch_le
    {ε : ℝ} (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ)
    (o0 : CausalObservationTrace O n) (N : ℕ)
    (hε : 0 < ε) (hεw : ∀ o, ε ≤ causalSpliceWeight π τ o) :
    decodeErr (causalThinnedTranscriptExperiment ε π Qs τ N)
        (causalPlanObservationExperiment n τ Qs)
        (summaryFirstMatchRule o0) θ ≤
      (1 - ε) ^ N := by
  classical
  letI : DecidableEq (CausalObservationTrace O n) := Classical.decEq _
  let S := causalEpisodeSummaryExperiment π Qs τ θ
  let w := causalSpliceWeight π τ
  let T := causalPlanObservationExperiment n τ Qs θ
  let p := ImportanceResampling.consProb w T
  let U := ImportanceResampling.tiltedOutcome w T
  let R := failureOutcomeLaw S p o0
  have hS : IsDist S :=
    (causalEpisodeSummaryExperiment_valid π hπ Qs hQ τ) θ
  have hT : IsDist T := (causalPlanObservationExperiment_valid n τ Qs hQ) θ
  have hw0 : ∀ o, 0 ≤ w o := fun o => causalSpliceWeight_nonneg π hπ τ o
  have hw1 : ∀ o, w o ≤ 1 := fun o => causalSpliceWeight_le_one π hπ τ o
  have hp : 0 < p := hε.trans_le (le_consProb_of_weight_floor hT hεw)
  have hp1 : p ≤ 1 := ImportanceResampling.consProb_le_one hw1 hT
  have hU : IsDist U := ImportanceResampling.isDist_tiltedOutcome hw0 hT hp
  have htrueRaw : ∀ o, S (true, o) = w o * T o := by
    intro o
    change causalEpisodeSummaryExperiment π Qs τ θ (true, o) =
      causalSpliceWeight π τ o *
        causalPlanObservationExperiment n τ Qs θ o
    rw [causalEpisodeSummaryExperiment_true,
      causalSpliceMass_eq_weight_mul_target]
  have htrue : ∀ o, S (true, o) = p * U o := by
    intro o
    rw [htrueRaw]
    unfold U ImportanceResampling.tiltedOutcome
    exact (mul_div_cancel₀ (w o * T o) hp.ne').symm
  have hR : IsDist R := failureOutcomeLaw_valid hS hU htrue hp1 o0
  change CoverageBound.tvDist
      (finiteDecisionLaw (causalThinnedTranscriptExperiment ε π Qs τ N)
        (summaryFirstMatchRule o0) θ) T ≤ (1 - ε) ^ N
  rw [causalThinned_firstMatch_output_eq π hπ Qs hQ τ θ o0 N hp]
  change CoverageBound.tvDist (abstractThinnedOutputLaw ε w T R o0 N) T ≤
    (1 - ε) ^ N
  unfold abstractThinnedOutputLaw
  exact ImportanceResampling.tvDist_thinnedOutputLaw_le
    hε hεw hw1 hT hR o0 N

/-- Deficiency of the thinned transcript to the requested native test. -/
theorem finiteDeficiency_causalThinned_le
    [Nonempty Θ]
    {ε : ℝ} (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n)
    (o0 : CausalObservationTrace O n) (N : ℕ)
    (hε : 0 < ε) (hεw : ∀ o, ε ≤ causalSpliceWeight π τ o) :
    finiteDeficiency (causalThinnedTranscriptExperiment ε π Qs τ N)
        (causalPlanObservationExperiment n τ Qs) ≤
      (1 - ε) ^ N := by
  apply finiteDeficiency_le_of_decoder _ _ (summaryFirstMatchRule o0)
    (summaryFirstMatchRule_mem o0) _
  intro θ
  exact decodeErr_causalThinned_firstMatch_le
    π hπ Qs hQ τ θ o0 N hε hεw

/-- **Actual causal Bernoulli-thinning certificate for one test.**  If the
behavior propensity of every observation branch of `τ` is at least `ε>0`,
then `N` reset episodes simulate its native law within `(1-ε)^N`. -/
theorem finiteDeficiency_causalEpisodic_thinning_le
    [Nonempty Θ] [Nonempty O]
    {ε : ℝ} (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (N : ℕ)
    (hε : 0 < ε) (hεw : ∀ o, ε ≤ causalSpliceWeight π τ o) :
    finiteDeficiency (causalEpisodicExperiment π Qs n N)
        (causalPlanObservationExperiment n τ Qs) ≤
      (1 - ε) ^ N := by
  let o0 : CausalObservationTrace O n := Classical.arbitrary _
  calc
    finiteDeficiency (causalEpisodicExperiment π Qs n N)
        (causalPlanObservationExperiment n τ Qs) ≤
      finiteDeficiency (causalThinnedTranscriptExperiment ε π Qs τ N)
        (causalPlanObservationExperiment n τ Qs) :=
      finiteDeficiency_mono_source_of_blackwellLE_arbitrary _ _ _
        (causalThinnedTranscriptExperiment_valid π hπ Qs hQ τ N hε hεw)
        (causalPlanObservationExperiment_valid n τ Qs hQ)
        (causalThinnedTranscript_blackwell π Qs τ N hε hεw)
    _ ≤ (1 - ε) ^ N :=
      finiteDeficiency_causalThinned_le π hπ Qs hQ τ o0 N hε hεw

/-- The same path-weight certificate for recorded episode horizon `H≥n`. -/
theorem finiteDeficiency_causalEpisodic_thinning_le_of_le
    [Nonempty Θ] [Nonempty O]
    {ε : ℝ} (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n H : ℕ} (hnH : n ≤ H) (τ : CausalPlan A O n) (N : ℕ)
    (hε : 0 < ε) (hεw : ∀ o, ε ≤ causalSpliceWeight π τ o) :
    finiteDeficiency (causalEpisodicExperiment π Qs H N)
        (causalPlanObservationExperiment n τ Qs) ≤
      (1 - ε) ^ N := by
  calc
    finiteDeficiency (causalEpisodicExperiment π Qs H N)
        (causalPlanObservationExperiment n τ Qs) ≤
      finiteDeficiency (causalEpisodicExperiment π Qs n N)
        (causalPlanObservationExperiment n τ Qs) :=
      finiteDeficiency_mono_source_of_blackwellLE_arbitrary _ _ _
        (causalEpisodicExperiment_valid π hπ Qs hQ n N)
        (causalPlanObservationExperiment_valid n τ Qs hQ)
        (causalEpisodicExperiment_prefix_blackwell_of_le π hπ Qs hQ hnH N)
    _ ≤ (1 - ε) ^ N :=
      finiteDeficiency_causalEpisodic_thinning_le
        π hπ Qs hQ τ N hε hεw

/-- **Per-action-floor episodic certificate, actual causal transcript.**  If
the fixed behavior policy assigns every action probability at least `ε>0`,
then the literal depth-at-most-`n` audit after `N` reset episodes is bounded by
`(1-ε^n)^N`, for an arbitrary nonempty world class. -/
theorem causalNativeDeficiencyUpTo_causalEpisodic_floor_le
    [Nonempty Θ] [Nonempty O]
    {ε : ℝ} (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (hfloor : ∀ h a, ε ≤ π h a) (hε : 0 < ε)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n H : ℕ} (hnH : n ≤ H) (N : ℕ) :
    causalNativeDeficiencyUpTo (causalEpisodicExperiment π Qs H N) Qs n ≤
      (1 - ε ^ n) ^ N := by
  rw [causalNativeDeficiencyUpTo_eq_terminal
    (causalEpisodicExperiment π Qs H N)
    (causalEpisodicExperiment_valid π hπ Qs hQ H N) Qs hQ n]
  obtain ⟨τ, hτ⟩ := exists_causalPlan_eq_nativeDeficiency
    (causalEpisodicExperiment π Qs H N) Qs n
  rw [hτ]
  apply finiteDeficiency_causalEpisodic_thinning_le_of_le
    π hπ Qs hQ hnH τ N (pow_pos hε n)
  exact fun o => pow_floor_le_causalSpliceWeight π hε.le hfloor τ o

/-! ## Independent deterministic schedules: exact executed tests

This is the nonadaptive part of Proposition `prop:episodic`(b).  Episode
policies may differ, but are fixed before the experiment.  A target literally
run in one episode is an exact garbling of the whole recorded transcript.
The stronger predictable/adaptive first-execution wrapper is proved separately
in `AdaptiveEpisodicExecution.lean`.
-/

/-- Product of an indexed family of independent, not necessarily identical,
finite experiments. -/
def independentFiniteExperiment
    {I : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (E : I → FiniteExperiment Θ X) : FiniteExperiment Θ (I → X) :=
  fun θ x => ∏ i, E i θ (x i)

theorem independentFiniteExperiment_valid
    {I : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (E : I → FiniteExperiment Θ X) (hE : ∀ i, IsFiniteExperiment (E i)) :
    IsFiniteExperiment (independentFiniteExperiment E) := by
  intro θ
  constructor
  · intro x
    exact Finset.prod_nonneg fun i _ => (hE i θ).1 (x i)
  · unfold independentFiniteExperiment
    rw [← Fintype.prod_sum]
    simp_rw [(hE _ θ).2]
    simp

/-- Marginalization identity for a product whose coordinate laws may vary. -/
theorem sum_family_prod_mul_eval
    {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E]
    (f : I → E → ℝ) (hf : ∀ i, ∑ a, f i a = 1)
    (k : I) (g : E → ℝ) :
    ∑ x : I → E, (∏ i, f i (x i)) * g (x k) =
      ∑ a, f k a * g a := by
  set F : I → E → ℝ := fun i a => f i a * if i = k then g a else 1 with hF
  have hprod : ∀ x : I → E,
      (∏ i, f i (x i)) * g (x k) = ∏ i, F i (x i) := by
    intro x
    simp only [hF]
    rw [Finset.prod_mul_distrib]
    have hg : (∏ i : I, if i = k then g (x i) else 1) = g (x k) := by
      simp
    rw [hg]
  have hsum : ∀ i, (∑ a, F i a) =
      if i = k then ∑ a, f k a * g a else 1 := by
    intro i
    by_cases hik : i = k
    · subst i
      simp [hF]
    · simp [hF, hik, hf]
  calc
    ∑ x : I → E, (∏ i, f i (x i)) * g (x k) =
        ∑ x : I → E, ∏ i, F i (x i) :=
      Finset.sum_congr rfl fun x _ => hprod x
    _ = ∏ i, ∑ a, F i a := (Fintype.prod_sum F).symm
    _ = ∏ i, (if i = k then ∑ a, f k a * g a else 1) :=
      Finset.prod_congr rfl fun i _ => hsum i
    _ = ∑ a, f k a * g a := by simp

/-- Deterministically select one episode from a recorded independent
transcript. -/
def episodeCoordinateRule
    {I : Type*} [Fintype I] [DecidableEq I] [Fintype X] (k : I) :
    (I → X) → X → ℝ :=
  finiteMapRule (fun x => x k)

theorem episodeCoordinateRule_mem
    {I : Type*} [Fintype I] [DecidableEq I] [Fintype X] (k : I) :
    episodeCoordinateRule (X := X) k ∈ stochasticRules (I → X) X :=
  finiteMapRule_mem _

theorem finiteDecisionLaw_independent_coordinate
    {I : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (E : I → FiniteExperiment Θ X) (hE : ∀ i, IsFiniteExperiment (E i))
    (k : I) :
    finiteDecisionLaw (independentFiniteExperiment E)
        (episodeCoordinateRule k) = E k := by
  classical
  funext θ y
  unfold finiteDecisionLaw independentFiniteExperiment
    episodeCoordinateRule finiteMapRule
  rw [sum_family_prod_mul_eval (fun i => E i θ) (fun i => (hE i θ).2)
    k (fun x => if y = x then 1 else 0)]
  simp

theorem independent_coordinate_blackwell
    {I : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (E : I → FiniteExperiment Θ X) (hE : ∀ i, IsFiniteExperiment (E i))
    (k : I) :
    FiniteBlackwellLE (E k) (independentFiniteExperiment E) :=
  ⟨episodeCoordinateRule k, episodeCoordinateRule_mem k,
    finiteDecisionLaw_independent_coordinate E hE k⟩

/-- Actual transcript of independent reset episodes whose within-episode
behavior policies may vary according to a fixed schedule. -/
def causalScheduledEpisodicExperiment
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → CausalPolicy A O) (Qs : Θ → CausalResponse A O) (H : ℕ) :
    FiniteExperiment Θ (I → CausalFiniteTrace A O H) :=
  independentFiniteExperiment (fun i => causalFiniteExperiment (ρ i) Qs H)

theorem causalScheduledEpisodicExperiment_valid
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → CausalPolicy A O) (hρ : ∀ i, IsCausalPolicy (ρ i))
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (H : ℕ) : IsFiniteExperiment (causalScheduledEpisodicExperiment ρ Qs H) :=
  independentFiniteExperiment_valid _ fun i =>
    causalFiniteExperiment_valid (ρ i) (hρ i) Qs hQ H

/-- Any finite experiment exactly available in one scheduled episode is
exactly available from the whole scheduled transcript. -/
theorem causalScheduled_target_blackwell
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → CausalPolicy A O) (hρ : ∀ i, IsCausalPolicy (ρ i))
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (H : ℕ) (k : I) {Y' : Type*} [Fintype Y']
    (F : FiniteExperiment Θ Y')
    (hF : FiniteBlackwellLE F (causalFiniteExperiment (ρ k) Qs H)) :
    FiniteBlackwellLE F (causalScheduledEpisodicExperiment ρ Qs H) := by
  apply finiteBlackwellLE_trans hF
  exact independent_coordinate_blackwell
    (fun i => causalFiniteExperiment (ρ i) Qs H)
    (fun i => causalFiniteExperiment_valid (ρ i) (hρ i) Qs hQ H) k

/-- Concrete literal-execution case: if scheduled episode `k` runs the
target deterministic plan, its observation experiment is an exact garbling
of the whole transcript. -/
theorem causalScheduled_plan_blackwell
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → CausalPolicy A O) (hρ : ∀ i, IsCausalPolicy (ρ i))
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (k : I)
    (hk : ρ k = causalPolicyOfPlan n τ) :
    FiniteBlackwellLE (causalPlanObservationExperiment n τ Qs)
      (causalScheduledEpisodicExperiment ρ Qs n) := by
  apply causalScheduled_target_blackwell ρ hρ Qs hQ n k
  rw [hk]
  exact (causalPlan_full_observation_blackwell_equiv n τ Qs).1

/-- Literal execution therefore has zero directed deficiency on an arbitrary
nonempty world class. -/
theorem finiteDeficiency_causalScheduled_plan_eq_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    [Nonempty Θ] [Nonempty O]
    (ρ : I → CausalPolicy A O) (hρ : ∀ i, IsCausalPolicy (ρ i))
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (k : I)
    (hk : ρ k = causalPolicyOfPlan n τ) :
    finiteDeficiency (causalScheduledEpisodicExperiment ρ Qs n)
      (causalPlanObservationExperiment n τ Qs) = 0 := by
  let E := causalScheduledEpisodicExperiment ρ Qs n
  let F := causalPlanObservationExperiment n τ Qs
  have hFE : FiniteBlackwellLE F E :=
    causalScheduled_plan_blackwell ρ hρ Qs hQ τ k hk
  obtain ⟨G, hG, heq⟩ := hFE
  apply le_antisymm
  · apply finiteDeficiency_le_of_decoder E F G hG 0
    intro θ
    change finiteTV (finiteDecisionLaw E G θ) (F θ) ≤ 0
    rw [congrFun heq θ]
    simp [finiteTV]
  · exact finiteDeficiency_nonneg_of_valid E F
      (causalScheduledEpisodicExperiment_valid ρ hρ Qs hQ n)
      (causalPlanObservationExperiment_valid n τ Qs hQ)

end

end IdExp
