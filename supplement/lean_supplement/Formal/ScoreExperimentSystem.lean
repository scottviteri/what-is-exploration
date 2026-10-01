import Formal.FinitaryObjectiveCore
import Formal.GenericStrictnessTransfer
import Mathlib.Data.ENNReal.Real

/-!
# Finite-record score criteria for process strictness

Exact processing, directed simulation error, and score continuity through
approximate decoders. The positive-cost assumption fixes a target before
quantifying over all larger source records. It is a sufficient design
criterion, not a necessary condition on every objective.
-/
namespace IdExp
open Set
open scoped ENNReal
noncomputable section

/-- Local decoder approximation follows from same-output score continuity.
Its tolerance can depend on the fixed target's signal alphabet. -/
structure ScoreExperimentSystem (X : Type*) where
  deficiency : X → X → ℝ
  score : X → ℝ
  exact : X → X → Prop
  score_nonneg : ∀ E, 0 ≤ score E
  score_exact_le : ∀ {E F}, exact E F → score F ≤ score E
  deficiency_nonneg : ∀ E F, 0 ≤ deficiency E F
  deficiency_triangle : ∀ E F T, deficiency E T ≤ deficiency E F + deficiency F T
  deficiency_exact_zero : ∀ {E F}, exact E F → deficiency E F = 0
  approximation : ∀ F η, 0 < η → ∀ r, 0 < r → ∃ δ, 0 < δ ∧
    ∀ E, deficiency E F < δ → ∃ H, exact E H ∧
      deficiency F H < r ∧ |score H - score F| < η

namespace ScoreExperimentSystem
variable {X P : Type*} (M : ScoreExperimentSystem X) (K : P → ℕ → X)

def Refines : Prop := ∀ π m n, m ≤ n → M.exact (K π n) (K π m)
def Dominates (π ρ : P) : Prop := FinitaryDominates K M.deficiency π ρ

/-- Positive fixed-target loss, uniform over the source and its garbling. -/
def HasFixedTargetCost : Prop :=
  ∀ π n ε, 0 < ε → ∃ η, 0 < η ∧ ∀ E H,
    M.exact E (K π n) → M.exact E H → ε ≤ M.deficiency H (K π n) →
      η ≤ M.score E - M.score H

/-- A weaker sufficient condition: source-uniform cost is only required below
each fixed score ceiling. The ceiling includes the complete supremum itself. -/
def HasBoundedFixedTargetCost : Prop :=
  ∀ π n C ε, 0 < ε → ∃ η, 0 < η ∧ ∀ E H,
    M.score E ≤ C → M.exact E (K π n) → M.exact E H →
      ε ≤ M.deficiency H (K π n) → η ≤ M.score E - M.score H

theorem HasFixedTargetCost.bounded (hc : M.HasFixedTargetCost K) :
    M.HasBoundedFixedTargetCost K := by
  intro π n _C ε hε
  obtain ⟨η, hη, hh⟩ := hc π n ε hε
  exact ⟨η, hη, fun E H _ he hg hd => hh E H he hg hd⟩

def ScoreBounded (π : P) : Prop := BddAbove (range (fun n => M.score (K π n)))
/-- The real supremum is used only with a boundedness hypothesis. -/
def completeScore (π : P) : ℝ := ⨆ n, M.score (K π n)
/-- The actual score retains possible infinite saturation. -/
def totalScore (π : P) : ℝ≥0∞ := ⨆ n, ENNReal.ofReal (M.score (K π n))

theorem deficiency_source_antitone (hK : M.Refines K) (π : P) (T : X) :
    Antitone (fun t => M.deficiency (K π t) T) := by
  intro m n hmn
  have h := M.deficiency_triangle (K π n) (K π m) T
  rw [M.deficiency_exact_zero (hK π m n hmn), zero_add] at h
  exact h

theorem dominates_iff_arbitrarily (hK : M.Refines K) (π ρ : P) :
    M.Dominates K π ρ ↔ ∀ n ε, 0 < ε → ∃ t, M.deficiency (K π t) (K ρ n) < ε := by
  constructor
  · intro h n ε hε
    obtain ⟨t, ht⟩ := h n ε hε
    exact ⟨t, ht t le_rfl⟩
  · intro h n ε hε
    obtain ⟨t, ht⟩ := h n ε hε
    exact ⟨t, fun s hs => (M.deficiency_source_antitone K hK π (K ρ n) hs).trans_lt ht⟩

/-- A failed order comparison leaves a fixed finite target out of reach. -/
theorem not_dominates_iff_fixed_gap (hK : M.Refines K) (π ρ : P) :
    ¬ M.Dominates K π ρ ↔ ∃ n ε, 0 < ε ∧ ∀ t, ε ≤ M.deficiency (K π t) (K ρ n) := by
  rw [M.dominates_iff_arbitrarily K hK]
  push Not
  rfl

theorem prefixScore_le_complete (π : P) (hb : M.ScoreBounded K π) (n : ℕ) :
    M.score (K π n) ≤ M.completeScore K π := le_ciSup hb n

theorem completeScore_nonneg (π : P) (hb : M.ScoreBounded K π) :
    0 ≤ M.completeScore K π :=
  (M.score_nonneg (K π 0)).trans (M.prefixScore_le_complete K π hb 0)

/-- Continuity and data processing suffice for weak order preservation. -/
theorem prefixScore_le_of_dominates {π ρ : P}
    (hb : M.ScoreBounded K π) (h : M.Dominates K π ρ) (n : ℕ) :
    M.score (K ρ n) ≤ M.completeScore K π := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨δ, hδ, ha⟩ := M.approximation (K ρ n) η hη 1 zero_lt_one
  obtain ⟨t, ht⟩ := h n δ hδ
  obtain ⟨H, he, _, hs⟩ := ha (K π t) (ht t le_rfl)
  have hlo := (abs_lt.mp hs).1
  have hd := M.score_exact_le he
  have hu := M.prefixScore_le_complete K π hb t
  linarith

theorem scoreBounded_of_dominates {π ρ : P}
    (hb : M.ScoreBounded K π) (h : M.Dominates K π ρ) : M.ScoreBounded K ρ :=
  ⟨M.completeScore K π, by
    rintro _ ⟨n, rfl⟩
    exact M.prefixScore_le_of_dominates K hb h n⟩

theorem completeScore_mono {π ρ : P}
    (hb : M.ScoreBounded K π) (h : M.Dominates K π ρ) :
    M.completeScore K ρ ≤ M.completeScore K π :=
  ciSup_le (fun n => M.prefixScore_le_of_dominates K hb h n)

/-- The gap depends on a fixed missing target, not on the growing weak record. -/
theorem completeScore_strict_of_bounded_cost (hK : M.Refines K) (hc : M.HasBoundedFixedTargetCost K)
    {π ρ : P} (hb : M.ScoreBounded K π) (h : M.Dominates K π ρ)
    (hn : ¬ M.Dominates K ρ π) : M.completeScore K ρ < M.completeScore K π := by
  obtain ⟨n, ε, hε, hgap⟩ := (M.not_dominates_iff_fixed_gap K hK ρ π).mp hn
  obtain ⟨η, hη, hcost⟩ := hc π n (M.completeScore K π) (ε / 2) (half_pos hε)
  have hupper : ∀ m, M.score (K ρ m) ≤ M.completeScore K π - η / 2 := by
    intro m
    obtain ⟨δ, hδ, ha⟩ := M.approximation (K ρ m) (η / 2) (half_pos hη)
      (ε / 2) (half_pos hε)
    obtain ⟨t, ht⟩ := h m δ hδ
    let s := max n t
    obtain ⟨H, he, hd, hs⟩ := ha (K π s) (ht s (le_max_right _ _))
    have htri := M.deficiency_triangle (K ρ m) H (K π n)
    have hlow : ε / 2 ≤ M.deficiency H (K π n) := by
      have hh := hgap m
      linarith
    have hcst := hcost (K π s) H (M.prefixScore_le_complete K π hb s) (hK π n s (le_max_left _ _)) he hlow
    have hclose := (abs_lt.mp hs).1
    have hbound := M.prefixScore_le_complete K π hb s
    linarith
  have hs : M.completeScore K ρ ≤ M.completeScore K π - η / 2 := ciSup_le hupper
  linarith

/-- The source-independent fixed-cost condition is a sufficient special case. -/
theorem completeScore_strict (hK : M.Refines K) (hc : M.HasFixedTargetCost K)
    {π ρ : P} (hb : M.ScoreBounded K π) (h : M.Dominates K π ρ)
    (hn : ¬ M.Dominates K ρ π) : M.completeScore K ρ < M.completeScore K π :=
  M.completeScore_strict_of_bounded_cost K hK (hc.bounded M K) hb h hn

/-- Equality at finite total is exactly reverse finitary simulation. -/
theorem completeScore_eq_iff_reverse (hK : M.Refines K) (hc : M.HasFixedTargetCost K)
    {π ρ : P} (hb : M.ScoreBounded K π) (h : M.Dominates K π ρ) :
    M.completeScore K π = M.completeScore K ρ ↔ M.Dominates K ρ π := by
  constructor
  · intro he
    by_contra hn
    have hlt := M.completeScore_strict K hK hc hb h hn
    rw [he] at hlt
    exact (lt_irrefl _) hlt
  · intro hr
    exact le_antisymm
      (M.completeScore_mono K (M.scoreBounded_of_dominates K hb h) hr)
      (M.completeScore_mono K hb h)

/-- The stronger conclusion needs cost uniformity only below a fixed score ceiling. -/
theorem completeScore_eq_iff_reverse_of_bounded_cost (hK : M.Refines K) (hc : M.HasBoundedFixedTargetCost K)
    {π ρ : P} (hb : M.ScoreBounded K π) (h : M.Dominates K π ρ) :
    M.completeScore K π = M.completeScore K ρ ↔ M.Dominates K ρ π := by
  constructor
  · intro he
    by_contra hn
    have hlt := M.completeScore_strict_of_bounded_cost K hK hc hb h hn
    rw [he] at hlt
    exact (lt_irrefl _) hlt
  · intro hr
    exact le_antisymm
      (M.completeScore_mono K (M.scoreBounded_of_dominates K hb h) hr)
      (M.completeScore_mono K hb h)

theorem completeScore_strictlyFinitaryMonotone (hK : M.Refines K)
    (hc : M.HasFixedTargetCost K) (hb : ∀ π, M.ScoreBounded K π) :
    IsStrictlyFinitaryMonotone K M.deficiency (M.completeScore K) :=
  ⟨fun π _ρ h => M.completeScore_mono K (hb π) h,
   fun π _ρ h hn => M.completeScore_strict K hK hc (hb π) h hn⟩

theorem scoreBounded_iff_totalScore_ne_top (π : P) :
    M.ScoreBounded K π ↔ M.totalScore K π ≠ ⊤ := by
  constructor
  · intro hb
    have hu : M.totalScore K π ≤ ENNReal.ofReal (M.completeScore K π) :=
      iSup_le (fun n => ENNReal.ofReal_le_ofReal (M.prefixScore_le_complete K π hb n))
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  · intro hn
    refine ⟨(M.totalScore K π).toReal, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (ENNReal.ofReal_le_iff_le_toReal hn).mp
      (le_iSup (fun n => ENNReal.ofReal (M.score (K π n))) n)

theorem totalScore_toReal (π : P) : (M.totalScore K π).toReal = M.completeScore K π := by
  unfold totalScore completeScore
  rw [ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (M.score_nonneg _)]

theorem totalScore_eq_ofReal_complete (π : P) (hb : M.ScoreBounded K π) :
    M.totalScore K π = ENNReal.ofReal (M.completeScore K π) := by
  rw [← M.totalScore_toReal K π]
  exact (ENNReal.ofReal_toReal ((M.scoreBounded_iff_totalScore_ne_top K π).mp hb)).symm

theorem totalScore_mono {π ρ : P} (h : M.Dominates K π ρ) :
    M.totalScore K ρ ≤ M.totalScore K π := by
  by_cases hn : M.totalScore K π = ⊤
  · simp [hn]
  have hb := (M.scoreBounded_iff_totalScore_ne_top K π).mpr hn
  have hbρ := M.scoreBounded_of_dominates K hb h
  rw [M.totalScore_eq_ofReal_complete K π hb, M.totalScore_eq_ofReal_complete K ρ hbρ]
  exact ENNReal.ofReal_le_ofReal (M.completeScore_mono K hb h)

theorem totalScore_eq_iff_reverse (hK : M.Refines K) (hc : M.HasFixedTargetCost K)
    {π ρ : P} (hb : M.totalScore K π ≠ ⊤) (h : M.Dominates K π ρ) :
    M.totalScore K π = M.totalScore K ρ ↔ M.Dominates K ρ π := by
  constructor
  · intro he
    have he' := congrArg ENNReal.toReal he
    rw [M.totalScore_toReal, M.totalScore_toReal] at he'
    exact (M.completeScore_eq_iff_reverse K hK hc
      ((M.scoreBounded_iff_totalScore_ne_top K π).mpr hb) h).mp he'
  · intro hr
    exact le_antisymm (M.totalScore_mono K hr) (M.totalScore_mono K h)

/-- The stronger conclusion needs cost uniformity only below a fixed score ceiling. -/
theorem totalScore_eq_iff_reverse_of_bounded_cost (hK : M.Refines K) (hc : M.HasBoundedFixedTargetCost K)
    {π ρ : P} (hb : M.totalScore K π ≠ ⊤) (h : M.Dominates K π ρ) :
    M.totalScore K π = M.totalScore K ρ ↔ M.Dominates K ρ π := by
  constructor
  · intro he
    have he' := congrArg ENNReal.toReal he
    rw [M.totalScore_toReal, M.totalScore_toReal] at he'
    exact (M.completeScore_eq_iff_reverse_of_bounded_cost K hK hc
      ((M.scoreBounded_iff_totalScore_ne_top K π).mpr hb) h).mp he'
  · intro hr
    exact le_antisymm (M.totalScore_mono K hr) (M.totalScore_mono K h)

/-- Exact obstruction criterion for any stronger desired comparison. -/
theorem totalScore_strictness_iff (hK : M.Refines K) (hc : M.HasFixedTargetCost K)
    (U : P → P → Prop) (hUD : ∀ π ρ, U π ρ → M.Dominates K π ρ) :
    StrictlyMonotoneFor U (M.totalScore K) ↔
      ReverseDominanceLifts U (M.Dominates K) ∧ NoInfiniteStrictPairFor U (M.totalScore K) :=
  strictlyMonotoneFor_iff_reverseLifts_and_noInfiniteStrictPair U (M.Dominates K)
    (M.totalScore K) hUD (fun _ _ h => M.totalScore_mono K h)
    (fun _ _ hb h => M.totalScore_eq_iff_reverse K hK hc hb h)

/-- The stronger conclusion needs cost uniformity only below a fixed score ceiling. -/
theorem totalScore_strictness_iff_of_bounded_cost (hK : M.Refines K) (hc : M.HasBoundedFixedTargetCost K)
    (U : P → P → Prop) (hUD : ∀ π ρ, U π ρ → M.Dominates K π ρ) :
    StrictlyMonotoneFor U (M.totalScore K) ↔
      ReverseDominanceLifts U (M.Dominates K) ∧ NoInfiniteStrictPairFor U (M.totalScore K) :=
  strictlyMonotoneFor_iff_reverseLifts_and_noInfiniteStrictPair U (M.Dominates K)
    (M.totalScore K) hUD (fun _ _ h => M.totalScore_mono K h)
    (fun _ _ hb h => M.totalScore_eq_iff_reverse_of_bounded_cost K hK hc hb h)

/-- Finite totals leave only a mismatch between the two comparison criteria. -/
theorem totalScore_strictness_iff_of_finite (hK : M.Refines K)
    (hc : M.HasFixedTargetCost K) (hb : ∀ π, M.ScoreBounded K π)
    (U : P → P → Prop) (hUD : ∀ π ρ, U π ρ → M.Dominates K π ρ) :
    StrictlyMonotoneFor U (M.totalScore K) ↔ ReverseDominanceLifts U (M.Dominates K) :=
  strictlyMonotoneFor_iff_reverseLifts_of_finite U (M.Dominates K) (M.totalScore K)
    hUD (fun _ _ h => M.totalScore_mono K h)
    (fun _ _ hf h => M.totalScore_eq_iff_reverse K hK hc hf h)
    (fun π => (M.scoreBounded_iff_totalScore_ne_top K π).mp (hb π))

/-- The stronger conclusion needs cost uniformity only below a fixed score ceiling. -/
theorem totalScore_strictness_iff_of_finite_of_bounded_cost (hK : M.Refines K)
    (hc : M.HasBoundedFixedTargetCost K) (hb : ∀ π, M.ScoreBounded K π)
    (U : P → P → Prop) (hUD : ∀ π ρ, U π ρ → M.Dominates K π ρ) :
    StrictlyMonotoneFor U (M.totalScore K) ↔ ReverseDominanceLifts U (M.Dominates K) :=
  strictlyMonotoneFor_iff_reverseLifts_of_finite U (M.Dominates K) (M.totalScore K)
    hUD (fun _ _ h => M.totalScore_mono K h)
    (fun _ _ hf h => M.totalScore_eq_iff_reverse_of_bounded_cost K hK hc hf h)
    (fun π => (M.scoreBounded_iff_totalScore_ne_top K π).mp (hb π))

end ScoreExperimentSystem
end
end IdExp
