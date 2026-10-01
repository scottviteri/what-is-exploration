import Mathlib

/-!
# Three irreversible doors: maximality is not adequacy

For a root-mixture policy with probabilities summing to one and positive
capability scales, this file checks the elementary order-theoretic core:
coordinatewise profile dominance forces equality, no mixture attains the zero
profile, and LEFT can be rho-approximately above DARK although the two exact
profiles are incomparable. It also checks that coverage probabilities `(1,1,1)`
from three fresh episodes give the zero algebraic profile; this is a different
protocol from one irreversible run. `ThreeDoorValues.lean` identifies these
coordinates with actual Le Cam deficiencies, and `ThreeDoorCausal.lean` proves
the literal all-depth causal profiles and infinite-history nonidentification.
-/

namespace IdExp

/-- Three-coordinate deficiency profile of an irreversible root mixture. -/
def threeDoorProfile (rL rR rD wL wR wD : ℝ) : Fin 3 → ℝ
  | 0 => rL * (1 - wL)
  | 1 => rR * (1 - wR)
  | 2 => rD * (1 - wD)

/-- Positive scales and a fixed probability budget make the profiles an antichain. -/
theorem threeDoorProfile_antichain
    {rL rR rD wL wR wD vL vR vD : ℝ}
    (hrL : 0 < rL) (hrR : 0 < rR) (hrD : 0 < rD)
    (hw : wL + wR + wD = 1) (hv : vL + vR + vD = 1)
    (hdom : ∀ i, threeDoorProfile rL rR rD vL vR vD i ≤
      threeDoorProfile rL rR rD wL wR wD i) :
    vL = wL ∧ vR = wR ∧ vD = wD := by
  have hL := hdom 0
  have hR := hdom 1
  have hD := hdom 2
  simp [threeDoorProfile] at hL hR hD
  have hLv : wL ≤ vL := by nlinarith
  have hRv : wR ≤ vR := by nlinarith
  have hDv : wD ≤ vD := by nlinarith
  constructor
  · linarith
  constructor <;> linarith

/-- A probability mixture cannot attain all three positive capabilities at once. -/
theorem threeDoorProfile_ne_zero
    {rL rR rD wL wR wD : ℝ}
    (hrL : 0 < rL) (hrR : 0 < rR) (hrD : 0 < rD)
    (hw : wL + wR + wD = 1) :
    threeDoorProfile rL rR rD wL wR wD ≠ 0 := by
  intro hzero
  have hL : rL * (1 - wL) = 0 := by
    have h := congrFun hzero 0
    simpa [threeDoorProfile] using h
  have hR : rR * (1 - wR) = 0 := by
    have h := congrFun hzero 1
    simpa [threeDoorProfile] using h
  have hD : rD * (1 - wD) = 0 := by
    have h := congrFun hzero 2
    simpa [threeDoorProfile] using h
  have hwL : wL = 1 := by nlinarith
  have hwR : wR = 1 := by nlinarith
  have hwD : wD = 1 := by nlinarith
  linarith

/-- With a reset/fresh copy, taking each door once gives access probability one in every
coordinate and hence the zero batch profile.  The three `1`s are coverage probabilities across
three episodes, not a one-episode mixture (so no unit-sum hypothesis is intended). -/
theorem threeDoor_three_fresh_episodes_zero (rL rR rD : ℝ) :
    threeDoorProfile rL rR rD 1 1 1 = 0 := by
  funext i
  fin_cases i <;> simp [threeDoorProfile]

/-- LEFT is coordinatewise within epsilon of DARK once epsilon covers rho. -/
theorem left_approximately_dominates_dark {ρ ε : ℝ}
    (hρ : 0 ≤ ρ) (hρε : ρ ≤ ε) :
    ∀ i, threeDoorProfile (1 / 2) (1 / 2) ρ 1 0 0 i ≤
      threeDoorProfile (1 / 2) (1 / 2) ρ 0 0 1 i + ε := by
  intro i
  fin_cases i <;> simp [threeDoorProfile] <;> linarith

/-- The exact tolerance threshold for LEFT to approximately dominate DARK. -/
theorem left_approximately_dominates_dark_iff {ρ ε : ℝ} (hρ : 0 ≤ ρ) :
    (∀ i, threeDoorProfile (1 / 2) (1 / 2) ρ 1 0 0 i ≤
      threeDoorProfile (1 / 2) (1 / 2) ρ 0 0 1 i + ε) ↔ ρ ≤ ε := by
  constructor
  · intro h
    have hD := h 2
    simpa [threeDoorProfile] using hD
  · exact left_approximately_dominates_dark hρ
/-- Below tolerance one half, DARK cannot approximately dominate LEFT. -/
theorem dark_not_approximately_dominates_left {ρ ε : ℝ} (hε : ε < 1 / 2) :
    ¬ ∀ i, threeDoorProfile (1 / 2) (1 / 2) ρ 0 0 1 i ≤
      threeDoorProfile (1 / 2) (1 / 2) ρ 1 0 0 i + ε := by
  intro h
  have hL := h 0
  simp [threeDoorProfile] at hL
  linarith

/-- The exact tolerance threshold for DARK to approximately dominate LEFT. -/
theorem dark_approximately_dominates_left_iff {ρ ε : ℝ} (hρ : 0 ≤ ρ) :
    (∀ i, threeDoorProfile (1 / 2) (1 / 2) ρ 0 0 1 i ≤
      threeDoorProfile (1 / 2) (1 / 2) ρ 1 0 0 i + ε) ↔ 1 / 2 ≤ ε := by
  constructor
  · intro h
    have hL := h 0
    simpa [threeDoorProfile] using hL
  · intro hε i
    fin_cases i <;> simp [threeDoorProfile] <;> linarith

/-- At every positive dark scale, pure LEFT and DARK each win one coordinate. -/
theorem left_dark_profiles_incomparable {ρ : ℝ} (hρ : 0 < ρ) :
    (threeDoorProfile (1 / 2) (1 / 2) ρ 1 0 0 0 <
      threeDoorProfile (1 / 2) (1 / 2) ρ 0 0 1 0) ∧
    (threeDoorProfile (1 / 2) (1 / 2) ρ 0 0 1 2 <
      threeDoorProfile (1 / 2) (1 / 2) ρ 1 0 0 2) := by
  simpa [threeDoorProfile] using hρ

end IdExp
