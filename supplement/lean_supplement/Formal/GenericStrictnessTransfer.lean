import Mathlib.Data.ENNReal.Basic

/-!
# Strict-score transfer between two comparisons

This order-only theorem isolates two exact obstructions. A score may identify
objects equivalent for a weaker comparison, or may assign infinity to both
members of a strict pair. A finite-score equality theorem for the weaker
comparison makes these the only obstructions to strictness for the desired one.
No preorder laws are needed by the transfer argument itself.
-/
namespace IdExp
open scoped ENNReal

variable {P : Type*}

/-- Both weak preservation and strict preservation of one-sided comparisons.
The first argument of `R` is the better object. -/
def StrictlyMonotoneFor (R : P → P → Prop) (J : P → ℝ≥0∞) : Prop :=
  (∀ π ρ, R π ρ → J ρ ≤ J π) ∧
  (∀ π ρ, R π ρ → ¬ R ρ π → J ρ < J π)

/-- On comparable pairs, reverse weak comparison lifts to reverse desired
comparison. -/
def ReverseDominanceLifts (U D : P → P → Prop) : Prop :=
  ∀ π ρ, U π ρ → D ρ π → U ρ π

/-- Infinite score ties are excluded only on strict pairs. -/
def NoInfiniteStrictPairFor (U : P → P → Prop) (J : P → ℝ≥0∞) : Prop :=
  ∀ π ρ, U π ρ → ¬ U ρ π → ¬ (J π = ⊤ ∧ J ρ = ⊤)

/-- Exact strictness transfer. The substantive analytic premise is the finite
score equality/reverse-comparison theorem; the transfer itself is independent of
experiments, priors, objectives, and process representations. -/
theorem strictlyMonotoneFor_iff_reverseLifts_and_noInfiniteStrictPair
    (U D : P → P → Prop) (J : P → ℝ≥0∞)
    (hUD : ∀ π ρ, U π ρ → D π ρ)
    (hmonoD : ∀ π ρ, D π ρ → J ρ ≤ J π)
    (hfiniteEq : ∀ π ρ, J π ≠ ⊤ → D π ρ → (J π = J ρ ↔ D ρ π)) :
    StrictlyMonotoneFor U J ↔
      ReverseDominanceLifts U D ∧ NoInfiniteStrictPairFor U J := by
  constructor
  · intro hJ
    constructor
    · intro π ρ hu hd
      by_contra hn
      exact (not_lt_of_ge (hmonoD ρ π hd)) (hJ.2 π ρ hu hn)
    · intro π ρ hu hn he
      have hlt := hJ.2 π ρ hu hn
      rw [he.1, he.2] at hlt
      exact (lt_irrefl _) hlt
  · rintro ⟨hU, hS⟩
    refine ⟨fun π ρ hu => hmonoD π ρ (hUD π ρ hu), ?_⟩
    intro π ρ hu hn
    apply lt_of_le_of_ne (hmonoD π ρ (hUD π ρ hu))
    intro he
    by_cases htop : J π = ⊤
    · exact hS π ρ hu hn ⟨htop, he.trans htop⟩
    exact hn (hU π ρ hu ((hfiniteEq π ρ htop (hUD π ρ hu)).mp he.symm))

/-- If all totals are finite, reverse lifting is the only remaining obstruction. -/
theorem strictlyMonotoneFor_iff_reverseLifts_of_finite
    (U D : P → P → Prop) (J : P → ℝ≥0∞)
    (hUD : ∀ π ρ, U π ρ → D π ρ)
    (hmonoD : ∀ π ρ, D π ρ → J ρ ≤ J π)
    (hfiniteEq : ∀ π ρ, J π ≠ ⊤ → D π ρ → (J π = J ρ ↔ D ρ π))
    (hfinite : ∀ π, J π ≠ ⊤) :
    StrictlyMonotoneFor U J ↔ ReverseDominanceLifts U D := by
  rw [strictlyMonotoneFor_iff_reverseLifts_and_noInfiniteStrictPair U D J hUD hmonoD hfiniteEq]
  exact and_iff_left (fun π ρ _ _ h => hfinite π h.1)

/-- When the two comparisons agree, only infinity ties can obstruct strictness. -/
theorem strictlyMonotoneFor_self_iff_noInfiniteStrictPair
    (D : P → P → Prop) (J : P → ℝ≥0∞)
    (hmonoD : ∀ π ρ, D π ρ → J ρ ≤ J π)
    (hfiniteEq : ∀ π ρ, J π ≠ ⊤ → D π ρ → (J π = J ρ ↔ D ρ π)) :
    StrictlyMonotoneFor D J ↔ NoInfiniteStrictPairFor D J := by
  rw [strictlyMonotoneFor_iff_reverseLifts_and_noInfiniteStrictPair D D J
    (fun _ _ h => h) hmonoD hfiniteEq]
  exact and_iff_right (fun _ _ _ h => h)

end IdExp
