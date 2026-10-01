import Formal.FiniteTV
import Formal.FiniteProbability

/-!
# The unrestricted causal-class obstruction

**Relevance:** direct current-paper support for `prop:unrestricted`.

This file encodes the finite root-branch subclass used in the proof.  A world is a bit vector
`A → Bool`; the acquired experiment samples a root action with probabilities `p` (recording that
action) and reveals only its bit.  The native root-`a` experiment reveals bit `a`.  Lean checks:

* both experiment matrices are stochastic;
* worlds differing only at `a` have acquired total variation exactly `p a` and target total
  variation exactly one;
* every decoder for root test `a` has error at least `(1 - p a)/2` on that pair; and
* some action has `p a ≤ 1 / |A|`, giving the paper's bound
  `(1/2) (1 - 1/|A|)`.

`UnrestrictedCausal.lean` supplies the causal embedding and all-horizon
wrapper: every later observation is deterministic, the full acquired trace
factors through this root experiment by an explicit world-independent
stochastic rule, and the same sharp bound holds at every horizon.
`UnrestrictedClass.lean` gives the full arbitrary-alphabet paper theorem,
including the deficiency infimum and exclusion of zero from the actual
causal-policy profile closure.
-/

set_option linter.unusedSectionVars false

namespace IdExp

open Finset

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- Acquired root history: sample action `a ~ p`, record it, and observe the world's bit `θ a`. -/
noncomputable def rootAcquired (p : A → ℝ) : FiniteExperiment (A → Bool) (A × Bool) :=
  fun θ ao => if ao.2 = θ ao.1 then p ao.1 else 0

/-- Native root-`a` intervention. -/
noncomputable def rootTest (a : A) : FiniteExperiment (A → Bool) Bool :=
  fun θ o => if o = θ a then 1 else 0

def zeroWorld : A → Bool := fun _ => false

/-- The world differing from `zeroWorld` only at action `a`. -/
def flipWorld (a : A) : A → Bool := fun x => decide (x = a)

theorem rootAcquired_valid (p : A → ℝ) (hp : IsDist p) :
    IsFiniteExperiment (rootAcquired p) := by
  intro θ
  constructor
  · intro ao
    by_cases h : ao.2 = θ ao.1
    · simp [rootAcquired, h, hp.1]
    · simp [rootAcquired, h]
  · rw [Fintype.sum_prod_type]
    have hbool : ∀ a, ∑ o : Bool, (if o = θ a then p a else 0) = p a := by
      intro a
      cases h : θ a <;> simp [h]
    simp only [rootAcquired]
    simp_rw [hbool]
    exact hp.2

theorem rootTest_valid (a : A) : IsFiniteExperiment (rootTest a) := by
  intro θ
  constructor
  · intro o
    by_cases h : o = θ a <;> simp [rootTest, h]
  · cases h : θ a <;> simp [rootTest, h]

/-- The sampled root history separates the selected bit-pair only on the event that action `a`
was selected. -/
theorem rootAcquired_pair_tv (p : A → ℝ) (hp : IsDist p) (a : A) :
    finiteTV (rootAcquired p zeroWorld) (rootAcquired p (flipWorld a)) = p a := by
  unfold finiteTV rootAcquired zeroWorld flipWorld
  rw [Fintype.sum_prod_type]
  have hrow : ∀ x : A,
      ∑ o : Bool, |(if o = false then p x else 0) -
        (if o = decide (x = a) then p x else 0)| =
        if x = a then 2 * p x else 0 := by
    intro x
    by_cases hx : x = a
    · subst x
      rw [Fintype.sum_bool]
      simp [abs_of_nonneg (hp.1 a)]
      ring
    · simp [hx]
  simp_rw [hrow]
  simp

/-- The native root test perfectly separates the same pair. -/
theorem rootTest_pair_tv (a : A) :
    finiteTV (rootTest a zeroWorld) (rootTest a (flipWorld a)) = 1 := by
  unfold finiteTV rootTest zeroWorld flipWorld
  norm_num

/-- A probability vector on a nonempty finite action space has a coordinate no larger than the
uniform mass. -/
theorem exists_action_le_inv_card (p : A → ℝ) (hp : IsDist p) :
    ∃ a, p a ≤ (Fintype.card A : ℝ)⁻¹ := by
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_sum_le (s := (Finset.univ : Finset A))
    Finset.univ_nonempty (f := p) (g := fun _ => (Fintype.card A : ℝ)⁻¹) (by
      rw [hp.2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
      exact le_rfl)
  exact ⟨a, ha⟩

/-- Exact finite-subclass form of the unrestricted-class obstruction: no family of decoders can
simulate every root intervention more accurately than the stated constant. -/
theorem unrestricted_root_decoder_lower (p : A → ℝ) (hp : IsDist p)
    (G : A → (A × Bool) → Bool → ℝ)
    (hG : ∀ a, G a ∈ stochasticRules (A × Bool) Bool) (c : ℝ)
    (herr : ∀ a θ,
      finiteTV (finiteDecisionLaw (rootAcquired p) (G a) θ) (rootTest a θ) ≤ c) :
    (1 / 2) * (1 - (Fintype.card A : ℝ)⁻¹) ≤ c := by
  obtain ⟨a, ha⟩ := exists_action_le_inv_card p hp
  have hpair := finiteTV_pairwise_decoder_lower (rootAcquired p) (rootTest a) (G a)
    (hG a) zeroWorld (flipWorld a) c (herr a zeroWorld) (herr a (flipWorld a))
  rw [rootTest_pair_tv a, rootAcquired_pair_tv p hp a] at hpair
  nlinarith

end IdExp
