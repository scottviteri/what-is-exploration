import Formal.DualCertificate
import Formal.ThreeDoors

/-!
# Actual finite deficiencies for irreversible noisy doors

A world is a binary vector. Choosing action `a` reveals only its coordinate
through a binary channel of strength `r a`; the root action is part of the
acquired signal. This file proves the exact decoder-infimum deficiency
`r a * (1 - w a)`, not merely the algebra of an asserted profile.

The upper decoder re-emits the observation if the requested branch was
chosen, and otherwise emits a fair bit. Worlds differing only in the
requested coordinate give the matching TV lower bound. The calculation is
generic over finite action alphabets and strengths in `[0, 1/2]`.
`threeDoorScales ρ` specializes it to LEFT, RIGHT, and DARK. Absorbing causal
histories and terminal experiments are a separate wrapper.
-/

namespace IdExp

open Finset Set

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The native root test, with probability `1/2 + r a` of the world's bit.
At strength one half this reveals that bit exactly. -/
def threeDoorRootTest (r : A → ℝ) (a : A) : FiniteExperiment (A → Fin 2) (Fin 2) :=
  fun θ o => if o = θ a then 1 / 2 + r a else 1 / 2 - r a

omit [Fintype A] [DecidableEq A] in
theorem threeDoorRootTest_sum (r : A → ℝ) (a : A) (θ : A → Fin 2) :
    ∑ o, threeDoorRootTest r a θ o = 1 := by
  generalize h : θ a = b
  fin_cases b <;> simp [threeDoorRootTest, h, Fin.sum_univ_succ] <;> ring

omit [Fintype A] [DecidableEq A] in
theorem threeDoorRootTest_valid (r : A → ℝ)
    (hr0 : ∀ a, 0 ≤ r a) (hrhalf : ∀ a, r a ≤ 1 / 2) (a : A) :
    IsFiniteExperiment (threeDoorRootTest r a) := by
  intro θ
  refine ⟨?_, threeDoorRootTest_sum r a θ⟩
  intro o
  unfold threeDoorRootTest
  split_ifs <;> linarith [hr0 a, hrhalf a]

/-- Choose a root action according to `w`, recording it together with its
single noisy observation. -/
def threeDoorRootExperiment (w r : A → ℝ) :
    FiniteExperiment (A → Fin 2) (A × Fin 2) :=
  fun θ ao => w ao.1 * threeDoorRootTest r ao.1 θ ao.2

omit [DecidableEq A] in
theorem threeDoorRootExperiment_valid (w r : A → ℝ) (hw : IsDist w)
    (hr0 : ∀ a, 0 ≤ r a) (hrhalf : ∀ a, r a ≤ 1 / 2) :
    IsFiniteExperiment (threeDoorRootExperiment w r) := by
  intro θ
  constructor
  · intro ao
    exact mul_nonneg (hw.1 ao.1) ((threeDoorRootTest_valid r hr0 hrhalf ao.1 θ).1 ao.2)
  · simp only [threeDoorRootExperiment, Fintype.sum_prod_type, ← Finset.mul_sum,
      threeDoorRootTest_sum, mul_one]
    exact hw.2

/-- Simulation, not world identification: keep the observed bit on the
requested branch and use the minimax fair bit on every other branch. -/
def threeDoorRootDecoder (a : A) : (A × Fin 2) → Fin 2 → ℝ :=
  fun ao o => if ao.1 = a then (if o = ao.2 then 1 else 0) else 1 / 2

omit [Fintype A] in
theorem threeDoorRootDecoder_valid (a : A) :
    threeDoorRootDecoder a ∈ stochasticRules (A × Fin 2) (Fin 2) := by
  intro ao _
  constructor
  · intro o
    unfold threeDoorRootDecoder
    split_ifs <;> norm_num
  · by_cases h : ao.1 = a
    · simp [threeDoorRootDecoder, h]
    · simp [threeDoorRootDecoder, h]

/-- The explicit decoder's law is the target law with probability `w a`
and the fair midpoint with probability `1 - w a`. -/
theorem threeDoorRootDecoder_law (w r : A → ℝ) (hw : IsDist w)
    (a : A) (θ : A → Fin 2) (o : Fin 2) :
    finiteDecisionLaw (threeDoorRootExperiment w r) (threeDoorRootDecoder a) θ o =
      w a * threeDoorRootTest r a θ o + (1 - w a) / 2 := by
  unfold finiteDecisionLaw threeDoorRootExperiment
  rw [Fintype.sum_prod_type]
  have hrow (b : A) :
      ∑ y, w b * threeDoorRootTest r b θ y * threeDoorRootDecoder a (b, y) o =
        w b / 2 + if b = a then w b * (threeDoorRootTest r b θ o - 1 / 2) else 0 := by
    by_cases hb : b = a
    · subst b
      simp [threeDoorRootDecoder]
      ring
    · simp only [threeDoorRootDecoder, hb, if_false, add_zero]
      rw [← Finset.sum_mul, ← Finset.mul_sum, threeDoorRootTest_sum]
      ring
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.sum_div, hw.2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The explicit simulation error is exactly the unobserved-branch mass
times that branch's channel strength, in every world. -/
theorem threeDoorRootDecoder_error (w r : A → ℝ) (hw : IsDist w)
    (hr0 : ∀ a, 0 ≤ r a) (a : A) (θ : A → Fin 2) :
    decodeErr (threeDoorRootExperiment w r) (threeDoorRootTest r a)
      (threeDoorRootDecoder a) θ = r a * (1 - w a) := by
  have hwa : w a ≤ 1 := by
    rw [← hw.2]
    exact Finset.single_le_sum (fun b _ => hw.1 b) (Finset.mem_univ a)
  have hc : 0 ≤ r a * (1 - w a) := mul_nonneg (hr0 a) (sub_nonneg.2 hwa)
  have hdiff (o : Fin 2) :
      finiteDecisionLaw (threeDoorRootExperiment w r) (threeDoorRootDecoder a) θ o -
        threeDoorRootTest r a θ o =
      if o = θ a then -(r a * (1 - w a)) else r a * (1 - w a) := by
    rw [threeDoorRootDecoder_law w r hw]
    unfold threeDoorRootTest
    split_ifs <;> ring
  change (1 / 2 : ℝ) * ∑ o,
    |finiteDecisionLaw (threeDoorRootExperiment w r) (threeDoorRootDecoder a) θ o -
      threeDoorRootTest r a θ o| = _
  simp_rw [hdiff, abs_ite, abs_neg, abs_of_nonneg hc, ite_self]
  simp

def threeDoorZeroWorld : A → Fin 2 := fun _ => 0

/-- A pair differing only in the requested coordinate provides the lower
certificate, independently of which decoder is proposed. -/
def threeDoorFlipWorld (a : A) : A → Fin 2 := fun b => if b = a then 1 else 0

omit [Fintype A] in
theorem threeDoorRootTest_pair_tv (r : A → ℝ) (hr0 : ∀ a, 0 ≤ r a) (a : A) :
    finiteTV (threeDoorRootTest r a threeDoorZeroWorld)
      (threeDoorRootTest r a (threeDoorFlipWorld a)) = 2 * r a := by
  simp [finiteTV, threeDoorRootTest, threeDoorZeroWorld, threeDoorFlipWorld,
    Fin.sum_univ_succ]
  rw [abs_of_nonneg (by linarith [hr0 a]), abs_of_nonpos (by linarith [hr0 a])]
  ring

/-- Recording the chosen action preserves precisely `w a` of the pair's
native separation. This also supplies the global-label nonidentification
obstruction used in the causal wrapper. -/
theorem threeDoorRootExperiment_pair_tv (w r : A → ℝ) (hw : IsDist w)
    (hr0 : ∀ a, 0 ≤ r a) (a : A) :
    finiteTV (threeDoorRootExperiment w r threeDoorZeroWorld)
      (threeDoorRootExperiment w r (threeDoorFlipWorld a)) = 2 * r a * w a := by
  unfold finiteTV threeDoorRootExperiment
  rw [Fintype.sum_prod_type]
  have hrow (b : A) :
      ∑ o, |w b * threeDoorRootTest r b threeDoorZeroWorld o -
        w b * threeDoorRootTest r b (threeDoorFlipWorld a) o| =
      if b = a then 4 * r a * w a else 0 := by
    by_cases hb : b = a
    · subst b
      simp_rw [← mul_sub, abs_mul, abs_of_nonneg (hw.1 a)]
      rw [← Finset.mul_sum]
      have ht := threeDoorRootTest_pair_tv r hr0 a
      unfold finiteTV at ht
      have hs : ∑ o, |threeDoorRootTest r a threeDoorZeroWorld o -
          threeDoorRootTest r a (threeDoorFlipWorld a) o| = 4 * r a := by linarith
      rw [hs]
      simp
      ring
    · simp [threeDoorRootTest, threeDoorZeroWorld, threeDoorFlipWorld, hb]
  simp_rw [hrow]
  simp
  ring

/-- **Exact finite Le Cam deficiency for a noisy irreversible door.** Both
the source and target are actual probability experiments under the stated
hypotheses; one explicit decoder and one world-pair certificate coincide. -/
theorem threeDoorRoot_deficiency (w r : A → ℝ) (hw : IsDist w)
    (hr0 : ∀ a, 0 ≤ r a) (hrhalf : ∀ a, r a ≤ 1 / 2) (a : A) :
    finiteDeficiency (threeDoorRootExperiment w r) (threeDoorRootTest r a) =
      r a * (1 - w a) := by
  apply le_antisymm
  · exact finiteDeficiency_le_of_decoder _ _ (threeDoorRootDecoder a)
      (threeDoorRootDecoder_valid a) _
      (fun θ => (threeDoorRootDecoder_error w r hw hr0 a θ).le)
  · apply le_csInf (finiteDeficiencyCandidates_nonempty_of_valid _ _
      (threeDoorRootExperiment_valid w r hw hr0 hrhalf)
      (threeDoorRootTest_valid r hr0 hrhalf a))
    rintro c ⟨G, hG, herr⟩
    have hpair := finiteTV_pairwise_decoder_lower (threeDoorRootExperiment w r)
      (threeDoorRootTest r a) G hG threeDoorZeroWorld (threeDoorFlipWorld a) c
      (herr threeDoorZeroWorld) (herr (threeDoorFlipWorld a))
    rw [threeDoorRootTest_pair_tv r hr0 a,
      threeDoorRootExperiment_pair_tv w r hw hr0 a] at hpair
    nlinarith

/-- LEFT and RIGHT reveal their bits; DARK has strength `ρ`. -/
def threeDoorScales (ρ : ℝ) : Fin 3 → ℝ := ![1 / 2, 1 / 2, ρ]

theorem threeDoorScales_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ a, 0 ≤ threeDoorScales ρ a := by
  intro a
  fin_cases a <;> simp [threeDoorScales, hρ]

theorem threeDoorScales_le_half {ρ : ℝ} (hρ : ρ ≤ 1 / 2) :
    ∀ a, threeDoorScales ρ a ≤ 1 / 2 := by
  intro a
  fin_cases a
  · norm_num [threeDoorScales]
  · norm_num [threeDoorScales]
  · exact hρ

/-- The paper's displayed three-door vector is the vector of genuine
deficiencies, not an assumed proxy for those deficiencies. -/
theorem threeDoor_deficiency_profile (w : Fin 3 → ℝ) (hw : IsDist w)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2) (a : Fin 3) :
    finiteDeficiency (threeDoorRootExperiment w (threeDoorScales ρ))
      (threeDoorRootTest (threeDoorScales ρ) a) =
    threeDoorProfile (1 / 2) (1 / 2) ρ (w 0) (w 1) (w 2) a := by
  rw [threeDoorRoot_deficiency w (threeDoorScales ρ) hw
    (threeDoorScales_nonneg hρ0) (threeDoorScales_le_half hρhalf)]
  fin_cases a <;> simp [threeDoorScales, threeDoorProfile]

/-- The exact one-sided tolerance between three-coordinate deficiency
profiles: the largest positive coordinate excess of the first over the second. -/
def threeDoorProfileGap (p q : Fin 3 → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => max (p a - q a) 0)

/-- The paper's first displayed directed gap: LEFT is within precisely
`ρ` of DARK in the native profile order. -/
theorem threeDoorProfileGap_left_dark {ρ : ℝ} (hρ : 0 ≤ ρ) :
    threeDoorProfileGap (threeDoorProfile (1 / 2) (1 / 2) ρ 1 0 0)
      (threeDoorProfile (1 / 2) (1 / 2) ρ 0 0 1) = ρ := by
  unfold threeDoorProfileGap
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    fin_cases a <;> simp [threeDoorProfile] <;> linarith
  · have h := Finset.le_sup'
      (fun a => max (threeDoorProfile (1 / 2) (1 / 2) ρ 1 0 0 a -
        threeDoorProfile (1 / 2) (1 / 2) ρ 0 0 1 a) 0)
      (Finset.mem_univ (2 : Fin 3))
    convert h using 1
    simp [threeDoorProfile, max_eq_left hρ]

/-- The reverse directed gap stays at one half, independently of the
nonnegative DARK strength. -/
theorem threeDoorProfileGap_dark_left {ρ : ℝ} (hρ : 0 ≤ ρ) :
    threeDoorProfileGap (threeDoorProfile (1 / 2) (1 / 2) ρ 0 0 1)
      (threeDoorProfile (1 / 2) (1 / 2) ρ 1 0 0) = 1 / 2 := by
  unfold threeDoorProfileGap
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    fin_cases a <;> simp [threeDoorProfile] <;> linarith
  · have h := Finset.le_sup'
      (fun a => max (threeDoorProfile (1 / 2) (1 / 2) ρ 0 0 1 a -
        threeDoorProfile (1 / 2) (1 / 2) ρ 1 0 0 a) 0)
      (Finset.mem_univ (0 : Fin 3))
    convert h using 1
    norm_num [threeDoorProfile]

end
end IdExp
