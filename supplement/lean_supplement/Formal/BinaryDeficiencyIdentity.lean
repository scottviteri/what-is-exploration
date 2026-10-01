import Formal.TwoWorldCoherence
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# The two-world binary deficiency identity

`TwoWorldCoherence.lean` proves the support-function half of the binary
randomization criterion, `binaryCallGap E F ≤ finiteDeficiency E F`.  This
module proves the reverse inequality and hence the exact identity

    finiteDeficiency E F = binaryCallGap E F

for valid two-world finite experiments `E` on `X` and `F` on `Y`.

The argument is the finite linear-programming duality step of the paper,
carried out with a geometric Hahn–Banach separation.

* **Separation.**  For `r` below the deficiency, the compact convex set of
  decoded two-row laws `{E ⬝ G}` is disjoint from the closed convex
  total-variation ball of unit-row-sum pairs around `F`.  A continuous
  linear functional, written through its coefficient vector `w : Bool → Y → ℝ`,
  strictly separates them.
* **Normalization.**  Evaluating the functional at the deterministic argmax
  decoder and at an extreme point of the ball, then centering and rescaling
  `w`, yields dual payoffs `0 ≤ w_b ≤ λ_b` with `λ_false + λ_true = 1` whose
  dual value exceeds `r`.
* **Call decomposition.**  The payoff `φ(z) = max_y ((1-z) w_false y + z w_true y)`
  is convex with chord slopes in `[-λ_false, λ_true]`.  On the finite grid of
  posterior scores of `E` and `F` it is an affine function plus a nonnegative
  combination of call payoffs `(z - s)_+` with total weight at most one, so
  the dual value is at most the optimized call gap.
-/

namespace IdExp

open Finset Set

set_option linter.unusedSectionVars false

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-! ### The convex score payoff and its slopes -/

section ScorePayoff

variable [Nonempty Y]

/-- The dual payoff as a function of the posterior score `z`: the best action
against a two-row experiment with score `z` and unit mass. -/
noncomputable def scorePayoff (w0 w1 : Y → ℝ) (z : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun y => (1 - z) * w0 y + z * w1 y)

theorem le_scorePayoff (w0 w1 : Y → ℝ) (z : ℝ) (y : Y) :
    (1 - z) * w0 y + z * w1 y ≤ scorePayoff w0 w1 z :=
  Finset.le_sup' (fun y => (1 - z) * w0 y + z * w1 y) (Finset.mem_univ y)

theorem exists_eq_scorePayoff (w0 w1 : Y → ℝ) (z : ℝ) :
    ∃ y, scorePayoff w0 w1 z = (1 - z) * w0 y + z * w1 y := by
  obtain ⟨y, -, hy⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun y => (1 - z) * w0 y + z * w1 y)
  exact ⟨y, hy⟩

/-- Chord slopes of the score payoff are at least `-l0`. -/
theorem scorePayoff_chord_lower (w0 w1 : Y → ℝ) (l0 : ℝ)
    (hw01 : ∀ y, w0 y ≤ l0) (hw10 : ∀ y, 0 ≤ w1 y) {t t' : ℝ} (htt : t ≤ t') :
    -l0 * (t' - t) ≤ scorePayoff w0 w1 t' - scorePayoff w0 w1 t := by
  obtain ⟨y0, hy0⟩ := exists_eq_scorePayoff w0 w1 t
  have h0 := le_scorePayoff w0 w1 t' y0
  have hs : 0 ≤ (w1 y0 - w0 y0 + l0) * (t' - t) :=
    mul_nonneg (by linarith [hw10 y0, hw01 y0]) (sub_nonneg.mpr htt)
  nlinarith [hs, h0, hy0]

/-- Chord slopes of the score payoff are at most `l1`. -/
theorem scorePayoff_chord_upper (w0 w1 : Y → ℝ) (l1 : ℝ)
    (hw00 : ∀ y, 0 ≤ w0 y) (hw11 : ∀ y, w1 y ≤ l1) {t t' : ℝ} (htt : t ≤ t') :
    scorePayoff w0 w1 t' - scorePayoff w0 w1 t ≤ l1 * (t' - t) := by
  obtain ⟨y1, hy1⟩ := exists_eq_scorePayoff w0 w1 t'
  have h1 := le_scorePayoff w0 w1 t y1
  have hs : 0 ≤ (l1 - (w1 y1 - w0 y1)) * (t' - t) :=
    mul_nonneg (by linarith [hw00 y1, hw11 y1]) (sub_nonneg.mpr htt)
  nlinarith [hs, h1, hy1]

/-- Three-point convexity of the score payoff, in multiplied-out form. -/
theorem scorePayoff_threeSlope (w0 w1 : Y → ℝ) {t t' t'' : ℝ}
    (h1 : t ≤ t') (h2 : t' ≤ t'') :
    (scorePayoff w0 w1 t' - scorePayoff w0 w1 t) * (t'' - t') ≤
      (scorePayoff w0 w1 t'' - scorePayoff w0 w1 t') * (t' - t) := by
  obtain ⟨y, hy⟩ := exists_eq_scorePayoff w0 w1 t'
  have ha := mul_le_mul_of_nonneg_right (le_scorePayoff w0 w1 t y) (sub_nonneg.mpr h2)
  have hb := mul_le_mul_of_nonneg_right (le_scorePayoff w0 w1 t'' y) (sub_nonneg.mpr h1)
  have e : ((1 - t') * w0 y + t' * w1 y) * (t'' - t) =
      ((1 - t) * w0 y + t * w1 y) * (t'' - t') +
        ((1 - t'') * w0 y + t'' * w1 y) * (t' - t) := by ring
  nlinarith [ha, hb, e, hy]

/-- Adjacent chord slopes of the score payoff are monotone. -/
theorem scorePayoff_slope_le (w0 w1 : Y → ℝ) {t t' t'' : ℝ}
    (h1 : t < t') (h2 : t' < t'') :
    (scorePayoff w0 w1 t' - scorePayoff w0 w1 t) / (t' - t) ≤
      (scorePayoff w0 w1 t'' - scorePayoff w0 w1 t') / (t'' - t') := by
  rw [div_le_div_iff₀ (sub_pos.mpr h1) (sub_pos.mpr h2)]
  exact scorePayoff_threeSlope w0 w1 h1.le h2.le

/-- Non-adjacent chord slopes of the score payoff are monotone. -/
theorem scorePayoff_slope_le' (w0 w1 : Y → ℝ) {t0 t' t t'' : ℝ}
    (h1 : t0 < t') (h2 : t' ≤ t) (h3 : t < t'') :
    (scorePayoff w0 w1 t' - scorePayoff w0 w1 t0) / (t' - t0) ≤
      (scorePayoff w0 w1 t'' - scorePayoff w0 w1 t) / (t'' - t) := by
  rcases h2.lt_or_eq with h2 | h2
  · exact (scorePayoff_slope_le w0 w1 h1 h2).trans (scorePayoff_slope_le w0 w1 h2 h3)
  · subst h2
    exact scorePayoff_slope_le w0 w1 h1 h3

/-- **Call decomposition on a finite grid.**  On any finite set `S` of scores
the score payoff agrees with an affine function plus a nonnegative combination
of call payoffs `(s - s')₊` centred at points of `S`.  The affine slope is at
least `-l0`, and the slope beyond `S` (affine slope plus total call weight) is
bounded by every later chord slope. -/
theorem scorePayoff_grid (w0 w1 : Y → ℝ) (l0 : ℝ)
    (hw01 : ∀ y, w0 y ≤ l0) (hw10 : ∀ y, 0 ≤ w1 y)
    (S : Finset ℝ) :
    ∃ (a b : ℝ) (c : ℝ → ℝ), (∀ s, 0 ≤ c s) ∧ (∀ s, s ∉ S → c s = 0) ∧
      (∀ s ∈ S, scorePayoff w0 w1 s = a + b * s + ∑ s' ∈ S, c s' * max (s - s') 0) ∧
      -l0 ≤ b ∧
      (∀ t t'', (∀ s ∈ S, s ≤ t) → t < t'' →
        b + ∑ s' ∈ S, c s' ≤
          (scorePayoff w0 w1 t'' - scorePayoff w0 w1 t) / (t'' - t)) := by
  classical
  induction S using Finset.induction_on_max with
  | empty =>
    refine ⟨0, -l0, fun _ => 0, fun _ => le_rfl, fun _ _ => rfl,
      fun s hs => absurd hs (Finset.notMem_empty s), le_rfl, ?_⟩
    intro t t'' _ htt
    rw [Finset.sum_empty, add_zero, le_div_iff₀ (sub_pos.mpr htt)]
    exact scorePayoff_chord_lower w0 w1 l0 hw01 hw10 htt.le
  | insert t' S hS ih =>
    obtain ⟨a, b, c, hc0, hcS, hrep, hb, hinv⟩ := ih
    rcases S.eq_empty_or_nonempty with rfl | hne
    · refine ⟨scorePayoff w0 w1 t' + l0 * t', -l0, fun _ => 0, fun _ => le_rfl,
        fun _ _ => rfl, ?_, le_rfl, ?_⟩
      · intro s hs
        simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hs
        subst hs
        simp
      · intro t t'' _ htt
        simp only [Finset.sum_const_zero, add_zero]
        rw [le_div_iff₀ (sub_pos.mpr htt)]
        exact scorePayoff_chord_lower w0 w1 l0 hw01 hw10 htt.le
    · set t0 := S.max' hne with ht0
      have ht0S : t0 ∈ S := Finset.max'_mem S hne
      have hle : ∀ s ∈ S, s ≤ t0 := fun s hs => Finset.le_max' S s hs
      have ht0t' : t0 < t' := hS t0 ht0S
      have ht'S : t' ∉ S := fun h => lt_irrefl _ (hS t' h)
      have ht't0 : t' ≠ t0 := ne_of_gt ht0t'
      set σ := (scorePayoff w0 w1 t' - scorePayoff w0 w1 t0) / (t' - t0) with hσ
      set δ := σ - (b + ∑ s' ∈ S, c s') with hδ
      have hδ0 : 0 ≤ δ := by
        have := hinv t0 t' hle ht0t'
        rw [hδ]
        linarith
      refine ⟨a, b, fun s => c s + if s = t0 then δ else 0, ?_, ?_, ?_, hb, ?_⟩
      · intro s
        show 0 ≤ c s + if s = t0 then δ else 0
        split_ifs <;> linarith [hc0 s]
      · intro s hs
        rw [Finset.mem_insert, not_or] at hs
        have hst0 : s ≠ t0 := fun h => hs.2 (h ▸ ht0S)
        simp [hcS s hs.2, hst0]
      · have hsum : ∀ s,
            ∑ s' ∈ insert t' S, (c s' + if s' = t0 then δ else 0) * max (s - s') 0 =
              (∑ s' ∈ S, c s' * max (s - s') 0) + δ * max (s - t0) 0 +
                c t' * max (s - t') 0 := by
          intro s
          rw [Finset.sum_insert ht'S]
          simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
            Finset.sum_ite_eq', if_pos ht0S, if_neg ht't0]
          ring
        intro s hs
        rw [Finset.mem_insert] at hs
        rw [hsum]
        rcases hs with hs | hs
        · rw [hs]
          have hrep0 := hrep t0 ht0S
          have hB : ∑ s' ∈ S, c s' * max (t0 - s') 0 = ∑ s' ∈ S, c s' * (t0 - s') :=
            Finset.sum_congr rfl fun s' hs' => by
              rw [max_eq_left (sub_nonneg.mpr (hle s' hs'))]
          have hA : ∑ s' ∈ S, c s' * max (t' - s') 0 =
              ∑ s' ∈ S, c s' * (t0 - s') + (∑ s' ∈ S, c s') * (t' - t0) := by
            rw [Finset.sum_mul, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro s' hs'
            rw [max_eq_left (sub_nonneg.mpr (hS s' hs').le)]
            ring
          have hσmul : σ * (t' - t0) = scorePayoff w0 w1 t' - scorePayoff w0 w1 t0 := by
            rw [hσ]
            exact div_mul_cancel₀ _ (sub_ne_zero.mpr ht't0)
          rw [hB] at hrep0
          rw [hA, hcS t' ht'S, max_eq_left (sub_nonneg.mpr ht0t'.le), hδ]
          linear_combination hrep0 - hσmul
        · have h1 : max (s - t0) 0 = 0 := max_eq_right (sub_nonpos.mpr (hle s hs))
          have h2 : max (s - t') 0 = 0 := max_eq_right (sub_nonpos.mpr (hS s hs).le)
          rw [h1, h2, mul_zero, mul_zero, add_zero, add_zero]
          exact hrep s hs
      · intro t t'' ht htt
        have hsumc : ∑ s' ∈ insert t' S, (c s' + if s' = t0 then δ else 0) =
            ∑ s' ∈ S, c s' + δ := by
          rw [Finset.sum_insert ht'S, Finset.sum_add_distrib, Finset.sum_ite_eq',
            if_pos ht0S, hcS t' ht'S, if_neg ht't0]
          ring
        rw [hsumc]
        have hslope : b + (∑ s' ∈ S, c s' + δ) = σ := by
          rw [hδ]
          ring
        rw [hslope]
        exact scorePayoff_slope_le' w0 w1 ht0t' (ht t' (Finset.mem_insert_self t' S)) htt

end ScorePayoff

/-! ### Mass and posterior-score coordinates of a two-world experiment -/

/-- Total mass of a signal under the two rows. -/
noncomputable def binaryMass (E : FiniteExperiment Bool X) (x : X) : ℝ :=
  E false x + E true x

/-- Posterior score of a signal: the true-row share of its mass (zero for a
zero-mass signal). -/
noncomputable def binaryScore (E : FiniteExperiment Bool X) (x : X) : ℝ :=
  E true x / binaryMass E x

theorem binaryMass_nonneg (E : FiniteExperiment Bool X) (hE : IsFiniteExperiment E) (x : X) :
    0 ≤ binaryMass E x :=
  add_nonneg ((hE false).1 x) ((hE true).1 x)

theorem binaryMass_mul_binaryScore (E : FiniteExperiment Bool X)
    (hE : IsFiniteExperiment E) (x : X) :
    binaryMass E x * binaryScore E x = E true x := by
  unfold binaryScore
  by_cases h : binaryMass E x = 0
  · rw [h, zero_mul]
    have h0 := (hE false).1 x
    have h1 := (hE true).1 x
    unfold binaryMass at h
    linarith
  · exact mul_div_cancel₀ _ h

theorem binaryScore_mem_Icc (E : FiniteExperiment Bool X)
    (hE : IsFiniteExperiment E) (x : X) :
    0 ≤ binaryScore E x ∧ binaryScore E x ≤ 1 := by
  unfold binaryScore
  rcases (binaryMass_nonneg E hE x).lt_or_eq with h | h
  · refine ⟨div_nonneg ((hE true).1 x) h.le, (div_le_one h).mpr ?_⟩
    unfold binaryMass
    linarith [(hE false).1 x]
  · rw [← h, div_zero]
    exact ⟨le_rfl, zero_le_one⟩

theorem sum_binaryMass (E : FiniteExperiment Bool X) (hE : IsFiniteExperiment E) :
    ∑ x, binaryMass E x = 2 := by
  unfold binaryMass
  rw [Finset.sum_add_distrib, (hE false).2, (hE true).2]
  norm_num

theorem sum_binaryMass_mul_binaryScore (E : FiniteExperiment Bool X)
    (hE : IsFiniteExperiment E) :
    ∑ x, binaryMass E x * binaryScore E x = 1 := by
  simp_rw [binaryMass_mul_binaryScore E hE]
  exact (hE true).2

/-- The call payoff in mass–score coordinates is the binary call function. -/
theorem sum_binaryMass_mul_max_eq_binaryCall (E : FiniteExperiment Bool X)
    (hE : IsFiniteExperiment E) (k : ℝ) :
    ∑ x, binaryMass E x * max (binaryScore E x - k) 0 = binaryCall E k := by
  unfold binaryCall
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_max_of_nonneg _ _ (binaryMass_nonneg E hE x), mul_zero, mul_sub,
    binaryMass_mul_binaryScore E hE]
  congr 1
  unfold binaryMass
  ring

/-- A two-row linear payoff in mass–score coordinates. -/
theorem binaryMass_mul_affine (E : FiniteExperiment Bool X)
    (hE : IsFiniteExperiment E) (x : X) (u0 u1 : ℝ) :
    binaryMass E x * ((1 - binaryScore E x) * u0 + binaryScore E x * u1) =
      E false x * u0 + E true x * u1 := by
  have h := binaryMass_mul_binaryScore E hE x
  have hm : binaryMass E x = E false x + E true x := rfl
  calc binaryMass E x * ((1 - binaryScore E x) * u0 + binaryScore E x * u1)
      = (binaryMass E x - binaryMass E x * binaryScore E x) * u0 +
          (binaryMass E x * binaryScore E x) * u1 := by ring
    _ = E false x * u0 + E true x * u1 := by rw [h, hm]; ring

/-- Summing a grid representation against mass–score coordinates. -/
theorem sum_binaryMass_mul_gridRep {Z : Type*} [Fintype Z]
    (H : FiniteExperiment Bool Z) (hH : IsFiniteExperiment H)
    (ψ : ℝ → ℝ) (a b : ℝ) (c : ℝ → ℝ) (S : Finset ℝ)
    (hrep : ∀ s ∈ S, ψ s = a + b * s + ∑ s' ∈ S, c s' * max (s - s') 0)
    (hmem : ∀ z, binaryScore H z ∈ S) :
    ∑ z, binaryMass H z * ψ (binaryScore H z) =
      2 * a + b + ∑ s ∈ S, c s * binaryCall H s := by
  have hpt : ∀ z, binaryMass H z * ψ (binaryScore H z) =
      binaryMass H z * a + (binaryMass H z * binaryScore H z) * b +
        ∑ s ∈ S, c s * (binaryMass H z * max (binaryScore H z - s) 0) := by
    intro z
    rw [hrep _ (hmem z), mul_add, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro s _
      ring
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    sum_binaryMass H hH, sum_binaryMass_mul_binaryScore H hH, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_binaryMass_mul_max_eq_binaryCall H hH]
  ring

/-! ### The dual value is at most the call gap -/

/-- **Call decomposition bound.**  A normalized two-row dual payoff
`0 ≤ w_b ≤ λ_b`, `λ_false + λ_true = 1`, evaluated at `F` and against the
best deterministic decoder for `E`, is at most the optimized call gap. -/
theorem dualValue_sub_le_binaryCallGap
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (w0 w1 : Y → ℝ) (l0 l1 : ℝ) (hl : l0 + l1 = 1)
    (hw00 : ∀ y, 0 ≤ w0 y) (hw01 : ∀ y, w0 y ≤ l0)
    (hw10 : ∀ y, 0 ≤ w1 y) (hw11 : ∀ y, w1 y ≤ l1)
    (d : X → Y)
    (hd : ∀ x y, E false x * w0 y + E true x * w1 y ≤
      E false x * w0 (d x) + E true x * w1 (d x)) :
    (∑ y, (F false y * w0 y + F true y * w1 y)) -
        ∑ x, (E false x * w0 (d x) + E true x * w1 (d x)) ≤
      binaryCallGap E F := by
  classical
  have : Nonempty Y := nonempty_of_isFiniteExperiment F hF
  have hFpt : ∀ y, F false y * w0 y + F true y * w1 y ≤
      binaryMass F y * scorePayoff w0 w1 (binaryScore F y) := by
    intro y
    rw [← binaryMass_mul_affine F hF y]
    exact mul_le_mul_of_nonneg_left (le_scorePayoff w0 w1 _ y) (binaryMass_nonneg F hF y)
  have hEpt : ∀ x, binaryMass E x * scorePayoff w0 w1 (binaryScore E x) ≤
      E false x * w0 (d x) + E true x * w1 (d x) := by
    intro x
    obtain ⟨y, hy⟩ := exists_eq_scorePayoff w0 w1 (binaryScore E x)
    rw [hy, binaryMass_mul_affine E hE x]
    exact hd x y
  let S : Finset ℝ :=
    (Finset.univ.image (binaryScore E)) ∪ (Finset.univ.image (binaryScore F))
  obtain ⟨a, b, c, hc0, -, hrep, hb, hinv⟩ :=
    scorePayoff_grid w0 w1 l0 hw01 hw10 S
  have hSE : ∀ x, binaryScore E x ∈ S := fun x =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ x))
  have hSF : ∀ y, binaryScore F y ∈ S := fun y =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ y))
  have hS01 : ∀ s ∈ S, 0 ≤ s ∧ s ≤ 1 := by
    intro s hs
    rcases Finset.mem_union.mp hs with h | h
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp h
      exact binaryScore_mem_Icc E hE x
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp h
      exact binaryScore_mem_Icc F hF y
  have hsumF := sum_binaryMass_mul_gridRep F hF (scorePayoff w0 w1) a b c S hrep hSF
  have hsumE := sum_binaryMass_mul_gridRep E hE (scorePayoff w0 w1) a b c S hrep hSE
  -- total call weight is at most one
  have hcsum : ∑ s ∈ S, c s ≤ 1 := by
    have h1 := hinv 1 2 (fun s hs => (hS01 s hs).2) one_lt_two
    have h2 := scorePayoff_chord_upper w0 w1 l1 hw00 hw11 (show (1 : ℝ) ≤ 2 by norm_num)
    rw [le_div_iff₀ (by norm_num)] at h1
    linarith
  have hgap : ∀ s ∈ S, binaryCall F s - binaryCall E s ≤ binaryCallGap E F := by
    intro s hs
    exact le_csSup (binaryCallGapValues_bddAbove E F hE hF) ⟨s, hS01 s hs, rfl⟩
  have hgap0 := binaryCallGap_nonneg E F hE hF
  calc (∑ y, (F false y * w0 y + F true y * w1 y)) -
        ∑ x, (E false x * w0 (d x) + E true x * w1 (d x))
      ≤ (∑ y, binaryMass F y * scorePayoff w0 w1 (binaryScore F y)) -
          ∑ x, binaryMass E x * scorePayoff w0 w1 (binaryScore E x) :=
        sub_le_sub (Finset.sum_le_sum fun y _ => hFpt y) (Finset.sum_le_sum fun x _ => hEpt x)
    _ = ∑ s ∈ S, c s * (binaryCall F s - binaryCall E s) := by
        rw [hsumF, hsumE]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        ring
    _ ≤ ∑ s ∈ S, c s * binaryCallGap E F :=
        Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hgap s hs) (hc0 s)
    _ = (∑ s ∈ S, c s) * binaryCallGap E F := by rw [Finset.sum_mul]
    _ ≤ 1 * binaryCallGap E F := mul_le_mul_of_nonneg_right hcsum hgap0
    _ = binaryCallGap E F := one_mul _

/-! ### Separation of the decoded laws from the total-variation ball -/

open Classical in
/-- Coordinate vectors of the two-row law space. -/
noncomputable def coordVec (b : Bool) (y : Y) : Bool → Y → ℝ :=
  fun b' y' => if b' = b then (if y' = y then 1 else 0) else 0

theorem eq_sum_coordVec (Q : Bool → Y → ℝ) :
    Q = ∑ b, ∑ y, Q b y • coordVec b y := by
  classical
  funext b' y'
  simp [Finset.sum_apply, coordVec]

/-- Every continuous linear functional on two-row laws is a coefficient sum. -/
theorem clm_apply_eq_sum (f : (Bool → Y → ℝ) →L[ℝ] ℝ) (Q : Bool → Y → ℝ) :
    f Q = ∑ y, (Q false y * f (coordVec false y) + Q true y * f (coordVec true y)) := by
  conv_lhs => rw [eq_sum_coordVec Q]
  simp only [map_sum, map_add, map_smul, smul_eq_mul, Fintype.sum_bool]
  rw [Finset.sum_add_distrib]
  ring

/-- Unit-row-sum two-row vectors within total variation `r` of `F` in each
row.  Nonnegativity is deliberately not imposed: the set must be convex and
closed, and its extreme directions are what the separation argument uses. -/
def tvBall (F : FiniteExperiment Bool Y) (r : ℝ) : Set (Bool → Y → ℝ) :=
  {Q | ∀ b, (∑ y, Q b y = 1) ∧ (1 / 2 : ℝ) * ∑ y, |Q b y - F b y| ≤ r}

theorem isClosed_tvBall (F : FiniteExperiment Bool Y) (r : ℝ) :
    IsClosed (tvBall F r) := by
  have h : tvBall F r = ⋂ b, ({Q : Bool → Y → ℝ | ∑ y, Q b y = 1} ∩
      {Q | (1 / 2 : ℝ) * ∑ y, |Q b y - F b y| ≤ r}) := by
    ext Q
    simp [tvBall]
  rw [h]
  exact isClosed_iInter fun b => IsClosed.inter
    (isClosed_eq (by fun_prop) continuous_const)
    (isClosed_le (by fun_prop) continuous_const)

theorem convex_tvBall (F : FiniteExperiment Bool Y) (r : ℝ) :
    Convex ℝ (tvBall F r) := by
  intro Q hQ Q' hQ' a b ha hb hab bb
  obtain ⟨hQ1, hQ2⟩ := hQ bb
  obtain ⟨hQ'1, hQ'2⟩ := hQ' bb
  constructor
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hQ1, hQ'1]
    linarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc (1 / 2 : ℝ) * ∑ y, |a * Q bb y + b * Q' bb y - F bb y|
        ≤ (1 / 2 : ℝ) * ∑ y, (a * |Q bb y - F bb y| + b * |Q' bb y - F bb y|) := by
          gcongr with y
          calc |a * Q bb y + b * Q' bb y - F bb y|
              = |a * (Q bb y - F bb y) + b * (Q' bb y - F bb y)| := by
                congr 1
                linear_combination (F bb y) * hab
            _ ≤ |a * (Q bb y - F bb y)| + |b * (Q' bb y - F bb y)| := abs_add_le _ _
            _ = a * |Q bb y - F bb y| + b * |Q' bb y - F bb y| := by
                rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ = a * ((1 / 2 : ℝ) * ∑ y, |Q bb y - F bb y|) +
            b * ((1 / 2 : ℝ) * ∑ y, |Q' bb y - F bb y|) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          ring
      _ ≤ a * r + b * r :=
          add_le_add (mul_le_mul_of_nonneg_left hQ2 ha) (mul_le_mul_of_nonneg_left hQ'2 hb)
      _ = r := by rw [← add_mul, hab, one_mul]

/-- Below the deficiency, no decoded law lies in the total-variation ball. -/
theorem disjoint_decodedLaws_tvBall
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (r : ℝ) (hr : r < finiteDeficiency E F) :
    Disjoint (finiteMatrixCapabilityMenu (D := Y) E) (tvBall F r) := by
  rw [Set.disjoint_left]
  rintro Q ⟨G, hG, rfl⟩ hQ
  have hle : finiteDeficiency E F ≤ r :=
    finiteDeficiency_le_of_decoder E F G hG r fun b => (hQ b).2
  exact absurd hr (not_lt.mpr hle)

/-- **Separation.**  Below the deficiency there is a two-row payoff `w`
strictly separating every decoded law from every point of the
total-variation ball. -/
theorem exists_separating_payoff
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (r : ℝ) (hr : r < finiteDeficiency E F) :
    ∃ (w : Bool → Y → ℝ) (u v : ℝ),
      (∀ G ∈ stochasticRules X Y,
        ∑ y, (finiteDecisionLaw E G false y * w false y +
          finiteDecisionLaw E G true y * w true y) < u) ∧
      u < v ∧
      (∀ Q ∈ tvBall F r, v < ∑ y, (Q false y * w false y + Q true y * w true y)) := by
  obtain ⟨f, u, v, hD, huv, hB⟩ := geometric_hahn_banach_compact_closed
    (convex_finiteMatrixCapabilityMenu (D := Y) E)
    (isCompact_finiteMatrixCapabilityMenu (D := Y) E) (convex_tvBall F r)
    (isClosed_tvBall F r) (disjoint_decodedLaws_tvBall E F r hr)
  refine ⟨fun b y => f (coordVec b y), u, v, ?_, huv, ?_⟩
  · intro G hG
    have h := hD _ ⟨G, hG, rfl⟩
    rwa [clm_apply_eq_sum] at h
  · intro Q hQ
    have h := hB Q hQ
    rwa [clm_apply_eq_sum] at h

/-! ### The reverse inequality -/

/-- **Dual witness.**  Every nonnegative `r` below the deficiency is also
below the optimized call gap. -/
theorem lt_binaryCallGap_of_lt_finiteDeficiency
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r < finiteDeficiency E F) :
    r < binaryCallGap E F := by
  classical
  have : Nonempty Y := nonempty_of_isFiniteExperiment F hF
  obtain ⟨w, u, v, hD, huv, hB⟩ := exists_separating_payoff E F r hr
  -- the deterministic argmax decoder
  have hdex : ∀ x, ∃ y, ∀ y', E false x * w false y' + E true x * w true y' ≤
      E false x * w false y + E true x * w true y := by
    intro x
    obtain ⟨y, -, hy⟩ := Finset.exists_max_image Finset.univ
      (fun y => E false x * w false y + E true x * w true y) Finset.univ_nonempty
    exact ⟨y, fun y' => hy y' (Finset.mem_univ y')⟩
  choose d hd using hdex
  obtain ⟨G, hGdef⟩ : ∃ G : X → Y → ℝ, ∀ x y, G x y = if y = d x then 1 else 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hG : G ∈ stochasticRules X Y := by
    intro x _
    constructor
    · intro y
      rw [hGdef]
      split_ifs <;> norm_num
    · simp [hGdef]
  have hGval : ∀ b, ∑ y, finiteDecisionLaw E G b y * w b y = ∑ x, E b x * w b (d x) := by
    intro b
    unfold finiteDecisionLaw
    rw [← sum_mul_decoderPullback]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    simp [hGdef, ite_mul]
  obtain ⟨LE, hLE⟩ : ∃ LE : ℝ, LE = ∑ x, (E false x * w false (d x) + E true x * w true (d x)) :=
    ⟨_, rfl⟩
  have hDval : LE < u := by
    have h := hD G hG
    rw [Finset.sum_add_distrib, hGval false, hGval true] at h
    rw [hLE, Finset.sum_add_distrib]
    exact h
  -- extreme points of the total-variation ball
  have hmaxex : ∀ b, ∃ y, ∀ y', w b y' ≤ w b y := fun b => by
    obtain ⟨y, -, hy⟩ := Finset.exists_max_image Finset.univ (w b) Finset.univ_nonempty
    exact ⟨y, fun y' => hy y' (Finset.mem_univ y')⟩
  have hminex : ∀ b, ∃ y, ∀ y', w b y ≤ w b y' := fun b => by
    obtain ⟨y, -, hy⟩ := Finset.exists_min_image Finset.univ (w b) Finset.univ_nonempty
    exact ⟨y, fun y' => hy y' (Finset.mem_univ y')⟩
  choose ymax hymax using hmaxex
  choose ymin hymin using hminex
  obtain ⟨Mn, hMn⟩ : ∃ Mn : Bool → ℝ, ∀ b, Mn b = w b (ymin b) := ⟨_, fun _ => rfl⟩
  obtain ⟨Mx, hMx⟩ : ∃ Mx : Bool → ℝ, ∀ b, Mx b = w b (ymax b) := ⟨_, fun _ => rfl⟩
  have hlo : ∀ b y, Mn b ≤ w b y := fun b y => by rw [hMn]; exact hymin b y
  have hhi : ∀ b y, w b y ≤ Mx b := fun b y => by rw [hMx]; exact hymax b y
  have hMnMx : ∀ b, Mn b ≤ Mx b := fun b => (hlo b (ymax b)).trans (hhi b (ymax b))
  obtain ⟨Q, hQdef⟩ : ∃ Q : Bool → Y → ℝ, ∀ b y,
      Q b y = F b y + (if y = ymin b then r else 0) - (if y = ymax b then r else 0) :=
    ⟨_, fun _ _ => rfl⟩
  have hQ : Q ∈ tvBall F r := by
    intro b
    constructor
    · simp only [hQdef]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), (hF b).2]
      ring
    · have hpt : ∀ y, |Q b y - F b y| ≤
          (if y = ymin b then r else 0) + (if y = ymax b then r else 0) := by
        intro y
        have h1 : Q b y - F b y =
            (if y = ymin b then r else 0) - (if y = ymax b then r else 0) := by
          rw [hQdef]
          ring
        have h2 : |(if y = ymin b then r else 0)| = (if y = ymin b then r else 0) :=
          abs_of_nonneg (by split_ifs <;> linarith)
        have h3 : |(if y = ymax b then r else 0)| = (if y = ymax b then r else 0) :=
          abs_of_nonneg (by split_ifs <;> linarith)
        rw [h1]
        exact (abs_sub _ _).trans (by rw [h2, h3])
      calc (1 / 2 : ℝ) * ∑ y, |Q b y - F b y|
          ≤ (1 / 2 : ℝ) * ∑ y, ((if y = ymin b then r else 0) + (if y = ymax b then r else 0)) := by
            gcongr with y
            exact hpt y
        _ = r := by
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
              if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
            ring
  have hQval : ∀ b, ∑ y, Q b y * w b y = ∑ y, F b y * w b y + r * Mn b - r * Mx b := by
    intro b
    rw [hMn, hMx]
    simp only [hQdef, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul,
      zero_mul, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  obtain ⟨LF, hLF⟩ : ∃ LF : ℝ, LF = ∑ y, (F false y * w false y + F true y * w true y) :=
    ⟨_, rfl⟩
  have hBval : v < LF + (r * Mn false - r * Mx false) + (r * Mn true - r * Mx true) := by
    have h := hB Q hQ
    rw [Finset.sum_add_distrib, hQval false, hQval true] at h
    rw [hLF, Finset.sum_add_distrib]
    linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (Mx false - Mn false) + (Mx true - Mn true) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    rw [hR]
    linarith [hMnMx false, hMnMx true]
  have hmain : r * R < LF - LE := by
    rw [hR]
    nlinarith [hDval, huv, hBval]
  have hRpos : 0 < R := by
    rcases hR0.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : Mx false = Mn false := by
        rw [hR] at h
        linarith [hMnMx false, hMnMx true]
      have h1 : Mx true = Mn true := by
        rw [hR] at h
        linarith [hMnMx false, hMnMx true]
      have hconst : ∀ b y, w b y = Mn b := by
        intro b y
        have hl := hlo b y
        have hh := hhi b y
        cases b
        · linarith
        · linarith
      have hLF0 : LF = Mn false + Mn true := by
        rw [hLF]
        simp_rw [hconst]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, (hF false).2, (hF true).2]
        ring
      have hLE0 : LE = Mn false + Mn true := by
        rw [hLE]
        simp_rw [hconst]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, (hE false).2, (hE true).2]
        ring
      rw [← h, mul_zero, hLF0, hLE0] at hmain
      linarith
  have hRne : R ≠ 0 := hRpos.ne'
  -- centre and rescale the payoff
  obtain ⟨w', hw'⟩ : ∃ w' : Bool → Y → ℝ, ∀ b y, w' b y = (w b y - Mn b) / R :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : Bool → ℝ, ∀ b, l b = (Mx b - Mn b) / R := ⟨_, fun _ => rfl⟩
  have hw'0 : ∀ b y, 0 ≤ w' b y := fun b y => by
    rw [hw']
    exact div_nonneg (by linarith [hlo b y]) hR0
  have hw'1 : ∀ b y, w' b y ≤ l b := fun b y => by
    rw [hw', hl]
    exact div_le_div_of_nonneg_right (by linarith [hhi b y]) hR0
  have hlsum : l false + l true = 1 := by
    rw [hl, hl, ← add_div, ← hR, div_self hRne]
  have hd' : ∀ x y, E false x * w' false y + E true x * w' true y ≤
      E false x * w' false (d x) + E true x * w' true (d x) := by
    intro x y
    have key : ∀ y, E false x * w' false y + E true x * w' true y =
        (E false x * w false y + E true x * w true y -
          (E false x * Mn false + E true x * Mn true)) / R := by
      intro y
      rw [hw', hw', mul_div_assoc', mul_div_assoc', ← add_div]
      congr 1
      ring
    rw [key, key]
    exact div_le_div_of_nonneg_right (by linarith [hd x y]) hR0
  have hstep := dualValue_sub_le_binaryCallGap E F hE hF (w' false) (w' true) (l false) (l true)
    hlsum (hw'0 false) (hw'1 false) (hw'0 true) (hw'1 true) d hd'
  have hF' : ∑ y, (F false y * w' false y + F true y * w' true y) =
      (LF - (Mn false + Mn true)) / R := by
    have key : ∀ y, F false y * w' false y + F true y * w' true y =
        ((F false y * w false y + F true y * w true y) -
          (F false y * Mn false + F true y * Mn true)) / R := by
      intro y
      rw [hw', hw', mul_div_assoc', mul_div_assoc', ← add_div]
      congr 1
      ring
    simp_rw [key]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← hLF, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, (hF false).2, (hF true).2]
    ring
  have hE' : ∑ x, (E false x * w' false (d x) + E true x * w' true (d x)) =
      (LE - (Mn false + Mn true)) / R := by
    have key : ∀ x, E false x * w' false (d x) + E true x * w' true (d x) =
        ((E false x * w false (d x) + E true x * w true (d x)) -
          (E false x * Mn false + E true x * Mn true)) / R := by
      intro x
      rw [hw', hw', mul_div_assoc', mul_div_assoc', ← add_div]
      congr 1
      ring
    simp_rw [key]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← hLE, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, (hE false).2, (hE true).2]
    ring
  rw [hF', hE', ← sub_div] at hstep
  have hnum : LF - (Mn false + Mn true) - (LE - (Mn false + Mn true)) = LF - LE := by ring
  rw [hnum] at hstep
  exact ((lt_div_iff₀ hRpos).mpr hmain).trans_le hstep

/-- **Reverse inequality of the binary deficiency identity.**  Directed
deficiency between two-world finite experiments is at most the optimized
call gap. -/
theorem finiteDeficiency_le_binaryCallGap
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    finiteDeficiency E F ≤ binaryCallGap E F := by
  by_contra h
  rw [not_le] at h
  exact lt_irrefl _ (lt_binaryCallGap_of_lt_finiteDeficiency E F hE hF _
    (binaryCallGap_nonneg E F hE hF) h)

/-- **The two-world binary deficiency identity.**  For valid finite
experiments on two worlds, directed deficiency equals the optimized
posterior-score call gap. -/
theorem finiteDeficiency_eq_binaryCallGap
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    finiteDeficiency E F = binaryCallGap E F :=
  le_antisymm (finiteDeficiency_le_binaryCallGap E F hE hF)
    (binaryCallGap_le_finiteDeficiency E F hE hF)

end IdExp
