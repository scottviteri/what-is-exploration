import Formal.BlackwellConverse
import Formal.FiniteBayesBregman
import Mathlib.Analysis.Convex.Jensen

/-!
# Strict posterior-potential comparison without finite worlds

The signal alphabets are finite; the world type is arbitrary. A posterior
system records predictive masses and posterior densities relative to one
prior, with their pointwise likelihood factorization. The separate prior
instantiation discharges that factorization, including null signals, from
continuity and full support. This module proves the complete stochastic
rather than merely deterministic garbling comparison and its equality case.
-/

set_option maxHeartbeats 1000000

namespace IdExp

open Finset Set

variable {Θ X Y : Type*} [Fintype X] [Fintype Y]

/-- Finite predictive masses and posterior likelihood-ratio functions.
The world class is not assumed finite. -/
structure SignalPosteriorSystem (E : FiniteExperiment Θ X) where
  mass : X → ℝ
  mass_dist : IsDist mass
  density : X → Θ → ℝ
  factor : ∀ x θ, mass x * density x θ = E θ x

noncomputable def SignalPosteriorSystem.potential
    {E : FiniteExperiment Θ X} (P : SignalPosteriorSystem E)
    (Φ : (Θ → ℝ) → ℝ) : ℝ := ∑ x, P.mass x * Φ (P.density x)

variable {E : FiniteExperiment Θ X} {F : FiniteExperiment Θ Y}
  (P : SignalPosteriorSystem E) (Q : SignalPosteriorSystem F)
  (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
  (hGF : finiteDecisionLaw E G = F)
  (hmass : ∀ y, ∑ x, P.mass x * G x y = Q.mass y)

include hGF in
/-- The posterior after garbling is the barycenter of the original
posteriors on each positive-predictive-mass signal. -/
theorem signalPosterior_barycenter (y : Y) (hy : Q.mass y ≠ 0) :
    (∑ x, (P.mass x * G x y / Q.mass y) • P.density x) = Q.density y := by
  funext θ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hsum : ∑ x, P.mass x * G x y * P.density x θ = Q.mass y * Q.density y θ := by
    calc _ = ∑ x, E θ x * G x y := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← P.factor x θ]
          ring
      _ = F θ y := congrFun (congrFun hGF θ) y
      _ = _ := (Q.factor y θ).symm
  calc _ = (∑ x, P.mass x * G x y * P.density x θ) / Q.mass y := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = Q.density y θ := by rw [hsum]; field_simp

include hG hGF hmass in
/-- The local Jensen bound, including null signals. -/
theorem signalPosterior_jensen
    (Φ : (Θ → ℝ) → ℝ) (C : Set (Θ → ℝ)) (hΦ : ConvexOn ℝ C Φ)
    (hP : ∀ x, P.density x ∈ C) (y : Y) :
    Q.mass y * Φ (Q.density y) ≤ ∑ x, P.mass x * G x y * Φ (P.density x) := by
  by_cases hy : Q.mass y = 0
  · have hz : ∀ x, P.mass x * G x y = 0 := by
      intro x
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun z _ => mul_nonneg (P.mass_dist.1 z) ((hG z (mem_univ z)).1 y))).mp
        ((hmass y).trans hy) x (mem_univ x)
    simp [hy, hz]
  · have hypos : 0 < Q.mass y := lt_of_le_of_ne (Q.mass_dist.1 y) (Ne.symm hy)
    have hw : ∑ x, P.mass x * G x y / Q.mass y = 1 := by
      rw [← Finset.sum_div, hmass y, div_self hy]
    have hj := hΦ.map_sum_le (t := Finset.univ)
      (w := fun x => P.mass x * G x y / Q.mass y) (p := P.density)
      (fun x _ => div_nonneg
        (mul_nonneg (P.mass_dist.1 x) ((hG x (mem_univ x)).1 y)) hypos.le)
      hw (fun x _ => hP x)
    rw [signalPosterior_barycenter P Q G hGF y hy] at hj
    simp only [smul_eq_mul] at hj
    have heq : ∑ x, P.mass x * G x y / Q.mass y * Φ (P.density x) =
        (∑ x, P.mass x * G x y * Φ (P.density x)) / Q.mass y := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [heq] at hj
    nlinarith [(le_div_iff₀ hypos).mp hj]

include hG hGF hmass in
/-- Convex posterior potentials respect arbitrary stochastic garblings on
any world class, provided the posterior systems use compatible predictive masses. -/
theorem signalPosterior_potential_mono
    (Φ : (Θ → ℝ) → ℝ) (C : Set (Θ → ℝ)) (hΦ : ConvexOn ℝ C Φ)
    (hP : ∀ x, P.density x ∈ C) : Q.potential Φ ≤ P.potential Φ := by
  calc Q.potential Φ ≤ ∑ y, ∑ x, P.mass x * G x y * Φ (P.density x) :=
      Finset.sum_le_sum fun y _ => signalPosterior_jensen P Q G hG hGF hmass Φ C hΦ hP y
    _ = P.potential Φ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      calc _ = (P.mass x * Φ (P.density x)) * ∑ y, G x y := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y _
                ring
        _ = _ := by rw [(hG x (mem_univ x)).2, mul_one]

include hG hGF hmass in
/-- Equality in strict Jensen identifies every posterior with the posterior
of any garbled signal to which it contributes positive predictive mass. -/
theorem signalPosterior_eq_of_potential_eq
    (Φ : (Θ → ℝ) → ℝ) (C : Set (Θ → ℝ)) (hΦ : StrictConvexOn ℝ C Φ)
    (hP : ∀ x, P.density x ∈ C) (heq : Q.potential Φ = P.potential Φ)
    (x : X) (y : Y) (hxy : P.mass x * G x y ≠ 0) :
    P.density x = Q.density y := by
  have hterm := signalPosterior_jensen P Q G hG hGF hmass Φ C hΦ.convexOn hP
  have htotal : (∑ y, Q.mass y * Φ (Q.density y)) =
      ∑ y, ∑ x, P.mass x * G x y * Φ (P.density x) := by
    rw [Finset.sum_comm]
    have hsum : (∑ x, ∑ y, P.mass x * G x y * Φ (P.density x)) = P.potential Φ := by
      apply Finset.sum_congr rfl
      intro x _
      calc _ = (P.mass x * Φ (P.density x)) * ∑ y, G x y := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y _
                ring
        _ = _ := by rw [(hG x (mem_univ x)).2, mul_one]
    rw [hsum]
    exact heq
  have heqy : Q.mass y * Φ (Q.density y) =
      ∑ x, P.mass x * G x y * Φ (P.density x) :=
    (Finset.sum_eq_sum_iff_of_le (fun y _ => hterm y)).mp htotal y (mem_univ y)
  have hxypos : 0 < P.mass x * G x y :=
    lt_of_le_of_ne (mul_nonneg (P.mass_dist.1 x) ((hG x (mem_univ x)).1 y)) (Ne.symm hxy)
  have hle : P.mass x * G x y ≤ Q.mass y := by
    rw [← hmass y]
    exact Finset.single_le_sum (fun x _ => mul_nonneg (P.mass_dist.1 x)
      ((hG x (mem_univ x)).1 y)) (mem_univ x)
  have hypos : 0 < Q.mass y := hxypos.trans_le hle
  have hy : Q.mass y ≠ 0 := ne_of_gt hypos
  have hw : ∑ x, P.mass x * G x y / Q.mass y = 1 := by
    rw [← Finset.sum_div, hmass y, div_self hy]
  have hj := hΦ.map_sum_eq_iff' (t := Finset.univ)
    (w := fun x => P.mass x * G x y / Q.mass y) (p := P.density)
    (fun x _ => div_nonneg
      (mul_nonneg (P.mass_dist.1 x) ((hG x (mem_univ x)).1 y)) hypos.le)
    hw (fun x _ => hP x)
  rw [signalPosterior_barycenter P Q G hGF y hy] at hj
  apply hj.mp ?_ x (mem_univ x) (div_ne_zero hxy hy)
  simp only [smul_eq_mul]
  calc Φ (Q.density y) = (∑ x, P.mass x * G x y * Φ (P.density x)) / Q.mass y := by
          rw [← heqy]; field_simp
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- The Bayes reverse channel, with a genuine probability row also at
null target signals. -/
noncomputable def signalPosteriorReverse [Nonempty X] : Y → X → ℝ := fun y x =>
  if Q.mass y = 0 then uniformPrior X x else P.mass x * G x y / Q.mass y

include hG hmass in
theorem signalPosteriorReverse_stochastic [Nonempty X] :
    signalPosteriorReverse P Q G ∈ stochasticRules Y X := by
  classical
  intro y _
  by_cases hy : Q.mass y = 0
  · rw [show signalPosteriorReverse P Q G y = uniformPrior X from by
          funext x; simp [signalPosteriorReverse, hy]]
    exact isDist_uniformPrior
  · constructor
    · intro x
      simp only [signalPosteriorReverse, if_neg hy]
      exact div_nonneg (mul_nonneg (P.mass_dist.1 x) ((hG x (mem_univ x)).1 y))
        (Q.mass_dist.1 y)
    · simp only [signalPosteriorReverse, if_neg hy]
      rw [← Finset.sum_div, hmass y, div_self hy]

include hG hGF hmass in
/-- Equal strictly convex posterior value gives a single reverse simulator
valid in every world. No finite-world assumption or full-revelation target. -/
theorem signalPosterior_reverse_of_potential_eq [Nonempty X]
    (Φ : (Θ → ℝ) → ℝ) (C : Set (Θ → ℝ)) (hΦ : StrictConvexOn ℝ C Φ)
    (hP : ∀ x, P.density x ∈ C) (heq : Q.potential Φ = P.potential Φ) :
    finiteDecisionLaw F (signalPosteriorReverse P Q G) = E := by
  funext θ x
  have ht (y : Y) : F θ y * signalPosteriorReverse P Q G y x = E θ x * G x y := by
    by_cases hy : Q.mass y = 0
    · have hF0 : F θ y = 0 := by rw [← Q.factor y θ, hy, zero_mul]
      have hz : P.mass x * G x y = 0 := by
        have ha : ∑ z, P.mass z * G z y = 0 := (hmass y).trans hy
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => mul_nonneg
          (P.mass_dist.1 z) ((hG z (mem_univ z)).1 y))).mp ha x (mem_univ x)
      rw [hF0, zero_mul, ← P.factor x θ]
      calc 0 = (P.mass x * G x y) * P.density x θ := by rw [hz, zero_mul]
        _ = _ := by ring
    · rw [signalPosteriorReverse, if_neg hy, ← Q.factor y θ, ← P.factor x θ]
      by_cases hxy : P.mass x * G x y = 0
      · rw [hxy, zero_div, mul_zero]
        calc 0 = (P.mass x * G x y) * P.density x θ := by rw [hxy, zero_mul]
          _ = _ := by ring
      · have hp := congrFun
          (signalPosterior_eq_of_potential_eq P Q G hG hGF hmass Φ C hΦ hP heq x y hxy) θ
        rw [hp]
        field_simp
  unfold finiteDecisionLaw
  simp_rw [ht]
  rw [← Finset.mul_sum, (hG x (mem_univ x)).2, mul_one]

include hG hGF hmass in
/-- Strict Blackwell domination implies strict posterior-potential loss. -/
theorem signalPosterior_potential_lt_of_no_reverse [Nonempty X]
    (Φ : (Θ → ℝ) → ℝ) (C : Set (Θ → ℝ)) (hΦ : StrictConvexOn ℝ C Φ)
    (hP : ∀ x, P.density x ∈ C)
    (hnot : ¬ ∃ R ∈ stochasticRules Y X, finiteDecisionLaw F R = E) :
    Q.potential Φ < P.potential Φ := by
  apply lt_of_le_of_ne (signalPosterior_potential_mono P Q G hG hGF hmass Φ C hΦ.convexOn hP)
  intro heq
  exact hnot ⟨signalPosteriorReverse P Q G,
    signalPosteriorReverse_stochastic P Q G hG hmass,
    signalPosterior_reverse_of_potential_eq P Q G hG hGF hmass Φ C hΦ hP heq⟩

end IdExp
